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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(lean_object* v_e_248_){
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
LEAN_EXPORT void l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_248_ = stack[0].m_obj;
lean_object* v_res_267_;
v_res_267_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_248_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg___boxed(lean_object* v_e_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_268_);
return v_res_270_;
}
}
lean_object* l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(lean_object* v_00_u03b1_271_, lean_object* v_e_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v_e_272_);
return v___x_274_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_272_ = stack[1].m_obj;
lean_object* v_res_275_;
v_res_275_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0(lean_box(0), v_e_272_);
stack->m_obj
 = v_res_275_;
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
lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1(lean_object* v___x_291_, uint8_t v___x_292_, lean_object* v_env_293_, lean_object* v_opts_294_, lean_object* v___x_295_, lean_object* v_scriptName_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___closed__0));
v___x_300_ = lean_string_append(v___x_291_, v___x_299_);
lean_inc_n(v_scriptName_296_, 2);
v___x_301_ = l_Lean_Name_toString(v_scriptName_296_, v___x_292_);
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
lean_dec_ref(v___x_301_);
lean_inc_ref(v_env_293_);
v___x_303_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_293_, v_opts_294_, v___x_295_, v_scriptName_296_);
v___x_304_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_303_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_304_, 1);
v___x_306_ = 1;
v___x_307_ = l_Lean_Options_empty;
v___x_308_ = lean_box(0);
v___x_309_ = lean_box(0);
v___x_310_ = l_Lean_findDocString_x3f(v_env_293_, v_scriptName_296_, v___x_306_, v___x_307_, v___x_308_, v___x_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_302_);
lean_ctor_set(v___x_312_, 1, v_a_305_);
lean_ctor_set(v___x_312_, 2, v_a_311_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___y_297_);
return v___x_313_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_a_305_);
lean_dec_ref(v___x_302_);
v_a_314_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_310_, 1);
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
lean_dec_ref(v___x_302_);
lean_dec(v_scriptName_296_);
lean_dec_ref(v_env_293_);
v_a_321_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_304_, 1);
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
LEAN_EXPORT void l_Lake_LakefileConfig_loadFromEnv___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_291_ = stack[0].m_obj;
uint8_t v___x_292_ = stack[1].m_num;
lean_object* v_env_293_ = stack[2].m_obj;
lean_object* v_opts_294_ = stack[3].m_obj;
lean_object* v___x_295_ = stack[4].m_obj;
lean_object* v_scriptName_296_ = stack[5].m_obj;
lean_object* v___y_297_ = stack[6].m_obj;
lean_object* v_res_328_;
v_res_328_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_291_, v___x_292_, v_env_293_, v_opts_294_, v___x_295_, v_scriptName_296_, v___y_297_);
stack->m_obj
 = v_res_328_;
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed(lean_object* v___x_329_, lean_object* v___x_330_, lean_object* v_env_331_, lean_object* v_opts_332_, lean_object* v___x_333_, lean_object* v_scriptName_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v___x_49126__boxed_337_; lean_object* v_res_338_; 
v___x_49126__boxed_337_ = lean_unbox(v___x_330_);
v_res_338_ = l_Lake_LakefileConfig_loadFromEnv___lam__1(v___x_329_, v___x_49126__boxed_337_, v_env_331_, v_opts_332_, v___x_333_, v_scriptName_334_, v___y_335_);
lean_dec_ref(v_opts_332_);
return v_res_338_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(lean_object* v_env_341_, lean_object* v_opts_342_, lean_object* v___x_343_, size_t v_sz_344_, size_t v_i_345_, lean_object* v_bs_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_a_350_; lean_object* v_a_351_; uint8_t v___x_353_; 
v___x_353_ = lean_usize_dec_lt(v_i_345_, v_sz_344_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec(v___x_343_);
lean_dec_ref(v_env_341_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_bs_346_);
lean_ctor_set(v___x_354_, 1, v___y_347_);
return v___x_354_;
}
else
{
lean_object* v___x_355_; lean_object* v_v_356_; lean_object* v___x_357_; 
v___x_355_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_356_ = lean_array_uget_borrowed(v_bs_346_, v_i_345_);
lean_inc(v_v_356_);
lean_inc_ref(v_env_341_);
v___x_357_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_341_, v_opts_342_, v___x_355_, v_v_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v_bs_346_);
lean_dec(v___x_343_);
lean_dec_ref(v_env_341_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_357_, 1);
v___x_359_ = 3;
v___x_360_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_360_, 0, v_a_358_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*1, v___x_359_);
v___x_361_ = lean_array_get_size(v___y_347_);
v___x_362_ = lean_array_push(v___y_347_, v___x_360_);
v_a_350_ = v___x_361_;
v_a_351_ = v___x_362_;
goto v___jp_349_;
}
else
{
lean_object* v_a_363_; lean_object* v_pkg_364_; lean_object* v_fn_365_; uint8_t v___x_366_; 
v_a_363_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_357_, 1);
v_pkg_364_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_pkg_364_);
v_fn_365_ = lean_ctor_get(v_a_363_, 1);
lean_inc_ref(v_fn_365_);
lean_dec(v_a_363_);
v___x_366_ = lean_name_eq(v_pkg_364_, v___x_343_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec_ref(v_fn_365_);
lean_dec_ref(v_bs_346_);
lean_dec_ref(v_env_341_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__0));
v___x_368_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_364_, v___x_353_);
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
lean_dec_ref(v___x_368_);
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___closed__1));
v___x_371_ = lean_string_append(v___x_369_, v___x_370_);
v___x_372_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_343_, v___x_353_);
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
lean_dec_ref(v___x_372_);
v___x_374_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_375_ = lean_string_append(v___x_373_, v___x_374_);
v___x_376_ = 3;
v___x_377_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v___x_376_);
v___x_378_ = lean_array_get_size(v___y_347_);
v___x_379_ = lean_array_push(v___y_347_, v___x_377_);
v_a_350_ = v___x_378_;
v_a_351_ = v___x_379_;
goto v___jp_349_;
}
else
{
lean_object* v___x_380_; lean_object* v_bs_x27_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
lean_dec(v_pkg_364_);
v___x_380_ = lean_unsigned_to_nat(0u);
v_bs_x27_381_ = lean_array_uset(v_bs_346_, v_i_345_, v___x_380_);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_345_, v___x_382_);
v___x_384_ = lean_array_uset(v_bs_x27_381_, v_i_345_, v_fn_365_);
v_i_345_ = v___x_383_;
v_bs_346_ = v___x_384_;
goto _start;
}
}
}
v___jp_349_:
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_352_, 0, v_a_350_);
lean_ctor_set(v___x_352_, 1, v_a_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_341_ = stack[0].m_obj;
lean_object* v_opts_342_ = stack[1].m_obj;
lean_object* v___x_343_ = stack[2].m_obj;
size_t v_sz_344_ = stack[3].m_num;
size_t v_i_345_ = stack[4].m_num;
lean_object* v_bs_346_ = stack[5].m_obj;
lean_object* v___y_347_ = stack[6].m_obj;
lean_object* v_res_386_;
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_341_, v_opts_342_, v___x_343_, v_sz_344_, v_i_345_, v_bs_346_, v___y_347_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9___boxed(lean_object* v_env_387_, lean_object* v_opts_388_, lean_object* v___x_389_, lean_object* v_sz_390_, lean_object* v_i_391_, lean_object* v_bs_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
size_t v_sz_boxed_395_; size_t v_i_boxed_396_; lean_object* v_res_397_; 
v_sz_boxed_395_ = lean_unbox_usize(v_sz_390_);
lean_dec(v_sz_390_);
v_i_boxed_396_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_387_, v_opts_388_, v___x_389_, v_sz_boxed_395_, v_i_boxed_396_, v_bs_392_, v___y_393_);
lean_dec_ref(v_opts_388_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(lean_object* v_t_398_, lean_object* v_k_399_){
_start:
{
if (lean_obj_tag(v_t_398_) == 0)
{
lean_object* v_k_400_; lean_object* v_v_401_; lean_object* v_l_402_; lean_object* v_r_403_; uint8_t v___x_404_; 
v_k_400_ = lean_ctor_get(v_t_398_, 1);
v_v_401_ = lean_ctor_get(v_t_398_, 2);
v_l_402_ = lean_ctor_get(v_t_398_, 3);
v_r_403_ = lean_ctor_get(v_t_398_, 4);
v___x_404_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_399_, v_k_400_);
switch(v___x_404_)
{
case 0:
{
v_t_398_ = v_l_402_;
goto _start;
}
case 1:
{
lean_object* v___x_406_; 
lean_inc(v_v_401_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_v_401_);
return v___x_406_;
}
default: 
{
v_t_398_ = v_r_403_;
goto _start;
}
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_409_, lean_object* v_k_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_409_, v_k_410_);
lean_dec(v_k_410_);
lean_dec(v_t_409_);
return v_res_411_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(lean_object* v_a_414_, lean_object* v___x_415_, size_t v_sz_416_, size_t v_i_417_, lean_object* v_bs_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_417_, v_sz_416_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec_ref(v___x_415_);
lean_dec_ref(v_a_414_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_bs_418_);
lean_ctor_set(v___x_422_, 1, v___y_419_);
return v___x_422_;
}
else
{
lean_object* v_toTreeMap_423_; lean_object* v_v_424_; lean_object* v___x_425_; 
v_toTreeMap_423_ = lean_ctor_get(v_a_414_, 0);
v_v_424_ = lean_array_uget_borrowed(v_bs_418_, v_i_417_);
v___x_425_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_423_, v_v_424_);
if (lean_obj_tag(v___x_425_) == 1)
{
lean_object* v_val_426_; lean_object* v_name_427_; lean_object* v___x_428_; lean_object* v_bs_x27_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v_val_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v___x_425_, 1);
v_name_427_ = lean_ctor_get(v_val_426_, 1);
lean_inc(v_name_427_);
lean_dec(v_val_426_);
v___x_428_ = lean_unsigned_to_nat(0u);
v_bs_x27_429_ = lean_array_uset(v_bs_418_, v_i_417_, v___x_428_);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_417_, v___x_430_);
v___x_432_ = lean_array_uset(v_bs_x27_429_, v_i_417_, v_name_427_);
v_i_417_ = v___x_431_;
v_bs_418_ = v___x_432_;
goto _start;
}
else
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_450_; 
lean_inc(v_v_424_);
lean_dec(v___x_425_);
lean_dec_ref(v_bs_418_);
v_isSharedCheck_450_ = !lean_is_exclusive(v_a_414_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_451_ = lean_ctor_get(v_a_414_, 1);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_a_414_, 0);
lean_dec(v_unused_452_);
v___x_435_ = v_a_414_;
v_isShared_436_ = v_isSharedCheck_450_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_a_414_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_450_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_437_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__0));
v___x_438_ = lean_string_append(v___x_415_, v___x_437_);
v___x_439_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_424_, v___x_421_);
v___x_440_ = lean_string_append(v___x_438_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_442_ = lean_string_append(v___x_440_, v___x_441_);
v___x_443_ = 3;
v___x_444_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set_uint8(v___x_444_, sizeof(void*)*1, v___x_443_);
v___x_445_ = lean_array_get_size(v___y_419_);
v___x_446_ = lean_array_push(v___y_419_, v___x_444_);
if (v_isShared_436_ == 0)
{
lean_ctor_set_tag(v___x_435_, 1);
lean_ctor_set(v___x_435_, 1, v___x_446_);
lean_ctor_set(v___x_435_, 0, v___x_445_);
v___x_448_ = v___x_435_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_414_ = stack[0].m_obj;
lean_object* v___x_415_ = stack[1].m_obj;
size_t v_sz_416_ = stack[2].m_num;
size_t v_i_417_ = stack[3].m_num;
lean_object* v_bs_418_ = stack[4].m_obj;
lean_object* v___y_419_ = stack[5].m_obj;
lean_object* v_res_453_;
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_414_, v___x_415_, v_sz_416_, v_i_417_, v_bs_418_, v___y_419_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___boxed(lean_object* v_a_454_, lean_object* v___x_455_, lean_object* v_sz_456_, lean_object* v_i_457_, lean_object* v_bs_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
size_t v_sz_boxed_461_; size_t v_i_boxed_462_; lean_object* v_res_463_; 
v_sz_boxed_461_ = lean_unbox_usize(v_sz_456_);
lean_dec(v_sz_456_);
v_i_boxed_462_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_454_, v___x_455_, v_sz_boxed_461_, v_i_boxed_462_, v_bs_458_, v___y_459_);
return v_res_463_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(lean_object* v_f_464_, lean_object* v_as_465_, size_t v_i_466_, size_t v_stop_467_, lean_object* v_b_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_eq(v_i_466_, v_stop_467_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_array_uget_borrowed(v_as_465_, v_i_466_);
lean_inc_ref(v_f_464_);
lean_inc(v___x_470_);
v___x_471_ = lean_apply_1(v_f_464_, v___x_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_b_468_);
lean_dec_ref(v_f_464_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; 
v_a_480_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_471_, 1);
v___x_481_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_470_);
v___x_482_ = l_Lake_RBArray_insert___redArg(v___x_481_, v_b_468_, v___x_470_, v_a_480_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_i_466_, v___x_483_);
v_i_466_ = v___x_484_;
v_b_468_ = v___x_482_;
goto _start;
}
}
else
{
lean_object* v___x_486_; 
lean_dec_ref(v_f_464_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_468_);
return v___x_486_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_464_ = stack[0].m_obj;
lean_object* v_as_465_ = stack[1].m_obj;
size_t v_i_466_ = stack[2].m_num;
size_t v_stop_467_ = stack[3].m_num;
lean_object* v_b_468_ = stack[4].m_obj;
lean_object* v_res_487_;
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_464_, v_as_465_, v_i_466_, v_stop_467_, v_b_468_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg___boxed(lean_object* v_f_488_, lean_object* v_as_489_, lean_object* v_i_490_, lean_object* v_stop_491_, lean_object* v_b_492_){
_start:
{
size_t v_i_boxed_493_; size_t v_stop_boxed_494_; lean_object* v_res_495_; 
v_i_boxed_493_ = lean_unbox_usize(v_i_490_);
lean_dec(v_i_490_);
v_stop_boxed_494_ = lean_unbox_usize(v_stop_491_);
lean_dec(v_stop_491_);
v_res_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_488_, v_as_489_, v_i_boxed_493_, v_stop_boxed_494_, v_b_492_);
lean_dec_ref(v_as_489_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(lean_object* v_env_496_, lean_object* v_attr_497_, lean_object* v_f_498_){
_start:
{
lean_object* v_entries_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_entries_499_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_497_, v_env_496_);
v___x_500_ = lean_array_get_size(v_entries_499_);
v___x_501_ = l_Lake_RBArray_mkEmpty___redArg(v___x_500_);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_nat_dec_lt(v___x_502_, v___x_500_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec_ref(v_entries_499_);
lean_dec_ref(v_f_498_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_501_);
return v___x_504_;
}
else
{
size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((size_t)0ULL);
v___x_506_ = lean_usize_of_nat(v___x_500_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_498_, v_entries_499_, v___x_505_, v___x_506_, v___x_501_);
lean_dec_ref(v_entries_499_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg___boxed(lean_object* v_env_508_, lean_object* v_attr_509_, lean_object* v_f_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_508_, v_attr_509_, v_f_510_);
lean_dec_ref(v_attr_509_);
return v_res_511_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_512_, lean_object* v_as_513_, size_t v_i_514_, size_t v_stop_515_, lean_object* v_b_516_, lean_object* v___y_517_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_eq(v_i_514_, v_stop_515_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_array_uget_borrowed(v_as_513_, v_i_514_);
lean_inc_ref(v_f_512_);
lean_inc(v___x_520_);
v___x_521_ = lean_apply_3(v_f_512_, v___x_520_, v___y_517_, lean_box(0));
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v_a_523_; lean_object* v___x_524_; size_t v___x_525_; size_t v___x_526_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
v_a_523_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_521_, 2);
lean_inc(v___x_520_);
v___x_524_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_520_, v_a_522_, v_b_516_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_514_, v___x_525_);
v_i_514_ = v___x_526_;
v_b_516_ = v___x_524_;
v___y_517_ = v_a_523_;
goto _start;
}
else
{
lean_object* v_a_528_; lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_b_516_);
lean_dec_ref(v_f_512_);
v_a_528_ = lean_ctor_get(v___x_521_, 0);
v_a_529_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_521_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_inc(v_a_528_);
lean_dec(v___x_521_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_528_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_537_; 
lean_dec_ref(v_f_512_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_b_516_);
lean_ctor_set(v___x_537_, 1, v___y_517_);
return v___x_537_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_512_ = stack[0].m_obj;
lean_object* v_as_513_ = stack[1].m_obj;
size_t v_i_514_ = stack[2].m_num;
size_t v_stop_515_ = stack[3].m_num;
lean_object* v_b_516_ = stack[4].m_obj;
lean_object* v___y_517_ = stack[5].m_obj;
lean_object* v_res_538_;
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_512_, v_as_513_, v_i_514_, v_stop_515_, v_b_516_, v___y_517_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_539_, lean_object* v_as_540_, lean_object* v_i_541_, lean_object* v_stop_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
size_t v_i_boxed_546_; size_t v_stop_boxed_547_; lean_object* v_res_548_; 
v_i_boxed_546_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_stop_boxed_547_ = lean_unbox_usize(v_stop_542_);
lean_dec(v_stop_542_);
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_539_, v_as_540_, v_i_boxed_546_, v_stop_boxed_547_, v_b_543_, v___y_544_);
lean_dec_ref(v_as_540_);
return v_res_548_;
}
}
lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(lean_object* v_env_549_, lean_object* v_attr_550_, lean_object* v_f_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_entries_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_entries_554_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_550_, v_env_549_);
v___x_555_ = lean_box(1);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_array_get_size(v_entries_554_);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec_ref(v_entries_554_);
lean_dec_ref(v_f_551_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_555_);
lean_ctor_set(v___x_559_, 1, v___y_552_);
return v___x_559_;
}
else
{
size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; 
v___x_560_ = ((size_t)0ULL);
v___x_561_ = lean_usize_of_nat(v___x_557_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_551_, v_entries_554_, v___x_560_, v___x_561_, v___x_555_, v___y_552_);
lean_dec_ref(v_entries_554_);
return v___x_562_;
}
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_549_ = stack[0].m_obj;
lean_object* v_attr_550_ = stack[1].m_obj;
lean_object* v_f_551_ = stack[2].m_obj;
lean_object* v___y_552_ = stack[3].m_obj;
lean_object* v_res_563_;
v_res_563_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_549_, v_attr_550_, v_f_551_, v___y_552_);
stack->m_obj
 = v_res_563_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_564_, lean_object* v_attr_565_, lean_object* v_f_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_564_, v_attr_565_, v_f_566_, v___y_567_);
lean_dec_ref(v_attr_565_);
return v_res_569_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(lean_object* v___x_573_, size_t v_sz_574_, size_t v_i_575_, lean_object* v_bs_576_, lean_object* v___y_577_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
lean_dec(v___x_573_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_bs_576_);
lean_ctor_set(v___x_580_, 1, v___y_577_);
return v___x_580_;
}
else
{
lean_object* v_v_581_; lean_object* v_pkg_582_; lean_object* v_name_583_; uint8_t v___x_584_; 
v_v_581_ = lean_array_uget(v_bs_576_, v_i_575_);
v_pkg_582_ = lean_ctor_get(v_v_581_, 0);
v_name_583_ = lean_ctor_get(v_v_581_, 1);
v___x_584_ = lean_name_eq(v_pkg_582_, v___x_573_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_inc(v_name_583_);
lean_inc(v_pkg_582_);
lean_dec(v_v_581_);
lean_dec_ref(v_bs_576_);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__0));
v___x_586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_583_, v___x_579_);
v___x_587_ = lean_string_append(v___x_585_, v___x_586_);
lean_dec_ref(v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__1));
v___x_589_ = lean_string_append(v___x_587_, v___x_588_);
v___x_590_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_582_, v___x_579_);
v___x_591_ = lean_string_append(v___x_589_, v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___closed__2));
v___x_593_ = lean_string_append(v___x_591_, v___x_592_);
v___x_594_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_573_, v___x_579_);
v___x_595_ = lean_string_append(v___x_593_, v___x_594_);
lean_dec_ref(v___x_594_);
v___x_596_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
v___x_598_ = 3;
v___x_599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*1, v___x_598_);
v___x_600_ = lean_array_get_size(v___y_577_);
v___x_601_ = lean_array_push(v___y_577_, v___x_599_);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v_bs_x27_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v_bs_x27_604_ = lean_array_uset(v_bs_576_, v_i_575_, v___x_603_);
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_575_, v___x_605_);
v___x_607_ = lean_array_uset(v_bs_x27_604_, v_i_575_, v_v_581_);
v_i_575_ = v___x_606_;
v_bs_576_ = v___x_607_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_573_ = stack[0].m_obj;
size_t v_sz_574_ = stack[1].m_num;
size_t v_i_575_ = stack[2].m_num;
lean_object* v_bs_576_ = stack[3].m_obj;
lean_object* v___y_577_ = stack[4].m_obj;
lean_object* v_res_609_;
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(v___x_573_, v_sz_574_, v_i_575_, v_bs_576_, v___y_577_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4___boxed(lean_object* v___x_610_, lean_object* v_sz_611_, lean_object* v_i_612_, lean_object* v_bs_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
size_t v_sz_boxed_616_; size_t v_i_boxed_617_; lean_object* v_res_618_; 
v_sz_boxed_616_ = lean_unbox_usize(v_sz_611_);
lean_dec(v_sz_611_);
v_i_boxed_617_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(v___x_610_, v_sz_boxed_616_, v_i_boxed_617_, v_bs_613_, v___y_614_);
return v_res_618_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(lean_object* v_env_619_, lean_object* v_opts_620_, lean_object* v_as_621_, size_t v_sz_622_, size_t v_i_623_, lean_object* v_b_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_lt(v_i_623_, v_sz_622_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v_env_619_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_b_624_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v_a_628_; lean_object* v___x_629_; 
v___x_627_ = l_Lake_instTypeNameModuleFacetDecl;
v_a_628_ = lean_array_uget_borrowed(v_as_621_, v_i_623_);
lean_inc(v_a_628_);
lean_inc_ref(v_env_619_);
v___x_629_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_619_, v_opts_620_, v___x_627_, v_a_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_b_624_);
lean_dec_ref(v_env_619_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v_name_639_; lean_object* v_config_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_651_; 
v_a_638_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_629_, 1);
v_name_639_ = lean_ctor_get(v_a_638_, 0);
v_config_640_ = lean_ctor_get(v_a_638_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_638_);
if (v_isSharedCheck_651_ == 0)
{
v___x_642_ = v_a_638_;
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_config_640_);
lean_inc(v_name_639_);
lean_dec(v_a_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_651_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_name_639_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_config_640_);
v___x_645_ = v_reuseFailAlloc_650_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; size_t v___x_647_; size_t v___x_648_; 
v___x_646_ = lean_array_push(v_b_624_, v___x_645_);
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_623_, v___x_647_);
v_i_623_ = v___x_648_;
v_b_624_ = v___x_646_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_619_ = stack[0].m_obj;
lean_object* v_opts_620_ = stack[1].m_obj;
lean_object* v_as_621_ = stack[2].m_obj;
size_t v_sz_622_ = stack[3].m_num;
size_t v_i_623_ = stack[4].m_num;
lean_object* v_b_624_ = stack[5].m_obj;
lean_object* v_res_652_;
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_619_, v_opts_620_, v_as_621_, v_sz_622_, v_i_623_, v_b_624_);
stack->m_obj
 = v_res_652_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(lean_object* v___x_665_, lean_object* v_as_666_, size_t v_i_667_, size_t v_stop_668_, lean_object* v_b_669_, lean_object* v___y_670_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_665_ = stack[0].m_obj;
lean_object* v_as_666_ = stack[1].m_obj;
size_t v_i_667_ = stack[2].m_num;
size_t v_stop_668_ = stack[3].m_num;
lean_object* v_b_669_ = stack[4].m_obj;
lean_object* v___y_670_ = stack[5].m_obj;
lean_object* v_res_709_;
v_res_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_665_, v_as_666_, v_i_667_, v_stop_668_, v_b_669_, v___y_670_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16___boxed(lean_object* v___x_710_, lean_object* v_as_711_, lean_object* v_i_712_, lean_object* v_stop_713_, lean_object* v_b_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
size_t v_i_boxed_717_; size_t v_stop_boxed_718_; lean_object* v_res_719_; 
v_i_boxed_717_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_stop_boxed_718_ = lean_unbox_usize(v_stop_713_);
lean_dec(v_stop_713_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_710_, v_as_711_, v_i_boxed_717_, v_stop_boxed_718_, v_b_714_, v___y_715_);
lean_dec_ref(v_as_711_);
return v_res_719_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v___x_724_, size_t v_sz_725_, size_t v_i_726_, lean_object* v_bs_727_, lean_object* v___y_728_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_lt(v_i_726_, v_sz_725_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec_ref(v___x_724_);
lean_dec_ref(v_a_722_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_bs_727_);
lean_ctor_set(v___x_731_, 1, v___y_728_);
return v___x_731_;
}
else
{
lean_object* v_toTreeMap_732_; lean_object* v_v_733_; lean_object* v___x_734_; lean_object* v_bs_x27_735_; lean_object* v_a_737_; lean_object* v_a_738_; lean_object* v___x_743_; 
v_toTreeMap_732_ = lean_ctor_get(v_a_722_, 0);
v_v_733_ = lean_array_uget(v_bs_727_, v_i_726_);
v___x_734_ = lean_unsigned_to_nat(0u);
v_bs_x27_735_ = lean_array_uset(v_bs_727_, v_i_726_, v___x_734_);
v___x_743_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_toTreeMap_732_, v_v_733_);
if (lean_obj_tag(v___x_743_) == 1)
{
lean_object* v_val_744_; lean_object* v_name_745_; 
lean_dec(v_v_733_);
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_743_, 1);
v_name_745_ = lean_ctor_get(v_val_744_, 1);
lean_inc(v_name_745_);
lean_dec(v_val_744_);
v_a_737_ = v_name_745_;
v_a_738_ = v___y_728_;
goto v___jp_736_;
}
else
{
uint8_t v___x_746_; 
lean_dec(v___x_743_);
v___x_746_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_733_, v_a_723_);
if (v___x_746_ == 0)
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_bs_x27_735_);
v_isSharedCheck_763_ = !lean_is_exclusive(v_a_722_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; lean_object* v_unused_765_; 
v_unused_764_ = lean_ctor_get(v_a_722_, 1);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_a_722_, 0);
lean_dec(v_unused_765_);
v___x_748_ = v_a_722_;
v_isShared_749_ = v_isSharedCheck_763_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_a_722_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_763_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__0));
v___x_751_ = lean_string_append(v___x_724_, v___x_750_);
v___x_752_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_733_, v___x_730_);
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
lean_dec_ref(v___x_752_);
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11___closed__1));
v___x_755_ = lean_string_append(v___x_753_, v___x_754_);
v___x_756_ = 3;
v___x_757_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*1, v___x_756_);
v___x_758_ = lean_array_get_size(v___y_728_);
v___x_759_ = lean_array_push(v___y_728_, v___x_757_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 1);
lean_ctor_set(v___x_748_, 1, v___x_759_);
lean_ctor_set(v___x_748_, 0, v___x_758_);
v___x_761_ = v___x_748_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
v_a_737_ = v_v_733_;
v_a_738_ = v___y_728_;
goto v___jp_736_;
}
}
v___jp_736_:
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_726_, v___x_739_);
v___x_741_ = lean_array_uset(v_bs_x27_735_, v_i_726_, v_a_737_);
v_i_726_ = v___x_740_;
v_bs_727_ = v___x_741_;
v___y_728_ = v_a_738_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_722_ = stack[0].m_obj;
lean_object* v_a_723_ = stack[1].m_obj;
lean_object* v___x_724_ = stack[2].m_obj;
size_t v_sz_725_ = stack[3].m_num;
size_t v_i_726_ = stack[4].m_num;
lean_object* v_bs_727_ = stack[5].m_obj;
lean_object* v___y_728_ = stack[6].m_obj;
lean_object* v_res_766_;
v_res_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_722_, v_a_723_, v___x_724_, v_sz_725_, v_i_726_, v_bs_727_, v___y_728_);
stack->m_obj
 = v_res_766_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v___x_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_bs_784_, lean_object* v___y_785_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_779_ = stack[0].m_obj;
lean_object* v_a_780_ = stack[1].m_obj;
lean_object* v___x_781_ = stack[2].m_obj;
size_t v_sz_782_ = stack[3].m_num;
size_t v_i_783_ = stack[4].m_num;
lean_object* v_bs_784_ = stack[5].m_obj;
lean_object* v___y_785_ = stack[6].m_obj;
lean_object* v_res_823_;
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_779_, v_a_780_, v___x_781_, v_sz_782_, v_i_783_, v_bs_784_, v___y_785_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15___boxed(lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v___x_826_, lean_object* v_sz_827_, lean_object* v_i_828_, lean_object* v_bs_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
size_t v_sz_boxed_832_; size_t v_i_boxed_833_; lean_object* v_res_834_; 
v_sz_boxed_832_ = lean_unbox_usize(v_sz_827_);
lean_dec(v_sz_827_);
v_i_boxed_833_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_824_, v_a_825_, v___x_826_, v_sz_boxed_832_, v_i_boxed_833_, v_bs_829_, v___y_830_);
lean_dec(v_a_825_);
return v_res_834_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(lean_object* v_a_836_, lean_object* v___x_837_, size_t v_sz_838_, size_t v_i_839_, lean_object* v_bs_840_, lean_object* v___y_841_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_usize_dec_lt(v_i_839_, v_sz_838_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v___x_837_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_bs_840_);
lean_ctor_set(v___x_844_, 1, v___y_841_);
return v___x_844_;
}
else
{
lean_object* v_v_845_; lean_object* v___x_846_; 
v_v_845_ = lean_array_uget_borrowed(v_bs_840_, v_i_839_);
v___x_846_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_a_836_, v_v_845_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; lean_object* v_bs_x27_849_; size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
v_val_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_unsigned_to_nat(0u);
v_bs_x27_849_ = lean_array_uset(v_bs_840_, v_i_839_, v___x_848_);
v___x_850_ = ((size_t)1ULL);
v___x_851_ = lean_usize_add(v_i_839_, v___x_850_);
v___x_852_ = lean_array_uset(v_bs_x27_849_, v_i_839_, v_val_847_);
v_i_839_ = v___x_851_;
v_bs_840_ = v___x_852_;
goto _start;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_inc(v_v_845_);
lean_dec(v___x_846_);
lean_dec_ref(v_bs_840_);
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___closed__0));
v___x_855_ = lean_string_append(v___x_837_, v___x_854_);
v___x_856_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_845_, v___x_843_);
v___x_857_ = lean_string_append(v___x_855_, v___x_856_);
lean_dec_ref(v___x_856_);
v___x_858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6___closed__1));
v___x_859_ = lean_string_append(v___x_857_, v___x_858_);
v___x_860_ = 3;
v___x_861_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*1, v___x_860_);
v___x_862_ = lean_array_get_size(v___y_841_);
v___x_863_ = lean_array_push(v___y_841_, v___x_861_);
v___x_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
return v___x_864_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_836_ = stack[0].m_obj;
lean_object* v___x_837_ = stack[1].m_obj;
size_t v_sz_838_ = stack[2].m_num;
size_t v_i_839_ = stack[3].m_num;
lean_object* v_bs_840_ = stack[4].m_obj;
lean_object* v___y_841_ = stack[5].m_obj;
lean_object* v_res_865_;
v_res_865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_836_, v___x_837_, v_sz_838_, v_i_839_, v_bs_840_, v___y_841_);
stack->m_obj
 = v_res_865_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8___boxed(lean_object* v_a_866_, lean_object* v___x_867_, lean_object* v_sz_868_, lean_object* v_i_869_, lean_object* v_bs_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
size_t v_sz_boxed_873_; size_t v_i_boxed_874_; lean_object* v_res_875_; 
v_sz_boxed_873_ = lean_unbox_usize(v_sz_868_);
lean_dec(v_sz_868_);
v_i_boxed_874_ = lean_unbox_usize(v_i_869_);
lean_dec(v_i_869_);
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_866_, v___x_867_, v_sz_boxed_873_, v_i_boxed_874_, v_bs_870_, v___y_871_);
lean_dec(v_a_866_);
return v_res_875_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(lean_object* v_env_876_, lean_object* v_opts_877_, size_t v_sz_878_, size_t v_i_879_, lean_object* v_bs_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
lean_dec_ref(v_env_876_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_bs_880_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; lean_object* v_v_884_; lean_object* v___x_885_; 
v___x_883_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_;
v_v_884_ = lean_array_uget_borrowed(v_bs_880_, v_i_879_);
lean_inc(v_v_884_);
lean_inc_ref(v_env_876_);
v___x_885_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_876_, v_opts_877_, v___x_883_, v_v_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_bs_880_);
lean_dec_ref(v_env_876_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v_bs_x27_896_; size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; 
v_a_894_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_885_, 1);
v___x_895_ = lean_unsigned_to_nat(0u);
v_bs_x27_896_ = lean_array_uset(v_bs_880_, v_i_879_, v___x_895_);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_add(v_i_879_, v___x_897_);
v___x_899_ = lean_array_uset(v_bs_x27_896_, v_i_879_, v_a_894_);
v_i_879_ = v___x_898_;
v_bs_880_ = v___x_899_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_876_ = stack[0].m_obj;
lean_object* v_opts_877_ = stack[1].m_obj;
size_t v_sz_878_ = stack[2].m_num;
size_t v_i_879_ = stack[3].m_num;
lean_object* v_bs_880_ = stack[4].m_obj;
lean_object* v_res_901_;
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_876_, v_opts_877_, v_sz_878_, v_i_879_, v_bs_880_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10___boxed(lean_object* v_env_902_, lean_object* v_opts_903_, lean_object* v_sz_904_, lean_object* v_i_905_, lean_object* v_bs_906_){
_start:
{
size_t v_sz_boxed_907_; size_t v_i_boxed_908_; lean_object* v_res_909_; 
v_sz_boxed_907_ = lean_unbox_usize(v_sz_904_);
lean_dec(v_sz_904_);
v_i_boxed_908_ = lean_unbox_usize(v_i_905_);
lean_dec(v_i_905_);
v_res_909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_902_, v_opts_903_, v_sz_boxed_907_, v_i_boxed_908_, v_bs_906_);
lean_dec_ref(v_opts_903_);
return v_res_909_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(lean_object* v_env_910_, lean_object* v_opts_911_, lean_object* v_as_912_, size_t v_sz_913_, size_t v_i_914_, lean_object* v_b_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = lean_usize_dec_lt(v_i_914_, v_sz_913_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec_ref(v_env_910_);
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v_b_915_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; lean_object* v_a_919_; lean_object* v___x_920_; 
v___x_918_ = l_Lake_instTypeNamePackageFacetDecl;
v_a_919_ = lean_array_uget_borrowed(v_as_912_, v_i_914_);
lean_inc(v_a_919_);
lean_inc_ref(v_env_910_);
v___x_920_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_910_, v_opts_911_, v___x_918_, v_a_919_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_b_915_);
lean_dec_ref(v_env_910_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
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
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v_name_930_; lean_object* v_config_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_942_; 
v_a_929_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_920_, 1);
v_name_930_ = lean_ctor_get(v_a_929_, 0);
v_config_931_ = lean_ctor_get(v_a_929_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_942_ == 0)
{
v___x_933_ = v_a_929_;
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_config_931_);
lean_inc(v_name_930_);
lean_dec(v_a_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_name_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_config_931_);
v___x_936_ = v_reuseFailAlloc_941_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; size_t v___x_938_; size_t v___x_939_; 
v___x_937_ = lean_array_push(v_b_915_, v___x_936_);
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_add(v_i_914_, v___x_938_);
v_i_914_ = v___x_939_;
v_b_915_ = v___x_937_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_910_ = stack[0].m_obj;
lean_object* v_opts_911_ = stack[1].m_obj;
lean_object* v_as_912_ = stack[2].m_obj;
size_t v_sz_913_ = stack[3].m_num;
size_t v_i_914_ = stack[4].m_num;
lean_object* v_b_915_ = stack[5].m_obj;
lean_object* v_res_943_;
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_910_, v_opts_911_, v_as_912_, v_sz_913_, v_i_914_, v_b_915_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13___boxed(lean_object* v_env_944_, lean_object* v_opts_945_, lean_object* v_as_946_, lean_object* v_sz_947_, lean_object* v_i_948_, lean_object* v_b_949_){
_start:
{
size_t v_sz_boxed_950_; size_t v_i_boxed_951_; lean_object* v_res_952_; 
v_sz_boxed_950_ = lean_unbox_usize(v_sz_947_);
lean_dec(v_sz_947_);
v_i_boxed_951_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_944_, v_opts_945_, v_as_946_, v_sz_boxed_950_, v_i_boxed_951_, v_b_949_);
lean_dec_ref(v_as_946_);
lean_dec_ref(v_opts_945_);
return v_res_952_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(lean_object* v_env_953_, lean_object* v_opts_954_, lean_object* v_as_955_, size_t v_sz_956_, size_t v_i_957_, lean_object* v_b_958_){
_start:
{
uint8_t v___x_959_; 
v___x_959_ = lean_usize_dec_lt(v_i_957_, v_sz_956_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v_env_953_);
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v_b_958_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_963_; 
v___x_961_ = l_Lake_instTypeNameLibraryFacetDecl;
v_a_962_ = lean_array_uget_borrowed(v_as_955_, v_i_957_);
lean_inc(v_a_962_);
lean_inc_ref(v_env_953_);
v___x_963_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_953_, v_opts_954_, v___x_961_, v_a_962_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v_b_958_);
lean_dec_ref(v_env_953_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_972_; lean_object* v_name_973_; lean_object* v_config_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_985_; 
v_a_972_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_963_, 1);
v_name_973_ = lean_ctor_get(v_a_972_, 0);
v_config_974_ = lean_ctor_get(v_a_972_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_985_ == 0)
{
v___x_976_ = v_a_972_;
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_config_974_);
lean_inc(v_name_973_);
lean_dec(v_a_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_name_973_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_config_974_);
v___x_979_ = v_reuseFailAlloc_984_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; size_t v___x_981_; size_t v___x_982_; 
v___x_980_ = lean_array_push(v_b_958_, v___x_979_);
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_957_, v___x_981_);
v_i_957_ = v___x_982_;
v_b_958_ = v___x_980_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_953_ = stack[0].m_obj;
lean_object* v_opts_954_ = stack[1].m_obj;
lean_object* v_as_955_ = stack[2].m_obj;
size_t v_sz_956_ = stack[3].m_num;
size_t v_i_957_ = stack[4].m_num;
lean_object* v_b_958_ = stack[5].m_obj;
lean_object* v_res_986_;
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_953_, v_opts_954_, v_as_955_, v_sz_956_, v_i_957_, v_b_958_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14___boxed(lean_object* v_env_987_, lean_object* v_opts_988_, lean_object* v_as_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_b_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_994_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_987_, v_opts_988_, v_as_989_, v_sz_boxed_993_, v_i_boxed_994_, v_b_992_);
lean_dec_ref(v_as_989_);
lean_dec_ref(v_opts_988_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(lean_object* v_t_996_, lean_object* v_k_997_){
_start:
{
if (lean_obj_tag(v_t_996_) == 0)
{
lean_object* v_k_998_; lean_object* v_v_999_; lean_object* v_l_1000_; lean_object* v_r_1001_; uint8_t v___x_1002_; 
v_k_998_ = lean_ctor_get(v_t_996_, 1);
v_v_999_ = lean_ctor_get(v_t_996_, 2);
v_l_1000_ = lean_ctor_get(v_t_996_, 3);
v_r_1001_ = lean_ctor_get(v_t_996_, 4);
v___x_1002_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_997_, v_k_998_);
switch(v___x_1002_)
{
case 0:
{
v_t_996_ = v_l_1000_;
goto _start;
}
case 1:
{
lean_object* v___x_1004_; 
lean_inc(v_v_999_);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_v_999_);
return v___x_1004_;
}
default: 
{
v_t_996_ = v_r_1001_;
goto _start;
}
}
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_box(0);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg___boxed(lean_object* v_t_1007_, lean_object* v_k_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_t_1007_, v_k_1008_);
lean_dec(v_k_1008_);
lean_dec(v_t_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(lean_object* v_k_1010_, lean_object* v_v_1011_, lean_object* v_t_1012_){
_start:
{
if (lean_obj_tag(v_t_1012_) == 0)
{
lean_object* v_size_1013_; lean_object* v_k_1014_; lean_object* v_v_1015_; lean_object* v_l_1016_; lean_object* v_r_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1297_; 
v_size_1013_ = lean_ctor_get(v_t_1012_, 0);
v_k_1014_ = lean_ctor_get(v_t_1012_, 1);
v_v_1015_ = lean_ctor_get(v_t_1012_, 2);
v_l_1016_ = lean_ctor_get(v_t_1012_, 3);
v_r_1017_ = lean_ctor_get(v_t_1012_, 4);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_t_1012_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1019_ = v_t_1012_;
v_isShared_1020_ = v_isSharedCheck_1297_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_r_1017_);
lean_inc(v_l_1016_);
lean_inc(v_v_1015_);
lean_inc(v_k_1014_);
lean_inc(v_size_1013_);
lean_dec(v_t_1012_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1297_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
uint8_t v___x_1021_; 
v___x_1021_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1010_, v_k_1014_);
switch(v___x_1021_)
{
case 0:
{
lean_object* v_impl_1022_; lean_object* v___x_1023_; 
lean_dec(v_size_1013_);
v_impl_1022_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_1010_, v_v_1011_, v_l_1016_);
v___x_1023_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1017_) == 0)
{
lean_object* v_size_1024_; lean_object* v_size_1025_; lean_object* v_k_1026_; lean_object* v_v_1027_; lean_object* v_l_1028_; lean_object* v_r_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_size_1024_ = lean_ctor_get(v_r_1017_, 0);
v_size_1025_ = lean_ctor_get(v_impl_1022_, 0);
v_k_1026_ = lean_ctor_get(v_impl_1022_, 1);
v_v_1027_ = lean_ctor_get(v_impl_1022_, 2);
v_l_1028_ = lean_ctor_get(v_impl_1022_, 3);
v_r_1029_ = lean_ctor_get(v_impl_1022_, 4);
lean_inc(v_r_1029_);
v___x_1030_ = lean_unsigned_to_nat(3u);
v___x_1031_ = lean_nat_mul(v___x_1030_, v_size_1024_);
v___x_1032_ = lean_nat_dec_lt(v___x_1031_, v_size_1025_);
lean_dec(v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_dec(v_r_1029_);
v___x_1033_ = lean_nat_add(v___x_1023_, v_size_1025_);
v___x_1034_ = lean_nat_add(v___x_1033_, v_size_1024_);
lean_dec(v___x_1033_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 3, v_impl_1022_);
lean_ctor_set(v___x_1019_, 0, v___x_1034_);
v___x_1036_ = v___x_1019_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_impl_1022_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_r_1017_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1103_; 
lean_inc(v_l_1028_);
lean_inc(v_v_1027_);
lean_inc(v_k_1026_);
lean_inc(v_size_1025_);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_impl_1022_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; lean_object* v_unused_1105_; lean_object* v_unused_1106_; lean_object* v_unused_1107_; lean_object* v_unused_1108_; 
v_unused_1104_ = lean_ctor_get(v_impl_1022_, 4);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_impl_1022_, 3);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v_impl_1022_, 2);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_impl_1022_, 1);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_impl_1022_, 0);
lean_dec(v_unused_1108_);
v___x_1039_ = v_impl_1022_;
v_isShared_1040_ = v_isSharedCheck_1103_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v_impl_1022_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1103_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_size_1041_; lean_object* v_size_1042_; lean_object* v_k_1043_; lean_object* v_v_1044_; lean_object* v_l_1045_; lean_object* v_r_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_size_1041_ = lean_ctor_get(v_l_1028_, 0);
v_size_1042_ = lean_ctor_get(v_r_1029_, 0);
v_k_1043_ = lean_ctor_get(v_r_1029_, 1);
v_v_1044_ = lean_ctor_get(v_r_1029_, 2);
v_l_1045_ = lean_ctor_get(v_r_1029_, 3);
v_r_1046_ = lean_ctor_get(v_r_1029_, 4);
v___x_1047_ = lean_unsigned_to_nat(2u);
v___x_1048_ = lean_nat_mul(v___x_1047_, v_size_1041_);
v___x_1049_ = lean_nat_dec_lt(v_size_1042_, v___x_1048_);
lean_dec(v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1078_; 
lean_inc(v_r_1046_);
lean_inc(v_l_1045_);
lean_inc(v_v_1044_);
lean_inc(v_k_1043_);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_r_1029_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; lean_object* v_unused_1080_; lean_object* v_unused_1081_; lean_object* v_unused_1082_; lean_object* v_unused_1083_; 
v_unused_1079_ = lean_ctor_get(v_r_1029_, 4);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_r_1029_, 3);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_r_1029_, 2);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_r_1029_, 1);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_r_1029_, 0);
lean_dec(v_unused_1083_);
v___x_1051_ = v_r_1029_;
v_isShared_1052_ = v_isSharedCheck_1078_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v_r_1029_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1078_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___x_1066_; lean_object* v___y_1068_; 
v___x_1053_ = lean_nat_add(v___x_1023_, v_size_1025_);
lean_dec(v_size_1025_);
v___x_1054_ = lean_nat_add(v___x_1053_, v_size_1024_);
lean_dec(v___x_1053_);
v___x_1066_ = lean_nat_add(v___x_1023_, v_size_1041_);
if (lean_obj_tag(v_l_1045_) == 0)
{
lean_object* v_size_1076_; 
v_size_1076_ = lean_ctor_get(v_l_1045_, 0);
lean_inc(v_size_1076_);
v___y_1068_ = v_size_1076_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_unsigned_to_nat(0u);
v___y_1068_ = v___x_1077_;
goto v___jp_1067_;
}
v___jp_1055_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_nat_add(v___y_1056_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec(v___y_1056_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 4, v_r_1017_);
lean_ctor_set(v___x_1051_, 3, v_r_1046_);
lean_ctor_set(v___x_1051_, 2, v_v_1015_);
lean_ctor_set(v___x_1051_, 1, v_k_1014_);
lean_ctor_set(v___x_1051_, 0, v___x_1059_);
v___x_1061_ = v___x_1051_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_r_1046_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_r_1017_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___x_1061_);
lean_ctor_set(v___x_1039_, 3, v___y_1057_);
lean_ctor_set(v___x_1039_, 2, v_v_1044_);
lean_ctor_set(v___x_1039_, 1, v_k_1043_);
lean_ctor_set(v___x_1039_, 0, v___x_1054_);
v___x_1063_ = v___x_1039_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_k_1043_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_v_1044_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v___y_1057_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = lean_nat_add(v___x_1066_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec(v___x_1066_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_l_1045_);
lean_ctor_set(v___x_1019_, 3, v_l_1028_);
lean_ctor_set(v___x_1019_, 2, v_v_1027_);
lean_ctor_set(v___x_1019_, 1, v_k_1026_);
lean_ctor_set(v___x_1019_, 0, v___x_1069_);
v___x_1071_ = v___x_1019_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_k_1026_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_v_1027_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_l_1028_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_l_1045_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_nat_add(v___x_1023_, v_size_1024_);
if (lean_obj_tag(v_r_1046_) == 0)
{
lean_object* v_size_1073_; 
v_size_1073_ = lean_ctor_get(v_r_1046_, 0);
lean_inc(v_size_1073_);
v___y_1056_ = v___x_1072_;
v___y_1057_ = v___x_1071_;
v___y_1058_ = v_size_1073_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___y_1056_ = v___x_1072_;
v___y_1057_ = v___x_1071_;
v___y_1058_ = v___x_1074_;
goto v___jp_1055_;
}
}
}
}
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
lean_del_object(v___x_1019_);
v___x_1084_ = lean_nat_add(v___x_1023_, v_size_1025_);
lean_dec(v_size_1025_);
v___x_1085_ = lean_nat_add(v___x_1084_, v_size_1024_);
lean_dec(v___x_1084_);
v___x_1086_ = lean_nat_add(v___x_1023_, v_size_1024_);
v___x_1087_ = lean_nat_add(v___x_1086_, v_size_1042_);
lean_dec(v___x_1086_);
lean_inc_ref(v_r_1017_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_r_1017_);
lean_ctor_set(v___x_1039_, 3, v_r_1029_);
lean_ctor_set(v___x_1039_, 2, v_v_1015_);
lean_ctor_set(v___x_1039_, 1, v_k_1014_);
lean_ctor_set(v___x_1039_, 0, v___x_1087_);
v___x_1089_ = v___x_1039_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_r_1029_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_r_1017_);
v___x_1089_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v_r_1017_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; lean_object* v_unused_1098_; lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1097_ = lean_ctor_get(v_r_1017_, 4);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_r_1017_, 3);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_r_1017_, 2);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_r_1017_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_r_1017_, 0);
lean_dec(v_unused_1101_);
v___x_1091_ = v_r_1017_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v_r_1017_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 4, v___x_1089_);
lean_ctor_set(v___x_1091_, 3, v_l_1028_);
lean_ctor_set(v___x_1091_, 2, v_v_1027_);
lean_ctor_set(v___x_1091_, 1, v_k_1026_);
lean_ctor_set(v___x_1091_, 0, v___x_1085_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_k_1026_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_v_1027_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_l_1028_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v___x_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1109_; 
v_l_1109_ = lean_ctor_get(v_impl_1022_, 3);
if (lean_obj_tag(v_l_1109_) == 0)
{
lean_object* v_r_1110_; lean_object* v_k_1111_; lean_object* v_v_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1123_; 
lean_inc_ref(v_l_1109_);
v_r_1110_ = lean_ctor_get(v_impl_1022_, 4);
v_k_1111_ = lean_ctor_get(v_impl_1022_, 1);
v_v_1112_ = lean_ctor_get(v_impl_1022_, 2);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_impl_1022_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; lean_object* v_unused_1125_; 
v_unused_1124_ = lean_ctor_get(v_impl_1022_, 3);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_impl_1022_, 0);
lean_dec(v_unused_1125_);
v___x_1114_ = v_impl_1022_;
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_r_1110_);
lean_inc(v_v_1112_);
lean_inc(v_k_1111_);
lean_dec(v_impl_1022_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1110_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 3, v_r_1110_);
lean_ctor_set(v___x_1114_, 2, v_v_1015_);
lean_ctor_set(v___x_1114_, 1, v_k_1014_);
lean_ctor_set(v___x_1114_, 0, v___x_1023_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_r_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_r_1110_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v___x_1118_);
lean_ctor_set(v___x_1019_, 3, v_l_1109_);
lean_ctor_set(v___x_1019_, 2, v_v_1112_);
lean_ctor_set(v___x_1019_, 1, v_k_1111_);
lean_ctor_set(v___x_1019_, 0, v___x_1116_);
v___x_1120_ = v___x_1019_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_k_1111_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_v_1112_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_l_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_r_1126_; 
v_r_1126_ = lean_ctor_get(v_impl_1022_, 4);
lean_inc(v_r_1126_);
if (lean_obj_tag(v_r_1126_) == 0)
{
lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1151_; 
lean_inc(v_l_1109_);
v_k_1127_ = lean_ctor_get(v_impl_1022_, 1);
v_v_1128_ = lean_ctor_get(v_impl_1022_, 2);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_impl_1022_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; lean_object* v_unused_1153_; lean_object* v_unused_1154_; 
v_unused_1152_ = lean_ctor_get(v_impl_1022_, 4);
lean_dec(v_unused_1152_);
v_unused_1153_ = lean_ctor_get(v_impl_1022_, 3);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_impl_1022_, 0);
lean_dec(v_unused_1154_);
v___x_1130_ = v_impl_1022_;
v_isShared_1131_ = v_isSharedCheck_1151_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
lean_dec(v_impl_1022_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1151_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_k_1132_; lean_object* v_v_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1147_; 
v_k_1132_ = lean_ctor_get(v_r_1126_, 1);
v_v_1133_ = lean_ctor_get(v_r_1126_, 2);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_r_1126_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; 
v_unused_1148_ = lean_ctor_get(v_r_1126_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_r_1126_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_r_1126_, 0);
lean_dec(v_unused_1150_);
v___x_1135_ = v_r_1126_;
v_isShared_1136_ = v_isSharedCheck_1147_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_v_1133_);
lean_inc(v_k_1132_);
lean_dec(v_r_1126_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1147_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = lean_unsigned_to_nat(3u);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 4, v_l_1109_);
lean_ctor_set(v___x_1135_, 3, v_l_1109_);
lean_ctor_set(v___x_1135_, 2, v_v_1128_);
lean_ctor_set(v___x_1135_, 1, v_k_1127_);
lean_ctor_set(v___x_1135_, 0, v___x_1023_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_l_1109_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_l_1109_);
v___x_1139_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v_l_1109_);
lean_ctor_set(v___x_1130_, 2, v_v_1015_);
lean_ctor_set(v___x_1130_, 1, v_k_1014_);
lean_ctor_set(v___x_1130_, 0, v___x_1023_);
v___x_1141_ = v___x_1130_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_l_1109_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_l_1109_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v___x_1141_);
lean_ctor_set(v___x_1019_, 3, v___x_1139_);
lean_ctor_set(v___x_1019_, 2, v_v_1133_);
lean_ctor_set(v___x_1019_, 1, v_k_1132_);
lean_ctor_set(v___x_1019_, 0, v___x_1137_);
v___x_1143_ = v___x_1019_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_1132_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_1133_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(2u);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_r_1126_);
lean_ctor_set(v___x_1019_, 3, v_impl_1022_);
lean_ctor_set(v___x_1019_, 0, v___x_1155_);
v___x_1157_ = v___x_1019_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_impl_1022_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_r_1126_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1160_; 
lean_dec(v_v_1015_);
lean_dec(v_k_1014_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 2, v_v_1011_);
lean_ctor_set(v___x_1019_, 1, v_k_1010_);
v___x_1160_ = v___x_1019_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_size_1013_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_k_1010_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_v_1011_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_l_1016_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_r_1017_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
default: 
{
lean_object* v_impl_1162_; lean_object* v___x_1163_; 
lean_dec(v_size_1013_);
v_impl_1162_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_1010_, v_v_1011_, v_r_1017_);
v___x_1163_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1016_) == 0)
{
lean_object* v_size_1164_; lean_object* v_size_1165_; lean_object* v_k_1166_; lean_object* v_v_1167_; lean_object* v_l_1168_; lean_object* v_r_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_size_1164_ = lean_ctor_get(v_l_1016_, 0);
v_size_1165_ = lean_ctor_get(v_impl_1162_, 0);
v_k_1166_ = lean_ctor_get(v_impl_1162_, 1);
v_v_1167_ = lean_ctor_get(v_impl_1162_, 2);
v_l_1168_ = lean_ctor_get(v_impl_1162_, 3);
lean_inc(v_l_1168_);
v_r_1169_ = lean_ctor_get(v_impl_1162_, 4);
v___x_1170_ = lean_unsigned_to_nat(3u);
v___x_1171_ = lean_nat_mul(v___x_1170_, v_size_1164_);
v___x_1172_ = lean_nat_dec_lt(v___x_1171_, v_size_1165_);
lean_dec(v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_dec(v_l_1168_);
v___x_1173_ = lean_nat_add(v___x_1163_, v_size_1164_);
v___x_1174_ = lean_nat_add(v___x_1173_, v_size_1165_);
lean_dec(v___x_1173_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_impl_1162_);
lean_ctor_set(v___x_1019_, 0, v___x_1174_);
v___x_1176_ = v___x_1019_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_l_1016_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_impl_1162_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1241_; 
lean_inc(v_r_1169_);
lean_inc(v_v_1167_);
lean_inc(v_k_1166_);
lean_inc(v_size_1165_);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_impl_1162_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; lean_object* v_unused_1243_; lean_object* v_unused_1244_; lean_object* v_unused_1245_; lean_object* v_unused_1246_; 
v_unused_1242_ = lean_ctor_get(v_impl_1162_, 4);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v_impl_1162_, 3);
lean_dec(v_unused_1243_);
v_unused_1244_ = lean_ctor_get(v_impl_1162_, 2);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v_impl_1162_, 1);
lean_dec(v_unused_1245_);
v_unused_1246_ = lean_ctor_get(v_impl_1162_, 0);
lean_dec(v_unused_1246_);
v___x_1179_ = v_impl_1162_;
v_isShared_1180_ = v_isSharedCheck_1241_;
goto v_resetjp_1178_;
}
else
{
lean_dec(v_impl_1162_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1241_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_size_1181_; lean_object* v_k_1182_; lean_object* v_v_1183_; lean_object* v_l_1184_; lean_object* v_r_1185_; lean_object* v_size_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_size_1181_ = lean_ctor_get(v_l_1168_, 0);
v_k_1182_ = lean_ctor_get(v_l_1168_, 1);
v_v_1183_ = lean_ctor_get(v_l_1168_, 2);
v_l_1184_ = lean_ctor_get(v_l_1168_, 3);
v_r_1185_ = lean_ctor_get(v_l_1168_, 4);
v_size_1186_ = lean_ctor_get(v_r_1169_, 0);
v___x_1187_ = lean_unsigned_to_nat(2u);
v___x_1188_ = lean_nat_mul(v___x_1187_, v_size_1186_);
v___x_1189_ = lean_nat_dec_lt(v_size_1181_, v___x_1188_);
lean_dec(v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1217_; 
lean_inc(v_r_1185_);
lean_inc(v_l_1184_);
lean_inc(v_v_1183_);
lean_inc(v_k_1182_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_l_1168_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; lean_object* v_unused_1219_; lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; 
v_unused_1218_ = lean_ctor_get(v_l_1168_, 4);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_l_1168_, 3);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_l_1168_, 2);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_l_1168_, 1);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_l_1168_, 0);
lean_dec(v_unused_1222_);
v___x_1191_ = v_l_1168_;
v_isShared_1192_ = v_isSharedCheck_1217_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v_l_1168_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1217_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1207_; 
v___x_1193_ = lean_nat_add(v___x_1163_, v_size_1164_);
v___x_1194_ = lean_nat_add(v___x_1193_, v_size_1165_);
lean_dec(v_size_1165_);
if (lean_obj_tag(v_l_1184_) == 0)
{
lean_object* v_size_1215_; 
v_size_1215_ = lean_ctor_get(v_l_1184_, 0);
lean_inc(v_size_1215_);
v___y_1207_ = v_size_1215_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_unsigned_to_nat(0u);
v___y_1207_ = v___x_1216_;
goto v___jp_1206_;
}
v___jp_1195_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_nat_add(v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec(v___y_1197_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 4, v_r_1169_);
lean_ctor_set(v___x_1191_, 3, v_r_1185_);
lean_ctor_set(v___x_1191_, 2, v_v_1167_);
lean_ctor_set(v___x_1191_, 1, v_k_1166_);
lean_ctor_set(v___x_1191_, 0, v___x_1199_);
v___x_1201_ = v___x_1191_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1166_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1167_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_r_1185_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_r_1169_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 4, v___x_1201_);
lean_ctor_set(v___x_1179_, 3, v___y_1196_);
lean_ctor_set(v___x_1179_, 2, v_v_1183_);
lean_ctor_set(v___x_1179_, 1, v_k_1182_);
lean_ctor_set(v___x_1179_, 0, v___x_1194_);
v___x_1203_ = v___x_1179_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1182_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1183_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___y_1196_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
v___jp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_nat_add(v___x_1193_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec(v___x_1193_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_l_1184_);
lean_ctor_set(v___x_1019_, 0, v___x_1208_);
v___x_1210_ = v___x_1019_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_l_1016_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_l_1184_);
v___x_1210_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_nat_add(v___x_1163_, v_size_1186_);
if (lean_obj_tag(v_r_1185_) == 0)
{
lean_object* v_size_1212_; 
v_size_1212_ = lean_ctor_get(v_r_1185_, 0);
lean_inc(v_size_1212_);
v___y_1196_ = v___x_1210_;
v___y_1197_ = v___x_1211_;
v___y_1198_ = v_size_1212_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___y_1196_ = v___x_1210_;
v___y_1197_ = v___x_1211_;
v___y_1198_ = v___x_1213_;
goto v___jp_1195_;
}
}
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
lean_del_object(v___x_1019_);
v___x_1223_ = lean_nat_add(v___x_1163_, v_size_1164_);
v___x_1224_ = lean_nat_add(v___x_1223_, v_size_1165_);
lean_dec(v_size_1165_);
v___x_1225_ = lean_nat_add(v___x_1223_, v_size_1181_);
lean_dec(v___x_1223_);
lean_inc_ref(v_l_1016_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 4, v_l_1168_);
lean_ctor_set(v___x_1179_, 3, v_l_1016_);
lean_ctor_set(v___x_1179_, 2, v_v_1015_);
lean_ctor_set(v___x_1179_, 1, v_k_1014_);
lean_ctor_set(v___x_1179_, 0, v___x_1225_);
v___x_1227_ = v___x_1179_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_l_1016_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_l_1168_);
v___x_1227_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_isSharedCheck_1234_ = !lean_is_exclusive(v_l_1016_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; lean_object* v_unused_1238_; lean_object* v_unused_1239_; 
v_unused_1235_ = lean_ctor_get(v_l_1016_, 4);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_l_1016_, 3);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_l_1016_, 2);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_l_1016_, 1);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_l_1016_, 0);
lean_dec(v_unused_1239_);
v___x_1229_ = v_l_1016_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v_l_1016_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v_r_1169_);
lean_ctor_set(v___x_1229_, 3, v___x_1227_);
lean_ctor_set(v___x_1229_, 2, v_v_1167_);
lean_ctor_set(v___x_1229_, 1, v_k_1166_);
lean_ctor_set(v___x_1229_, 0, v___x_1224_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_k_1166_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_v_1167_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_r_1169_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1247_; 
v_l_1247_ = lean_ctor_get(v_impl_1162_, 3);
lean_inc(v_l_1247_);
if (lean_obj_tag(v_l_1247_) == 0)
{
lean_object* v_r_1248_; lean_object* v_k_1249_; lean_object* v_v_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1273_; 
v_r_1248_ = lean_ctor_get(v_impl_1162_, 4);
v_k_1249_ = lean_ctor_get(v_impl_1162_, 1);
v_v_1250_ = lean_ctor_get(v_impl_1162_, 2);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_impl_1162_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; lean_object* v_unused_1275_; 
v_unused_1274_ = lean_ctor_get(v_impl_1162_, 3);
lean_dec(v_unused_1274_);
v_unused_1275_ = lean_ctor_get(v_impl_1162_, 0);
lean_dec(v_unused_1275_);
v___x_1252_ = v_impl_1162_;
v_isShared_1253_ = v_isSharedCheck_1273_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_r_1248_);
lean_inc(v_v_1250_);
lean_inc(v_k_1249_);
lean_dec(v_impl_1162_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1273_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1269_; 
v_k_1254_ = lean_ctor_get(v_l_1247_, 1);
v_v_1255_ = lean_ctor_get(v_l_1247_, 2);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_l_1247_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; lean_object* v_unused_1271_; lean_object* v_unused_1272_; 
v_unused_1270_ = lean_ctor_get(v_l_1247_, 4);
lean_dec(v_unused_1270_);
v_unused_1271_ = lean_ctor_get(v_l_1247_, 3);
lean_dec(v_unused_1271_);
v_unused_1272_ = lean_ctor_get(v_l_1247_, 0);
lean_dec(v_unused_1272_);
v___x_1257_ = v_l_1247_;
v_isShared_1258_ = v_isSharedCheck_1269_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
lean_dec(v_l_1247_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1269_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1248_, 2);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 4, v_r_1248_);
lean_ctor_set(v___x_1257_, 3, v_r_1248_);
lean_ctor_set(v___x_1257_, 2, v_v_1015_);
lean_ctor_set(v___x_1257_, 1, v_k_1014_);
lean_ctor_set(v___x_1257_, 0, v___x_1163_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_r_1248_);
v___x_1261_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
lean_inc(v_r_1248_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 3, v_r_1248_);
lean_ctor_set(v___x_1252_, 0, v___x_1163_);
v___x_1263_ = v___x_1252_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1249_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1250_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_r_1248_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v___x_1263_);
lean_ctor_set(v___x_1019_, 3, v___x_1261_);
lean_ctor_set(v___x_1019_, 2, v_v_1255_);
lean_ctor_set(v___x_1019_, 1, v_k_1254_);
lean_ctor_set(v___x_1019_, 0, v___x_1259_);
v___x_1265_ = v___x_1019_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
else
{
lean_object* v_r_1276_; 
v_r_1276_ = lean_ctor_get(v_impl_1162_, 4);
lean_inc(v_r_1276_);
if (lean_obj_tag(v_r_1276_) == 0)
{
lean_object* v_k_1277_; lean_object* v_v_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1289_; 
v_k_1277_ = lean_ctor_get(v_impl_1162_, 1);
v_v_1278_ = lean_ctor_get(v_impl_1162_, 2);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_impl_1162_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; lean_object* v_unused_1291_; lean_object* v_unused_1292_; 
v_unused_1290_ = lean_ctor_get(v_impl_1162_, 4);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v_impl_1162_, 3);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v_impl_1162_, 0);
lean_dec(v_unused_1292_);
v___x_1280_ = v_impl_1162_;
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_v_1278_);
lean_inc(v_k_1277_);
lean_dec(v_impl_1162_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_unsigned_to_nat(3u);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 4, v_l_1247_);
lean_ctor_set(v___x_1280_, 2, v_v_1015_);
lean_ctor_set(v___x_1280_, 1, v_k_1014_);
lean_ctor_set(v___x_1280_, 0, v___x_1163_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_l_1247_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v_l_1247_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_r_1276_);
lean_ctor_set(v___x_1019_, 3, v___x_1284_);
lean_ctor_set(v___x_1019_, 2, v_v_1278_);
lean_ctor_set(v___x_1019_, 1, v_k_1277_);
lean_ctor_set(v___x_1019_, 0, v___x_1282_);
v___x_1286_ = v___x_1019_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1277_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1278_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_r_1276_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1293_ = lean_unsigned_to_nat(2u);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v_impl_1162_);
lean_ctor_set(v___x_1019_, 3, v_r_1276_);
lean_ctor_set(v___x_1019_, 0, v___x_1293_);
v___x_1295_ = v___x_1019_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_r_1276_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_impl_1162_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
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
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_k_1010_);
lean_ctor_set(v___x_1299_, 2, v_v_1011_);
lean_ctor_set(v___x_1299_, 3, v_t_1012_);
lean_ctor_set(v___x_1299_, 4, v_t_1012_);
return v___x_1299_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(lean_object* v___x_1303_, lean_object* v_as_1304_, size_t v_i_1305_, size_t v_stop_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_usize_dec_eq(v_i_1305_, v_stop_1306_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v_name_1312_; lean_object* v_kind_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_array_uget_borrowed(v_as_1304_, v_i_1305_);
v_name_1312_ = lean_ctor_get(v___x_1311_, 1);
v_kind_1313_ = lean_ctor_get(v___x_1311_, 2);
v___x_1314_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_b_1307_, v_name_1312_);
if (lean_obj_tag(v___x_1314_) == 1)
{
lean_object* v_val_1315_; lean_object* v_kind_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_b_1307_);
v_val_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_val_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v_kind_1316_ = lean_ctor_get(v_val_1315_, 2);
lean_inc(v_kind_1316_);
lean_dec(v_val_1315_);
v___x_1317_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__0));
v___x_1318_ = lean_string_append(v___x_1303_, v___x_1317_);
v___x_1319_ = 1;
lean_inc(v_name_1312_);
v___x_1320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1312_, v___x_1319_);
v___x_1321_ = lean_string_append(v___x_1318_, v___x_1320_);
lean_dec_ref(v___x_1320_);
v___x_1322_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__1));
v___x_1323_ = lean_string_append(v___x_1321_, v___x_1322_);
v___x_1324_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1316_, v___x_1319_);
v___x_1325_ = lean_string_append(v___x_1323_, v___x_1324_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___closed__2));
v___x_1327_ = lean_string_append(v___x_1325_, v___x_1326_);
lean_inc(v_kind_1313_);
v___x_1328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1313_, v___x_1319_);
v___x_1329_ = lean_string_append(v___x_1327_, v___x_1328_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
v___x_1332_ = 3;
v___x_1333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*1, v___x_1332_);
v___x_1334_ = lean_array_get_size(v___y_1308_);
v___x_1335_ = lean_array_push(v___y_1308_, v___x_1333_);
v___x_1336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; 
lean_dec(v___x_1314_);
lean_inc(v___x_1311_);
lean_inc(v_name_1312_);
v___x_1337_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_name_1312_, v___x_1311_, v_b_1307_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1305_, v___x_1338_);
v_i_1305_ = v___x_1339_;
v_b_1307_ = v___x_1337_;
goto _start;
}
}
else
{
lean_object* v___x_1341_; 
lean_dec_ref(v___x_1303_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_b_1307_);
lean_ctor_set(v___x_1341_, 1, v___y_1308_);
return v___x_1341_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1303_ = stack[0].m_obj;
lean_object* v_as_1304_ = stack[1].m_obj;
size_t v_i_1305_ = stack[2].m_num;
size_t v_stop_1306_ = stack[3].m_num;
lean_object* v_b_1307_ = stack[4].m_obj;
lean_object* v___y_1308_ = stack[5].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1303_, v_as_1304_, v_i_1305_, v_stop_1306_, v_b_1307_, v___y_1308_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg___boxed(lean_object* v___x_1343_, lean_object* v_as_1344_, lean_object* v_i_1345_, lean_object* v_stop_1346_, lean_object* v_b_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
size_t v_i_boxed_1350_; size_t v_stop_boxed_1351_; lean_object* v_res_1352_; 
v_i_boxed_1350_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_stop_boxed_1351_ = lean_unbox_usize(v_stop_1346_);
lean_dec(v_stop_1346_);
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1343_, v_as_1344_, v_i_boxed_1350_, v_stop_boxed_1351_, v_b_1347_, v___y_1348_);
lean_dec_ref(v_as_1344_);
return v_res_1352_;
}
}
lean_object* l_Lake_LakefileConfig_loadFromEnv(lean_object* v_env_1359_, lean_object* v_opts_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_a_1364_; lean_object* v_a_1365_; lean_object* v_a_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1371_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1360_);
lean_inc_ref_n(v_env_1359_, 2);
v___f_1372_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1372_, 0, v_env_1359_);
lean_closure_set(v___f_1372_, 1, v_opts_1360_);
lean_closure_set(v___f_1372_, 2, v___x_1371_);
v___x_1373_ = l_Lake_instTypeNameScriptFn;
v___x_1374_ = l___private_Lake_Load_Lean_Eval_0__Lake_PackageDecl_loadFromEnv(v_env_1359_, v_opts_1360_);
v___x_1375_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v_baseName_1377_; lean_object* v_keyName_1378_; lean_object* v_config_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v_baseName_1377_ = lean_ctor_get(v_a_1376_, 0);
v_keyName_1378_ = lean_ctor_get(v_a_1376_, 1);
v_config_1379_ = lean_ctor_get(v_a_1376_, 3);
v___x_1380_ = 0;
lean_inc(v_baseName_1377_);
v___x_1381_ = l_Lean_Name_toString(v_baseName_1377_, v___x_1380_);
v___x_1382_ = lean_box(v___x_1380_);
lean_inc_ref(v_opts_1360_);
lean_inc_ref_n(v_env_1359_, 2);
lean_inc_ref(v___x_1381_);
v___f_1383_ = lean_alloc_closure((void*)(l_Lake_LakefileConfig_loadFromEnv___lam__1___boxed), 8, 5);
lean_closure_set(v___f_1383_, 0, v___x_1381_);
lean_closure_set(v___f_1383_, 1, v___x_1382_);
lean_closure_set(v___f_1383_, 2, v_env_1359_);
lean_closure_set(v___f_1383_, 3, v_opts_1360_);
lean_closure_set(v___f_1383_, 4, v___x_1373_);
v___x_1384_ = l_Lake_targetAttr;
v___x_1385_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_1359_, v___x_1384_, v___f_1372_);
v___x_1386_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v_toArray_1388_; size_t v_sz_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v_toArray_1388_ = lean_ctor_get(v_a_1387_, 1);
v_sz_1389_ = lean_array_size(v_toArray_1388_);
v___x_1390_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1388_);
lean_inc(v_keyName_1378_);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__4(v_keyName_1378_, v_sz_1389_, v___x_1390_, v_toArray_1388_, v_a_1361_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1655_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_a_1393_ = lean_ctor_get(v___x_1391_, 1);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1395_ = v___x_1391_;
v_isShared_1396_ = v_isSharedCheck_1655_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1655_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v_a_1433_; lean_object* v_a_1434_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v_a_1458_; lean_object* v_a_1459_; lean_object* v___y_1497_; lean_object* v_a_1498_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___x_1626_; lean_object* v_a_1628_; lean_object* v_a_1629_; lean_object* v___y_1637_; uint8_t v___x_1649_; 
v___x_1423_ = lean_box(1);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1626_ = lean_array_get_size(v_a_1392_);
v___x_1649_ = lean_nat_dec_lt(v___x_1424_, v___x_1626_);
if (v___x_1649_ == 0)
{
v_a_1628_ = v___x_1423_;
v_a_1629_ = v_a_1393_;
goto v___jp_1627_;
}
else
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_nat_dec_le(v___x_1626_, v___x_1626_);
if (v___x_1650_ == 0)
{
if (v___x_1649_ == 0)
{
v_a_1628_ = v___x_1423_;
v_a_1629_ = v_a_1393_;
goto v___jp_1627_;
}
else
{
size_t v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_usize_of_nat(v___x_1626_);
lean_inc_ref(v___x_1381_);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1381_, v_a_1392_, v___x_1390_, v___x_1651_, v___x_1423_, v_a_1393_);
v___y_1637_ = v___x_1652_;
goto v___jp_1636_;
}
}
else
{
size_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_usize_of_nat(v___x_1626_);
lean_inc_ref(v___x_1381_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1381_, v_a_1392_, v___x_1390_, v___x_1653_, v___x_1423_, v_a_1393_);
v___y_1637_ = v___x_1654_;
goto v___jp_1636_;
}
}
v___jp_1397_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___y_1407_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1410_, 0, v_a_1376_);
lean_ctor_set(v___x_1410_, 1, v___y_1400_);
lean_ctor_set(v___x_1410_, 2, v_a_1409_);
lean_ctor_set(v___x_1410_, 3, v_a_1392_);
lean_ctor_set(v___x_1410_, 4, v___y_1406_);
lean_ctor_set(v___x_1410_, 5, v___y_1399_);
lean_ctor_set(v___x_1410_, 6, v___y_1404_);
lean_ctor_set(v___x_1410_, 7, v___y_1403_);
lean_ctor_set(v___x_1410_, 8, v___y_1402_);
lean_ctor_set(v___x_1410_, 9, v___y_1401_);
lean_ctor_set(v___x_1410_, 10, v___y_1398_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v___y_1405_);
lean_ctor_set(v___x_1395_, 0, v___x_1410_);
v___x_1412_ = v___x_1395_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___y_1405_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_dec(v___y_1406_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v_a_1392_);
lean_dec(v_a_1376_);
v_a_1414_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1415_ = lean_io_error_to_string(v_a_1414_);
v___x_1416_ = 3;
v___x_1417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*1, v___x_1416_);
v___x_1418_ = lean_array_get_size(v___y_1405_);
v___x_1419_ = lean_array_push(v___y_1405_, v___x_1417_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 1);
lean_ctor_set(v___x_1395_, 1, v___x_1419_);
lean_ctor_set(v___x_1395_, 0, v___x_1418_);
v___x_1421_ = v___x_1395_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
v___jp_1425_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; size_t v_sz_1438_; lean_object* v___x_1439_; 
v___x_1435_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__0));
v___x_1436_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1359_, 2);
v___x_1437_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1436_, v_env_1359_);
v_sz_1438_ = lean_array_size(v___x_1437_);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__12(v_env_1359_, v_opts_1360_, v___x_1437_, v_sz_1438_, v___x_1390_, v___x_1435_);
lean_dec_ref(v___x_1437_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v___y_1398_ = v_a_1433_;
v___y_1399_ = v___y_1427_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___y_1429_;
v___y_1403_ = v___y_1430_;
v___y_1404_ = v___y_1431_;
v___y_1405_ = v_a_1434_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___x_1439_;
goto v___jp_1397_;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; size_t v_sz_1443_; lean_object* v___x_1444_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1359_, 2);
v___x_1442_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1441_, v_env_1359_);
v_sz_1443_ = lean_array_size(v___x_1442_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__13(v_env_1359_, v_opts_1360_, v___x_1442_, v_sz_1443_, v___x_1390_, v_a_1440_);
lean_dec_ref(v___x_1442_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v___y_1398_ = v_a_1433_;
v___y_1399_ = v___y_1427_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___y_1429_;
v___y_1403_ = v___y_1430_;
v___y_1404_ = v___y_1431_;
v___y_1405_ = v_a_1434_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___x_1444_;
goto v___jp_1397_;
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; size_t v_sz_1448_; lean_object* v___x_1449_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1359_);
v___x_1447_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1446_, v_env_1359_);
v_sz_1448_ = lean_array_size(v___x_1447_);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_LakefileConfig_loadFromEnv_spec__14(v_env_1359_, v_opts_1360_, v___x_1447_, v_sz_1448_, v___x_1390_, v_a_1445_);
lean_dec_ref(v___x_1447_);
lean_dec_ref(v_opts_1360_);
v___y_1398_ = v_a_1433_;
v___y_1399_ = v___y_1427_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___y_1429_;
v___y_1403_ = v___y_1430_;
v___y_1404_ = v___y_1431_;
v___y_1405_ = v_a_1434_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___x_1449_;
goto v___jp_1397_;
}
}
}
v___jp_1450_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; size_t v_sz_1462_; lean_object* v___x_1463_; 
v___x_1460_ = l_Lake_lintDriverAttr;
lean_inc_ref(v_env_1359_);
v___x_1461_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1460_, v_env_1359_);
v_sz_1462_ = lean_array_size(v___x_1461_);
lean_inc_ref(v___x_1381_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__15(v_a_1387_, v___y_1456_, v___x_1381_, v_sz_1462_, v___x_1390_, v___x_1461_, v_a_1459_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v_a_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
v_a_1465_ = lean_ctor_get(v___x_1463_, 1);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1463_, 2);
v___x_1466_ = lean_array_get_size(v_a_1464_);
v___x_1467_ = lean_nat_dec_lt(v___y_1453_, v___x_1466_);
if (v___x_1467_ == 0)
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_nat_dec_lt(v___x_1424_, v___x_1466_);
if (v___x_1468_ == 0)
{
lean_object* v_lintDriver_1469_; 
lean_dec(v_a_1464_);
lean_dec_ref(v___x_1381_);
v_lintDriver_1469_ = lean_ctor_get(v_config_1379_, 14);
lean_inc_ref(v_lintDriver_1469_);
v___y_1426_ = v___y_1452_;
v___y_1427_ = v___y_1451_;
v___y_1428_ = v_a_1458_;
v___y_1429_ = v___y_1454_;
v___y_1430_ = v___y_1455_;
v___y_1431_ = v___y_1456_;
v___y_1432_ = v___y_1457_;
v_a_1433_ = v_lintDriver_1469_;
v_a_1434_ = v_a_1465_;
goto v___jp_1425_;
}
else
{
lean_object* v_lintDriver_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_lintDriver_1470_ = lean_ctor_get(v_config_1379_, 14);
v___x_1471_ = lean_string_utf8_byte_size(v_lintDriver_1470_);
v___x_1472_ = lean_nat_dec_eq(v___x_1471_, v___x_1424_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v___x_1473_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__1));
v___x_1474_ = lean_string_append(v___x_1381_, v___x_1473_);
v___x_1475_ = 3;
v___x_1476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set_uint8(v___x_1476_, sizeof(void*)*1, v___x_1475_);
v___x_1477_ = lean_array_get_size(v_a_1465_);
v___x_1478_ = lean_array_push(v_a_1465_, v___x_1476_);
v_a_1368_ = v___x_1477_;
v_a_1369_ = v___x_1478_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref(v___x_1381_);
v___x_1479_ = lean_array_fget(v_a_1464_, v___x_1424_);
lean_dec(v_a_1464_);
v___x_1480_ = l_Lean_Name_toString(v___x_1479_, v___x_1468_);
v___y_1426_ = v___y_1452_;
v___y_1427_ = v___y_1451_;
v___y_1428_ = v_a_1458_;
v___y_1429_ = v___y_1454_;
v___y_1430_ = v___y_1455_;
v___y_1431_ = v___y_1456_;
v___y_1432_ = v___y_1457_;
v_a_1433_ = v___x_1480_;
v_a_1434_ = v_a_1465_;
goto v___jp_1425_;
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v___x_1481_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__2));
v___x_1482_ = lean_string_append(v___x_1381_, v___x_1481_);
v___x_1483_ = 3;
v___x_1484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*1, v___x_1483_);
v___x_1485_ = lean_array_get_size(v_a_1465_);
v___x_1486_ = lean_array_push(v_a_1465_, v___x_1484_);
v_a_1368_ = v___x_1485_;
v_a_1369_ = v___x_1486_;
goto v___jp_1367_;
}
}
else
{
lean_object* v_a_1487_; lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v_a_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1487_ = lean_ctor_get(v___x_1463_, 0);
v_a_1488_ = lean_ctor_get(v___x_1463_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1463_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_inc(v_a_1487_);
lean_dec(v___x_1463_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1487_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
v___jp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; size_t v_sz_1501_; lean_object* v___x_1502_; 
v___x_1499_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1359_);
v___x_1500_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1499_, v_env_1359_);
v_sz_1501_ = lean_array_size(v___x_1500_);
lean_inc_ref(v___x_1381_);
lean_inc(v_a_1387_);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__6(v_a_1387_, v___x_1381_, v_sz_1501_, v___x_1390_, v___x_1500_, v_a_1498_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
v_a_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1502_, 2);
v___x_1505_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1359_);
v___x_1506_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1359_, v___x_1505_, v___f_1383_, v_a_1504_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; size_t v_sz_1511_; lean_object* v___x_1512_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
v_a_1508_ = lean_ctor_get(v___x_1506_, 1);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1506_, 2);
v___x_1509_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1359_);
v___x_1510_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1509_, v_env_1359_);
v_sz_1511_ = lean_array_size(v___x_1510_);
lean_inc_ref(v___x_1381_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__8(v_a_1507_, v___x_1381_, v_sz_1511_, v___x_1390_, v___x_1510_, v_a_1508_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; size_t v_sz_1517_; lean_object* v___x_1518_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
v_a_1514_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1512_, 2);
v___x_1515_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1359_, 2);
v___x_1516_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1515_, v_env_1359_);
v_sz_1517_ = lean_array_size(v___x_1516_);
lean_inc(v_keyName_1378_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__9(v_env_1359_, v_opts_1360_, v_keyName_1378_, v_sz_1517_, v___x_1390_, v___x_1516_, v_a_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1576_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_a_1520_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1522_ = v___x_1518_;
v_isShared_1523_ = v_isSharedCheck_1576_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1576_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; size_t v_sz_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1524_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1359_, 2);
v___x_1525_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1524_, v_env_1359_);
v_sz_1526_ = lean_array_size(v___x_1525_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__10(v_env_1359_, v_opts_1360_, v_sz_1526_, v___x_1390_, v___x_1525_);
v___x_1528_ = l_IO_ofExcept___at___00Lake_LakefileConfig_loadFromEnv_spec__0___redArg(v___x_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; size_t v_sz_1532_; lean_object* v___x_1533_; 
lean_del_object(v___x_1522_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1359_);
v___x_1531_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1530_, v_env_1359_);
v_sz_1532_ = lean_array_size(v___x_1531_);
lean_inc_ref(v___x_1381_);
lean_inc(v_a_1387_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_LakefileConfig_loadFromEnv_spec__11(v_a_1387_, v_a_1507_, v___x_1381_, v_sz_1532_, v___x_1390_, v___x_1531_, v_a_1520_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v_a_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
v_a_1535_ = lean_ctor_get(v___x_1533_, 1);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1533_, 2);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_array_get_size(v_a_1534_);
v___x_1538_ = lean_nat_dec_lt(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_nat_dec_lt(v___x_1424_, v___x_1537_);
if (v___x_1539_ == 0)
{
lean_object* v_testDriver_1540_; 
lean_dec(v_a_1534_);
v_testDriver_1540_ = lean_ctor_get(v_config_1379_, 12);
lean_inc_ref(v_testDriver_1540_);
v___y_1451_ = v_a_1503_;
v___y_1452_ = v_a_1529_;
v___y_1453_ = v___x_1536_;
v___y_1454_ = v_a_1519_;
v___y_1455_ = v_a_1513_;
v___y_1456_ = v_a_1507_;
v___y_1457_ = v___y_1497_;
v_a_1458_ = v_testDriver_1540_;
v_a_1459_ = v_a_1535_;
goto v___jp_1450_;
}
else
{
lean_object* v_testDriver_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_testDriver_1541_ = lean_ctor_get(v_config_1379_, 12);
v___x_1542_ = lean_string_utf8_byte_size(v_testDriver_1541_);
v___x_1543_ = lean_nat_dec_eq(v___x_1542_, v___x_1424_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_a_1534_);
lean_dec(v_a_1529_);
lean_dec(v_a_1519_);
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1503_);
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v___x_1544_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__3));
v___x_1545_ = lean_string_append(v___x_1381_, v___x_1544_);
v___x_1546_ = 3;
v___x_1547_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*1, v___x_1546_);
v___x_1548_ = lean_array_get_size(v_a_1535_);
v___x_1549_ = lean_array_push(v_a_1535_, v___x_1547_);
v_a_1364_ = v___x_1548_;
v_a_1365_ = v___x_1549_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_array_fget(v_a_1534_, v___x_1424_);
lean_dec(v_a_1534_);
v___x_1551_ = l_Lean_Name_toString(v___x_1550_, v___x_1539_);
v___y_1451_ = v_a_1503_;
v___y_1452_ = v_a_1529_;
v___y_1453_ = v___x_1536_;
v___y_1454_ = v_a_1519_;
v___y_1455_ = v_a_1513_;
v___y_1456_ = v_a_1507_;
v___y_1457_ = v___y_1497_;
v_a_1458_ = v___x_1551_;
v_a_1459_ = v_a_1535_;
goto v___jp_1450_;
}
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v_a_1534_);
lean_dec(v_a_1529_);
lean_dec(v_a_1519_);
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1503_);
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v___x_1552_ = ((lean_object*)(l_Lake_LakefileConfig_loadFromEnv___closed__4));
v___x_1553_ = lean_string_append(v___x_1381_, v___x_1552_);
v___x_1554_ = 3;
v___x_1555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*1, v___x_1554_);
v___x_1556_ = lean_array_get_size(v_a_1535_);
v___x_1557_ = lean_array_push(v_a_1535_, v___x_1555_);
v_a_1364_ = v___x_1556_;
v_a_1365_ = v___x_1557_;
goto v___jp_1363_;
}
}
else
{
lean_object* v_a_1558_; lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1529_);
lean_dec(v_a_1519_);
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1503_);
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1558_ = lean_ctor_get(v___x_1533_, 0);
v_a_1559_ = lean_ctor_get(v___x_1533_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1533_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_inc(v_a_1558_);
lean_dec(v___x_1533_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1558_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
lean_dec(v_a_1519_);
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1503_);
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1567_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1568_ = lean_io_error_to_string(v_a_1567_);
v___x_1569_ = 3;
v___x_1570_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*1, v___x_1569_);
v___x_1571_ = lean_array_get_size(v_a_1520_);
v___x_1572_ = lean_array_push(v_a_1520_, v___x_1570_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set_tag(v___x_1522_, 1);
lean_ctor_set(v___x_1522_, 1, v___x_1572_);
lean_ctor_set(v___x_1522_, 0, v___x_1571_);
v___x_1574_ = v___x_1522_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1572_);
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
lean_dec(v_a_1513_);
lean_dec(v_a_1507_);
lean_dec(v_a_1503_);
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1577_ = lean_ctor_get(v___x_1518_, 0);
v_a_1578_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1518_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_inc(v_a_1577_);
lean_dec(v___x_1518_);
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
lean_dec(v_a_1507_);
lean_dec(v_a_1503_);
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1586_ = lean_ctor_get(v___x_1512_, 0);
v_a_1587_ = lean_ctor_get(v___x_1512_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1512_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_inc(v_a_1586_);
lean_dec(v___x_1512_);
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
else
{
lean_object* v_a_1595_; lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1503_);
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1595_ = lean_ctor_get(v___x_1506_, 0);
v_a_1596_ = lean_ctor_get(v___x_1506_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1506_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_inc(v_a_1595_);
lean_dec(v___x_1506_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1595_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v___y_1497_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___f_1383_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1604_ = lean_ctor_get(v___x_1502_, 0);
v_a_1605_ = lean_ctor_get(v___x_1502_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1502_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_inc(v_a_1604_);
lean_dec(v___x_1502_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1604_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
v___jp_1613_:
{
if (lean_obj_tag(v___y_1615_) == 0)
{
lean_object* v_a_1616_; 
v_a_1616_ = lean_ctor_get(v___y_1615_, 1);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___y_1615_, 2);
v___y_1497_ = v___y_1614_;
v_a_1498_ = v_a_1616_;
goto v___jp_1496_;
}
else
{
lean_object* v_a_1617_; lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v___y_1614_);
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___f_1383_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1617_ = lean_ctor_get(v___y_1615_, 0);
v_a_1618_ = lean_ctor_get(v___y_1615_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___y_1615_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___y_1615_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_inc(v_a_1617_);
lean_dec(v___y_1615_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1617_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
v___jp_1627_:
{
uint8_t v___x_1630_; 
v___x_1630_ = lean_nat_dec_lt(v___x_1424_, v___x_1626_);
if (v___x_1630_ == 0)
{
v___y_1497_ = v_a_1628_;
v_a_1498_ = v_a_1629_;
goto v___jp_1496_;
}
else
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_nat_dec_le(v___x_1626_, v___x_1626_);
if (v___x_1631_ == 0)
{
if (v___x_1630_ == 0)
{
v___y_1497_ = v_a_1628_;
v_a_1498_ = v_a_1629_;
goto v___jp_1496_;
}
else
{
size_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_usize_of_nat(v___x_1626_);
lean_inc_ref(v___x_1381_);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1381_, v_a_1392_, v___x_1390_, v___x_1632_, v___x_1423_, v_a_1629_);
v___y_1614_ = v_a_1628_;
v___y_1615_ = v___x_1633_;
goto v___jp_1613_;
}
}
else
{
size_t v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_usize_of_nat(v___x_1626_);
lean_inc_ref(v___x_1381_);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__16(v___x_1381_, v_a_1392_, v___x_1390_, v___x_1634_, v___x_1423_, v_a_1629_);
v___y_1614_ = v_a_1628_;
v___y_1615_ = v___x_1635_;
goto v___jp_1613_;
}
}
}
v___jp_1636_:
{
if (lean_obj_tag(v___y_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_a_1639_; 
v_a_1638_ = lean_ctor_get(v___y_1637_, 0);
lean_inc(v_a_1638_);
v_a_1639_ = lean_ctor_get(v___y_1637_, 1);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___y_1637_, 2);
v_a_1628_ = v_a_1638_;
v_a_1629_ = v_a_1639_;
goto v___jp_1627_;
}
else
{
lean_object* v_a_1640_; lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_del_object(v___x_1395_);
lean_dec(v_a_1392_);
lean_dec(v_a_1387_);
lean_dec_ref(v___f_1383_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1640_ = lean_ctor_get(v___y_1637_, 0);
v_a_1641_ = lean_ctor_get(v___y_1637_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___y_1637_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___y_1637_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_inc(v_a_1640_);
lean_dec(v___y_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1640_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_a_1387_);
lean_dec_ref(v___f_1383_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1656_ = lean_ctor_get(v___x_1391_, 0);
v_a_1657_ = lean_ctor_get(v___x_1391_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1391_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_inc(v_a_1656_);
lean_dec(v___x_1391_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1656_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref(v___f_1383_);
lean_dec_ref(v___x_1381_);
lean_dec(v_a_1376_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1665_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1666_ = lean_io_error_to_string(v_a_1665_);
v___x_1667_ = 3;
v___x_1668_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set_uint8(v___x_1668_, sizeof(void*)*1, v___x_1667_);
v___x_1669_ = lean_array_get_size(v_a_1361_);
v___x_1670_ = lean_array_push(v_a_1361_, v___x_1668_);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
return v___x_1671_;
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v___f_1372_);
lean_dec_ref(v_opts_1360_);
lean_dec_ref(v_env_1359_);
v_a_1672_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1673_ = lean_io_error_to_string(v_a_1672_);
v___x_1674_ = 3;
v___x_1675_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*1, v___x_1674_);
v___x_1676_ = lean_array_get_size(v_a_1361_);
v___x_1677_ = lean_array_push(v_a_1361_, v___x_1675_);
v___x_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
return v___x_1678_;
}
v___jp_1363_:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1364_);
lean_ctor_set(v___x_1366_, 1, v_a_1365_);
return v___x_1366_;
}
v___jp_1367_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1368_);
lean_ctor_set(v___x_1370_, 1, v_a_1369_);
return v___x_1370_;
}
}
}
LEAN_EXPORT void l_Lake_LakefileConfig_loadFromEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1359_ = stack[0].m_obj;
lean_object* v_opts_1360_ = stack[1].m_obj;
lean_object* v_a_1361_ = stack[2].m_obj;
lean_object* v_res_1679_;
v_res_1679_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1359_, v_opts_1360_, v_a_1361_);
stack->m_obj
 = v_res_1679_;
}
LEAN_EXPORT lean_object* l_Lake_LakefileConfig_loadFromEnv___boxed(lean_object* v_env_1680_, lean_object* v_opts_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lake_LakefileConfig_loadFromEnv(v_env_1680_, v_opts_1681_, v_a_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1(lean_object* v_00_u03b2_1685_, lean_object* v_inst_1686_, lean_object* v_t_1687_, lean_object* v_k_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___redArg(v_t_1687_, v_k_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1___boxed(lean_object* v_00_u03b2_1690_, lean_object* v_inst_1691_, lean_object* v_t_1692_, lean_object* v_k_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__1(v_00_u03b2_1690_, v_inst_1691_, v_t_1692_, v_k_1693_);
lean_dec(v_k_1693_);
lean_dec(v_t_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2(lean_object* v_00_u03b2_1695_, lean_object* v_k_1696_, lean_object* v_v_1697_, lean_object* v_t_1698_, lean_object* v_hl_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LakefileConfig_loadFromEnv_spec__2___redArg(v_k_1696_, v_v_1697_, v_t_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3(lean_object* v_00_u03b2_1701_, lean_object* v_env_1702_, lean_object* v_attr_1703_, lean_object* v_f_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___redArg(v_env_1702_, v_attr_1703_, v_f_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1706_, lean_object* v_env_1707_, lean_object* v_attr_1708_, lean_object* v_f_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3(v_00_u03b2_1706_, v_env_1707_, v_attr_1708_, v_f_1709_);
lean_dec_ref(v_attr_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(lean_object* v_00_u03b4_1711_, lean_object* v_t_1712_, lean_object* v_k_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___redArg(v_t_1712_, v_k_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1715_, lean_object* v_t_1716_, lean_object* v_k_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_LakefileConfig_loadFromEnv_spec__5(v_00_u03b4_1715_, v_t_1716_, v_k_1717_);
lean_dec(v_k_1717_);
lean_dec(v_t_1716_);
return v_res_1718_;
}
}
lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_object* v_00_u03b2_1719_, lean_object* v_env_1720_, lean_object* v_attr_1721_, lean_object* v_f_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___redArg(v_env_1720_, v_attr_1721_, v_f_1722_, v___y_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT void l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1720_ = stack[1].m_obj;
lean_object* v_attr_1721_ = stack[2].m_obj;
lean_object* v_f_1722_ = stack[3].m_obj;
lean_object* v___y_1723_ = stack[4].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(lean_box(0), v_env_1720_, v_attr_1721_, v_f_1722_, v___y_1723_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1727_, lean_object* v_env_1728_, lean_object* v_attr_1729_, lean_object* v_f_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7(v_00_u03b2_1727_, v_env_1728_, v_attr_1729_, v_f_1730_, v___y_1731_);
lean_dec_ref(v_attr_1729_);
return v_res_1733_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(lean_object* v___x_1734_, lean_object* v___x_1735_, lean_object* v_as_1736_, size_t v_i_1737_, size_t v_stop_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___redArg(v___x_1734_, v_as_1736_, v_i_1737_, v_stop_1738_, v_b_1739_, v___y_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1734_ = stack[0].m_obj;
lean_object* v___x_1735_ = stack[1].m_obj;
lean_object* v_as_1736_ = stack[2].m_obj;
size_t v_i_1737_ = stack[3].m_num;
size_t v_stop_1738_ = stack[4].m_num;
lean_object* v_b_1739_ = stack[5].m_obj;
lean_object* v___y_1740_ = stack[6].m_obj;
lean_object* v_res_1743_;
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1734_, v___x_1735_, v_as_1736_, v_i_1737_, v_stop_1738_, v_b_1739_, v___y_1740_);
stack->m_obj
 = v_res_1743_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17___boxed(lean_object* v___x_1744_, lean_object* v___x_1745_, lean_object* v_as_1746_, lean_object* v_i_1747_, lean_object* v_stop_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
size_t v_i_boxed_1752_; size_t v_stop_boxed_1753_; lean_object* v_res_1754_; 
v_i_boxed_1752_ = lean_unbox_usize(v_i_1747_);
lean_dec(v_i_1747_);
v_stop_boxed_1753_ = lean_unbox_usize(v_stop_1748_);
lean_dec(v_stop_1748_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LakefileConfig_loadFromEnv_spec__17(v___x_1744_, v___x_1745_, v_as_1746_, v_i_boxed_1752_, v_stop_boxed_1753_, v_b_1749_, v___y_1750_);
lean_dec_ref(v_as_1746_);
lean_dec(v___x_1745_);
return v_res_1754_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(lean_object* v_00_u03b2_1755_, lean_object* v_f_1756_, lean_object* v_as_1757_, size_t v_i_1758_, size_t v_stop_1759_, lean_object* v_b_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___redArg(v_f_1756_, v_as_1757_, v_i_1758_, v_stop_1759_, v_b_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1756_ = stack[1].m_obj;
lean_object* v_as_1757_ = stack[2].m_obj;
size_t v_i_1758_ = stack[3].m_num;
size_t v_stop_1759_ = stack[4].m_num;
lean_object* v_b_1760_ = stack[5].m_obj;
lean_object* v_res_1762_;
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(lean_box(0), v_f_1756_, v_as_1757_, v_i_1758_, v_stop_1759_, v_b_1760_);
stack->m_obj
 = v_res_1762_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1763_, lean_object* v_f_1764_, lean_object* v_as_1765_, lean_object* v_i_1766_, lean_object* v_stop_1767_, lean_object* v_b_1768_){
_start:
{
size_t v_i_boxed_1769_; size_t v_stop_boxed_1770_; lean_object* v_res_1771_; 
v_i_boxed_1769_ = lean_unbox_usize(v_i_1766_);
lean_dec(v_i_1766_);
v_stop_boxed_1770_ = lean_unbox_usize(v_stop_1767_);
lean_dec(v_stop_1767_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__3_spec__3(v_00_u03b2_1763_, v_f_1764_, v_as_1765_, v_i_boxed_1769_, v_stop_boxed_1770_, v_b_1768_);
lean_dec_ref(v_as_1765_);
return v_res_1771_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1772_, lean_object* v_f_1773_, lean_object* v_as_1774_, size_t v_i_1775_, size_t v_stop_1776_, lean_object* v_b_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___redArg(v_f_1773_, v_as_1774_, v_i_1775_, v_stop_1776_, v_b_1777_, v___y_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1773_ = stack[1].m_obj;
lean_object* v_as_1774_ = stack[2].m_obj;
size_t v_i_1775_ = stack[3].m_num;
size_t v_stop_1776_ = stack[4].m_num;
lean_object* v_b_1777_ = stack[5].m_obj;
lean_object* v___y_1778_ = stack[6].m_obj;
lean_object* v_res_1781_;
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(lean_box(0), v_f_1773_, v_as_1774_, v_i_1775_, v_stop_1776_, v_b_1777_, v___y_1778_);
stack->m_obj
 = v_res_1781_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1782_, lean_object* v_f_1783_, lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v_stop_1786_, lean_object* v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
size_t v_i_boxed_1790_; size_t v_stop_boxed_1791_; lean_object* v_res_1792_; 
v_i_boxed_1790_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_stop_boxed_1791_ = lean_unbox_usize(v_stop_1786_);
lean_dec(v_stop_1786_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_LakefileConfig_loadFromEnv_spec__7_spec__8(v_00_u03b2_1782_, v_f_1783_, v_as_1784_, v_i_boxed_1790_, v_stop_boxed_1791_, v_b_1787_, v___y_1788_);
lean_dec_ref(v_as_1784_);
return v_res_1792_;
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
