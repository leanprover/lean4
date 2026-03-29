// Lean compiler output
// Module: Lake.Load.Lean.Eval
// Imports: public import Lake.Config.Workspace import Lean.DocString import Lake.DSL.AttributesCore
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_moduleFacetAttr;
lean_object* l_Lake_OrderedTagAttribute_getAllEntries(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_packageFacetAttr;
extern lean_object* l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_libraryFacetAttr;
extern lean_object* l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBArray_mkEmpty___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_RBArray_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lake_packageAttr;
lean_object* lean_array_to_list(lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
extern lean_object* l_Lake_targetAttr;
extern lean_object* l_Lake_instTypeNameScriptFn_unsafe__1;
extern lean_object* l_Lake_lintDriverAttr;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultTargetAttr;
extern lean_object* l_Lake_scriptAttr;
extern lean_object* l_Lake_defaultScriptAttr;
extern lean_object* l_Lake_postUpdateAttr;
extern lean_object* l_Lake_packageDepAttr;
extern lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34_;
extern lean_object* l_Lake_testDriverAttr;
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
static const lean_string_object l_Lake_PackageDecl_loadFromEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "configuration file is missing a `package` declaration"};
static const lean_object* l_Lake_PackageDecl_loadFromEnv___closed__0 = (const lean_object*)&l_Lake_PackageDecl_loadFromEnv___closed__0_value;
static const lean_ctor_object l_Lake_PackageDecl_loadFromEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageDecl_loadFromEnv___closed__0_value)}};
static const lean_object* l_Lake_PackageDecl_loadFromEnv___closed__1 = (const lean_object*)&l_Lake_PackageDecl_loadFromEnv___closed__1_value;
static const lean_string_object l_Lake_PackageDecl_loadFromEnv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "configuration file has multiple `package` declarations"};
static const lean_object* l_Lake_PackageDecl_loadFromEnv___closed__2 = (const lean_object*)&l_Lake_PackageDecl_loadFromEnv___closed__2_value;
static const lean_ctor_object l_Lake_PackageDecl_loadFromEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageDecl_loadFromEnv___closed__2_value)}};
static const lean_object* l_Lake_PackageDecl_loadFromEnv___closed__3 = (const lean_object*)&l_Lake_PackageDecl_loadFromEnv___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_PackageDecl_loadFromEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageDecl_loadFromEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_loadFromEnv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_Package_loadFromEnv___lam__1___closed__0 = (const lean_object*)&l_Lake_Package_loadFromEnv___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' was already defined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "', but then redefined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' was defined in package '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "', but registered under '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "post-update hook was defined in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "', but was registered in '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": package is missing script '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' marked as a default"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = ": package is missing script or target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' marked as a lint driver"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": package is missing target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' marked as a test driver"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ": executable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' has the same root module '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "' as executable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_loadFromEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = ": cannot both set lintDriver and use @[lint_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__0 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__0_value;
static const lean_string_object l_Lake_Package_loadFromEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = ": only one script or executable can be tagged @[lint_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__1 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__1_value;
static const lean_string_object l_Lake_Package_loadFromEnv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = ": cannot both set testDriver and use @[test_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__2 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__2_value;
static const lean_string_object l_Lake_Package_loadFromEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = ": only one script, executable, or library can be tagged @[test_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__3 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetsFromEnv___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PackageDecl_loadFromEnv(lean_object* v_env_234_, lean_object* v_opts_235_){
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
v___x_239_ = ((lean_object*)(l_Lake_PackageDecl_loadFromEnv___closed__1));
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
v___x_242_ = l_Lake_instImpl_00___x40_Lake_Config_PackageConfig_1370621153____hygCtx___hyg_16_;
v___x_243_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_234_, v_opts_235_, v___x_242_, v_head_241_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
lean_dec_ref(v___x_238_);
lean_dec(v_tail_240_);
lean_dec_ref(v_env_234_);
v___x_244_ = ((lean_object*)(l_Lake_PackageDecl_loadFromEnv___closed__3));
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageDecl_loadFromEnv___boxed(lean_object* v_env_245_, lean_object* v_opts_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_PackageDecl_loadFromEnv(v_env_245_, v_opts_246_);
lean_dec_ref(v_opts_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(lean_object* v_e_248_){
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg___boxed(lean_object* v_e_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(v_e_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2(lean_object* v_00_u03b1_270_, lean_object* v_e_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(v_e_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___boxed(lean_object* v_00_u03b1_274_, lean_object* v_e_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2(v_00_u03b1_274_, v_e_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__0(lean_object* v_env_278_, lean_object* v_opts_279_, lean_object* v___x_280_, lean_object* v_name_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_278_, v_opts_279_, v___x_280_, v_name_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__0___boxed(lean_object* v_env_283_, lean_object* v_opts_284_, lean_object* v___x_285_, lean_object* v_name_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lake_Package_loadFromEnv___lam__0(v_env_283_, v_opts_284_, v___x_285_, v_name_286_);
lean_dec_ref(v_opts_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__1(lean_object* v_env_289_, lean_object* v_opts_290_, lean_object* v___x_291_, lean_object* v_self_292_, lean_object* v_scriptName_293_, lean_object* v___y_294_){
_start:
{
uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = 0;
lean_inc_n(v_scriptName_293_, 2);
v___x_297_ = l_Lean_Name_toString(v_scriptName_293_, v___x_296_);
lean_inc_ref(v_env_289_);
v___x_298_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_289_, v_opts_290_, v___x_291_, v_scriptName_293_);
v___x_299_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; uint8_t v___x_301_; lean_object* v___x_302_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref(v___x_299_);
v___x_301_ = 1;
v___x_302_ = l_Lean_findDocString_x3f(v_env_289_, v_scriptName_293_, v___x_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v_baseName_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref(v___x_302_);
v_baseName_304_ = lean_ctor_get(v_self_292_, 1);
lean_inc(v_baseName_304_);
lean_dec_ref(v_self_292_);
v___x_305_ = l_Lean_Name_toString(v_baseName_304_, v___x_296_);
v___x_306_ = ((lean_object*)(l_Lake_Package_loadFromEnv___lam__1___closed__0));
v___x_307_ = lean_string_append(v___x_305_, v___x_306_);
v___x_308_ = lean_string_append(v___x_307_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_a_300_);
lean_ctor_set(v___x_309_, 2, v_a_303_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___y_294_);
return v___x_310_;
}
else
{
lean_object* v_a_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_a_300_);
lean_dec_ref(v___x_297_);
lean_dec_ref(v_self_292_);
v_a_311_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_302_);
v___x_312_ = lean_io_error_to_string(v_a_311_);
v___x_313_ = 3;
v___x_314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*1, v___x_313_);
v___x_315_ = lean_array_get_size(v___y_294_);
v___x_316_ = lean_array_push(v___y_294_, v___x_314_);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
return v___x_317_;
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref(v___x_297_);
lean_dec(v_scriptName_293_);
lean_dec_ref(v_self_292_);
lean_dec_ref(v_env_289_);
v_a_318_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_318_);
lean_dec_ref(v___x_299_);
v___x_319_ = lean_io_error_to_string(v_a_318_);
v___x_320_ = 3;
v___x_321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*1, v___x_320_);
v___x_322_ = lean_array_get_size(v___y_294_);
v___x_323_ = lean_array_push(v___y_294_, v___x_321_);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___lam__1___boxed(lean_object* v_env_325_, lean_object* v_opts_326_, lean_object* v___x_327_, lean_object* v_self_328_, lean_object* v_scriptName_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lake_Package_loadFromEnv___lam__1(v_env_325_, v_opts_326_, v___x_327_, v_self_328_, v_scriptName_329_, v___y_330_);
lean_dec_ref(v_opts_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(lean_object* v_k_333_, lean_object* v_v_334_, lean_object* v_t_335_){
_start:
{
if (lean_obj_tag(v_t_335_) == 0)
{
lean_object* v_size_336_; lean_object* v_k_337_; lean_object* v_v_338_; lean_object* v_l_339_; lean_object* v_r_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_620_; 
v_size_336_ = lean_ctor_get(v_t_335_, 0);
v_k_337_ = lean_ctor_get(v_t_335_, 1);
v_v_338_ = lean_ctor_get(v_t_335_, 2);
v_l_339_ = lean_ctor_get(v_t_335_, 3);
v_r_340_ = lean_ctor_get(v_t_335_, 4);
v_isSharedCheck_620_ = !lean_is_exclusive(v_t_335_);
if (v_isSharedCheck_620_ == 0)
{
v___x_342_ = v_t_335_;
v_isShared_343_ = v_isSharedCheck_620_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_r_340_);
lean_inc(v_l_339_);
lean_inc(v_v_338_);
lean_inc(v_k_337_);
lean_inc(v_size_336_);
lean_dec(v_t_335_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_620_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___x_344_; 
v___x_344_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_333_, v_k_337_);
switch(v___x_344_)
{
case 0:
{
lean_object* v_impl_345_; lean_object* v___x_346_; 
lean_dec(v_size_336_);
v_impl_345_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_k_333_, v_v_334_, v_l_339_);
v___x_346_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_340_) == 0)
{
lean_object* v_size_347_; lean_object* v_size_348_; lean_object* v_k_349_; lean_object* v_v_350_; lean_object* v_l_351_; lean_object* v_r_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_size_347_ = lean_ctor_get(v_r_340_, 0);
v_size_348_ = lean_ctor_get(v_impl_345_, 0);
lean_inc(v_size_348_);
v_k_349_ = lean_ctor_get(v_impl_345_, 1);
lean_inc(v_k_349_);
v_v_350_ = lean_ctor_get(v_impl_345_, 2);
lean_inc(v_v_350_);
v_l_351_ = lean_ctor_get(v_impl_345_, 3);
lean_inc(v_l_351_);
v_r_352_ = lean_ctor_get(v_impl_345_, 4);
lean_inc(v_r_352_);
v___x_353_ = lean_unsigned_to_nat(3u);
v___x_354_ = lean_nat_mul(v___x_353_, v_size_347_);
v___x_355_ = lean_nat_dec_lt(v___x_354_, v_size_348_);
lean_dec(v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v_r_352_);
lean_dec(v_l_351_);
lean_dec(v_v_350_);
lean_dec(v_k_349_);
v___x_356_ = lean_nat_add(v___x_346_, v_size_348_);
lean_dec(v_size_348_);
v___x_357_ = lean_nat_add(v___x_356_, v_size_347_);
lean_dec(v___x_356_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 3, v_impl_345_);
lean_ctor_set(v___x_342_, 0, v___x_357_);
v___x_359_ = v___x_342_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_impl_345_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_r_340_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
else
{
lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_426_; 
v_isSharedCheck_426_ = !lean_is_exclusive(v_impl_345_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; lean_object* v_unused_428_; lean_object* v_unused_429_; lean_object* v_unused_430_; lean_object* v_unused_431_; 
v_unused_427_ = lean_ctor_get(v_impl_345_, 4);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v_impl_345_, 3);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_impl_345_, 2);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_impl_345_, 1);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_impl_345_, 0);
lean_dec(v_unused_431_);
v___x_362_ = v_impl_345_;
v_isShared_363_ = v_isSharedCheck_426_;
goto v_resetjp_361_;
}
else
{
lean_dec(v_impl_345_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_426_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_size_364_; lean_object* v_size_365_; lean_object* v_k_366_; lean_object* v_v_367_; lean_object* v_l_368_; lean_object* v_r_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_size_364_ = lean_ctor_get(v_l_351_, 0);
v_size_365_ = lean_ctor_get(v_r_352_, 0);
v_k_366_ = lean_ctor_get(v_r_352_, 1);
v_v_367_ = lean_ctor_get(v_r_352_, 2);
v_l_368_ = lean_ctor_get(v_r_352_, 3);
v_r_369_ = lean_ctor_get(v_r_352_, 4);
v___x_370_ = lean_unsigned_to_nat(2u);
v___x_371_ = lean_nat_mul(v___x_370_, v_size_364_);
v___x_372_ = lean_nat_dec_lt(v_size_365_, v___x_371_);
lean_dec(v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_401_; 
lean_inc(v_r_369_);
lean_inc(v_l_368_);
lean_inc(v_v_367_);
lean_inc(v_k_366_);
v_isSharedCheck_401_ = !lean_is_exclusive(v_r_352_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_402_ = lean_ctor_get(v_r_352_, 4);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_r_352_, 3);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_r_352_, 2);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_r_352_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_r_352_, 0);
lean_dec(v_unused_406_);
v___x_374_ = v_r_352_;
v_isShared_375_ = v_isSharedCheck_401_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_r_352_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_401_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_389_; lean_object* v___y_391_; 
v___x_376_ = lean_nat_add(v___x_346_, v_size_348_);
lean_dec(v_size_348_);
v___x_377_ = lean_nat_add(v___x_376_, v_size_347_);
lean_dec(v___x_376_);
v___x_389_ = lean_nat_add(v___x_346_, v_size_364_);
if (lean_obj_tag(v_l_368_) == 0)
{
lean_object* v_size_399_; 
v_size_399_ = lean_ctor_get(v_l_368_, 0);
lean_inc(v_size_399_);
v___y_391_ = v_size_399_;
goto v___jp_390_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v___y_391_ = v___x_400_;
goto v___jp_390_;
}
v___jp_378_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_nat_add(v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 4, v_r_340_);
lean_ctor_set(v___x_374_, 3, v_r_369_);
lean_ctor_set(v___x_374_, 2, v_v_338_);
lean_ctor_set(v___x_374_, 1, v_k_337_);
lean_ctor_set(v___x_374_, 0, v___x_382_);
v___x_384_ = v___x_374_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_r_369_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_r_340_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 4, v___x_384_);
lean_ctor_set(v___x_362_, 3, v___y_379_);
lean_ctor_set(v___x_362_, 2, v_v_367_);
lean_ctor_set(v___x_362_, 1, v_k_366_);
lean_ctor_set(v___x_362_, 0, v___x_377_);
v___x_386_ = v___x_362_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_k_366_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_v_367_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v___y_379_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_nat_add(v___x_389_, v___y_391_);
lean_dec(v___y_391_);
lean_dec(v___x_389_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_l_368_);
lean_ctor_set(v___x_342_, 3, v_l_351_);
lean_ctor_set(v___x_342_, 2, v_v_350_);
lean_ctor_set(v___x_342_, 1, v_k_349_);
lean_ctor_set(v___x_342_, 0, v___x_392_);
v___x_394_ = v___x_342_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_349_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_350_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_l_351_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_l_368_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_nat_add(v___x_346_, v_size_347_);
if (lean_obj_tag(v_r_369_) == 0)
{
lean_object* v_size_396_; 
v_size_396_ = lean_ctor_get(v_r_369_, 0);
lean_inc(v_size_396_);
v___y_379_ = v___x_394_;
v___y_380_ = v___x_395_;
v___y_381_ = v_size_396_;
goto v___jp_378_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___y_379_ = v___x_394_;
v___y_380_ = v___x_395_;
v___y_381_ = v___x_397_;
goto v___jp_378_;
}
}
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
lean_del_object(v___x_342_);
v___x_407_ = lean_nat_add(v___x_346_, v_size_348_);
lean_dec(v_size_348_);
v___x_408_ = lean_nat_add(v___x_407_, v_size_347_);
lean_dec(v___x_407_);
v___x_409_ = lean_nat_add(v___x_346_, v_size_347_);
v___x_410_ = lean_nat_add(v___x_409_, v_size_365_);
lean_dec(v___x_409_);
lean_inc_ref(v_r_340_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 4, v_r_340_);
lean_ctor_set(v___x_362_, 3, v_r_352_);
lean_ctor_set(v___x_362_, 2, v_v_338_);
lean_ctor_set(v___x_362_, 1, v_k_337_);
lean_ctor_set(v___x_362_, 0, v___x_410_);
v___x_412_ = v___x_362_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_r_352_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_r_340_);
v___x_412_ = v_reuseFailAlloc_425_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_isSharedCheck_419_ = !lean_is_exclusive(v_r_340_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; lean_object* v_unused_421_; lean_object* v_unused_422_; lean_object* v_unused_423_; lean_object* v_unused_424_; 
v_unused_420_ = lean_ctor_get(v_r_340_, 4);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_r_340_, 3);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_r_340_, 2);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v_r_340_, 1);
lean_dec(v_unused_423_);
v_unused_424_ = lean_ctor_get(v_r_340_, 0);
lean_dec(v_unused_424_);
v___x_414_ = v_r_340_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_r_340_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_412_);
lean_ctor_set(v___x_414_, 3, v_l_351_);
lean_ctor_set(v___x_414_, 2, v_v_350_);
lean_ctor_set(v___x_414_, 1, v_k_349_);
lean_ctor_set(v___x_414_, 0, v___x_408_);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_349_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_350_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_l_351_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v___x_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_432_; 
v_l_432_ = lean_ctor_get(v_impl_345_, 3);
lean_inc(v_l_432_);
if (lean_obj_tag(v_l_432_) == 0)
{
lean_object* v_r_433_; lean_object* v_k_434_; lean_object* v_v_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_446_; 
v_r_433_ = lean_ctor_get(v_impl_345_, 4);
v_k_434_ = lean_ctor_get(v_impl_345_, 1);
v_v_435_ = lean_ctor_get(v_impl_345_, 2);
v_isSharedCheck_446_ = !lean_is_exclusive(v_impl_345_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_447_ = lean_ctor_get(v_impl_345_, 3);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_impl_345_, 0);
lean_dec(v_unused_448_);
v___x_437_ = v_impl_345_;
v_isShared_438_ = v_isSharedCheck_446_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_r_433_);
lean_inc(v_v_435_);
lean_inc(v_k_434_);
lean_dec(v_impl_345_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_446_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_433_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 3, v_r_433_);
lean_ctor_set(v___x_437_, 2, v_v_338_);
lean_ctor_set(v___x_437_, 1, v_k_337_);
lean_ctor_set(v___x_437_, 0, v___x_346_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_r_433_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_r_433_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_441_);
lean_ctor_set(v___x_342_, 3, v_l_432_);
lean_ctor_set(v___x_342_, 2, v_v_435_);
lean_ctor_set(v___x_342_, 1, v_k_434_);
lean_ctor_set(v___x_342_, 0, v___x_439_);
v___x_443_ = v___x_342_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_k_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_v_435_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_l_432_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_r_449_; 
v_r_449_ = lean_ctor_get(v_impl_345_, 4);
lean_inc(v_r_449_);
if (lean_obj_tag(v_r_449_) == 0)
{
lean_object* v_k_450_; lean_object* v_v_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_474_; 
v_k_450_ = lean_ctor_get(v_impl_345_, 1);
v_v_451_ = lean_ctor_get(v_impl_345_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v_impl_345_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; 
v_unused_475_ = lean_ctor_get(v_impl_345_, 4);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_impl_345_, 3);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_impl_345_, 0);
lean_dec(v_unused_477_);
v___x_453_ = v_impl_345_;
v_isShared_454_ = v_isSharedCheck_474_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_v_451_);
lean_inc(v_k_450_);
lean_dec(v_impl_345_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_474_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_k_455_; lean_object* v_v_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_470_; 
v_k_455_ = lean_ctor_get(v_r_449_, 1);
v_v_456_ = lean_ctor_get(v_r_449_, 2);
v_isSharedCheck_470_ = !lean_is_exclusive(v_r_449_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_471_ = lean_ctor_get(v_r_449_, 4);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_r_449_, 3);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_r_449_, 0);
lean_dec(v_unused_473_);
v___x_458_ = v_r_449_;
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_v_456_);
lean_inc(v_k_455_);
lean_dec(v_r_449_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(3u);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_l_432_);
lean_ctor_set(v___x_458_, 3, v_l_432_);
lean_ctor_set(v___x_458_, 2, v_v_451_);
lean_ctor_set(v___x_458_, 1, v_k_450_);
lean_ctor_set(v___x_458_, 0, v___x_346_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_k_450_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_v_451_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_l_432_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_l_432_);
v___x_462_ = v_reuseFailAlloc_469_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 4, v_l_432_);
lean_ctor_set(v___x_453_, 2, v_v_338_);
lean_ctor_set(v___x_453_, 1, v_k_337_);
lean_ctor_set(v___x_453_, 0, v___x_346_);
v___x_464_ = v___x_453_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_l_432_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_l_432_);
v___x_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_466_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_464_);
lean_ctor_set(v___x_342_, 3, v___x_462_);
lean_ctor_set(v___x_342_, 2, v_v_456_);
lean_ctor_set(v___x_342_, 1, v_k_455_);
lean_ctor_set(v___x_342_, 0, v___x_460_);
v___x_466_ = v___x_342_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_k_455_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_v_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(2u);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_r_449_);
lean_ctor_set(v___x_342_, 3, v_impl_345_);
lean_ctor_set(v___x_342_, 0, v___x_478_);
v___x_480_ = v___x_342_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_impl_345_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_r_449_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
case 1:
{
lean_object* v___x_483_; 
lean_dec(v_v_338_);
lean_dec(v_k_337_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 2, v_v_334_);
lean_ctor_set(v___x_342_, 1, v_k_333_);
v___x_483_ = v___x_342_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_size_336_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_l_339_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_r_340_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
default: 
{
lean_object* v_impl_485_; lean_object* v___x_486_; 
lean_dec(v_size_336_);
v_impl_485_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_k_333_, v_v_334_, v_r_340_);
v___x_486_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_339_) == 0)
{
lean_object* v_size_487_; lean_object* v_size_488_; lean_object* v_k_489_; lean_object* v_v_490_; lean_object* v_l_491_; lean_object* v_r_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_size_487_ = lean_ctor_get(v_l_339_, 0);
v_size_488_ = lean_ctor_get(v_impl_485_, 0);
lean_inc(v_size_488_);
v_k_489_ = lean_ctor_get(v_impl_485_, 1);
lean_inc(v_k_489_);
v_v_490_ = lean_ctor_get(v_impl_485_, 2);
lean_inc(v_v_490_);
v_l_491_ = lean_ctor_get(v_impl_485_, 3);
lean_inc(v_l_491_);
v_r_492_ = lean_ctor_get(v_impl_485_, 4);
lean_inc(v_r_492_);
v___x_493_ = lean_unsigned_to_nat(3u);
v___x_494_ = lean_nat_mul(v___x_493_, v_size_487_);
v___x_495_ = lean_nat_dec_lt(v___x_494_, v_size_488_);
lean_dec(v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_r_492_);
lean_dec(v_l_491_);
lean_dec(v_v_490_);
lean_dec(v_k_489_);
v___x_496_ = lean_nat_add(v___x_486_, v_size_487_);
v___x_497_ = lean_nat_add(v___x_496_, v_size_488_);
lean_dec(v_size_488_);
lean_dec(v___x_496_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_impl_485_);
lean_ctor_set(v___x_342_, 0, v___x_497_);
v___x_499_ = v___x_342_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_l_339_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_impl_485_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_564_; 
v_isSharedCheck_564_ = !lean_is_exclusive(v_impl_485_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_565_ = lean_ctor_get(v_impl_485_, 4);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_impl_485_, 3);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_impl_485_, 2);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_impl_485_, 1);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_impl_485_, 0);
lean_dec(v_unused_569_);
v___x_502_ = v_impl_485_;
v_isShared_503_ = v_isSharedCheck_564_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_impl_485_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_564_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_size_504_; lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v_l_507_; lean_object* v_r_508_; lean_object* v_size_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_size_504_ = lean_ctor_get(v_l_491_, 0);
v_k_505_ = lean_ctor_get(v_l_491_, 1);
v_v_506_ = lean_ctor_get(v_l_491_, 2);
v_l_507_ = lean_ctor_get(v_l_491_, 3);
v_r_508_ = lean_ctor_get(v_l_491_, 4);
v_size_509_ = lean_ctor_get(v_r_492_, 0);
v___x_510_ = lean_unsigned_to_nat(2u);
v___x_511_ = lean_nat_mul(v___x_510_, v_size_509_);
v___x_512_ = lean_nat_dec_lt(v_size_504_, v___x_511_);
lean_dec(v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_540_; 
lean_inc(v_r_508_);
lean_inc(v_l_507_);
lean_inc(v_v_506_);
lean_inc(v_k_505_);
v_isSharedCheck_540_ = !lean_is_exclusive(v_l_491_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; lean_object* v_unused_544_; lean_object* v_unused_545_; 
v_unused_541_ = lean_ctor_get(v_l_491_, 4);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_l_491_, 3);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_l_491_, 2);
lean_dec(v_unused_543_);
v_unused_544_ = lean_ctor_get(v_l_491_, 1);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_l_491_, 0);
lean_dec(v_unused_545_);
v___x_514_ = v_l_491_;
v_isShared_515_ = v_isSharedCheck_540_;
goto v_resetjp_513_;
}
else
{
lean_dec(v_l_491_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_540_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_530_; 
v___x_516_ = lean_nat_add(v___x_486_, v_size_487_);
v___x_517_ = lean_nat_add(v___x_516_, v_size_488_);
lean_dec(v_size_488_);
if (lean_obj_tag(v_l_507_) == 0)
{
lean_object* v_size_538_; 
v_size_538_ = lean_ctor_get(v_l_507_, 0);
lean_inc(v_size_538_);
v___y_530_ = v_size_538_;
goto v___jp_529_;
}
else
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___y_530_ = v___x_539_;
goto v___jp_529_;
}
v___jp_518_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_nat_add(v___y_519_, v___y_521_);
lean_dec(v___y_521_);
lean_dec(v___y_519_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v_r_492_);
lean_ctor_set(v___x_514_, 3, v_r_508_);
lean_ctor_set(v___x_514_, 2, v_v_490_);
lean_ctor_set(v___x_514_, 1, v_k_489_);
lean_ctor_set(v___x_514_, 0, v___x_522_);
v___x_524_ = v___x_514_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_k_489_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_v_490_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_r_508_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v_r_492_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 4, v___x_524_);
lean_ctor_set(v___x_502_, 3, v___y_520_);
lean_ctor_set(v___x_502_, 2, v_v_506_);
lean_ctor_set(v___x_502_, 1, v_k_505_);
lean_ctor_set(v___x_502_, 0, v___x_517_);
v___x_526_ = v___x_502_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_k_505_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_v_506_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v___y_520_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = lean_nat_add(v___x_516_, v___y_530_);
lean_dec(v___y_530_);
lean_dec(v___x_516_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_l_507_);
lean_ctor_set(v___x_342_, 0, v___x_531_);
v___x_533_ = v___x_342_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_l_339_);
lean_ctor_set(v_reuseFailAlloc_537_, 4, v_l_507_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = lean_nat_add(v___x_486_, v_size_509_);
if (lean_obj_tag(v_r_508_) == 0)
{
lean_object* v_size_535_; 
v_size_535_ = lean_ctor_get(v_r_508_, 0);
lean_inc(v_size_535_);
v___y_519_ = v___x_534_;
v___y_520_ = v___x_533_;
v___y_521_ = v_size_535_;
goto v___jp_518_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___y_519_ = v___x_534_;
v___y_520_ = v___x_533_;
v___y_521_ = v___x_536_;
goto v___jp_518_;
}
}
}
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
lean_del_object(v___x_342_);
v___x_546_ = lean_nat_add(v___x_486_, v_size_487_);
v___x_547_ = lean_nat_add(v___x_546_, v_size_488_);
lean_dec(v_size_488_);
v___x_548_ = lean_nat_add(v___x_546_, v_size_504_);
lean_dec(v___x_546_);
lean_inc_ref(v_l_339_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 4, v_l_491_);
lean_ctor_set(v___x_502_, 3, v_l_339_);
lean_ctor_set(v___x_502_, 2, v_v_338_);
lean_ctor_set(v___x_502_, 1, v_k_337_);
lean_ctor_set(v___x_502_, 0, v___x_548_);
v___x_550_ = v___x_502_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_l_339_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_l_491_);
v___x_550_ = v_reuseFailAlloc_563_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_isSharedCheck_557_ = !lean_is_exclusive(v_l_339_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; lean_object* v_unused_560_; lean_object* v_unused_561_; lean_object* v_unused_562_; 
v_unused_558_ = lean_ctor_get(v_l_339_, 4);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_l_339_, 3);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_l_339_, 2);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_l_339_, 1);
lean_dec(v_unused_561_);
v_unused_562_ = lean_ctor_get(v_l_339_, 0);
lean_dec(v_unused_562_);
v___x_552_ = v_l_339_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_dec(v_l_339_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 4, v_r_492_);
lean_ctor_set(v___x_552_, 3, v___x_550_);
lean_ctor_set(v___x_552_, 2, v_v_490_);
lean_ctor_set(v___x_552_, 1, v_k_489_);
lean_ctor_set(v___x_552_, 0, v___x_547_);
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_489_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_490_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_r_492_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_570_; 
v_l_570_ = lean_ctor_get(v_impl_485_, 3);
lean_inc(v_l_570_);
if (lean_obj_tag(v_l_570_) == 0)
{
lean_object* v_r_571_; lean_object* v_k_572_; lean_object* v_v_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_596_; 
v_r_571_ = lean_ctor_get(v_impl_485_, 4);
v_k_572_ = lean_ctor_get(v_impl_485_, 1);
v_v_573_ = lean_ctor_get(v_impl_485_, 2);
v_isSharedCheck_596_ = !lean_is_exclusive(v_impl_485_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; lean_object* v_unused_598_; 
v_unused_597_ = lean_ctor_get(v_impl_485_, 3);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v_impl_485_, 0);
lean_dec(v_unused_598_);
v___x_575_ = v_impl_485_;
v_isShared_576_ = v_isSharedCheck_596_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_r_571_);
lean_inc(v_v_573_);
lean_inc(v_k_572_);
lean_dec(v_impl_485_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_596_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_k_577_; lean_object* v_v_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_592_; 
v_k_577_ = lean_ctor_get(v_l_570_, 1);
v_v_578_ = lean_ctor_get(v_l_570_, 2);
v_isSharedCheck_592_ = !lean_is_exclusive(v_l_570_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; 
v_unused_593_ = lean_ctor_get(v_l_570_, 4);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_l_570_, 3);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_l_570_, 0);
lean_dec(v_unused_595_);
v___x_580_ = v_l_570_;
v_isShared_581_ = v_isSharedCheck_592_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_v_578_);
lean_inc(v_k_577_);
lean_dec(v_l_570_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_592_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_571_, 2);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 4, v_r_571_);
lean_ctor_set(v___x_580_, 3, v_r_571_);
lean_ctor_set(v___x_580_, 2, v_v_338_);
lean_ctor_set(v___x_580_, 1, v_k_337_);
lean_ctor_set(v___x_580_, 0, v___x_486_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_r_571_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_r_571_);
v___x_584_ = v_reuseFailAlloc_591_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
lean_inc(v_r_571_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 3, v_r_571_);
lean_ctor_set(v___x_575_, 0, v___x_486_);
v___x_586_ = v___x_575_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_k_572_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_v_573_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_r_571_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_r_571_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_586_);
lean_ctor_set(v___x_342_, 3, v___x_584_);
lean_ctor_set(v___x_342_, 2, v_v_578_);
lean_ctor_set(v___x_342_, 1, v_k_577_);
lean_ctor_set(v___x_342_, 0, v___x_582_);
v___x_588_ = v___x_342_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_k_577_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_v_578_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
else
{
lean_object* v_r_599_; 
v_r_599_ = lean_ctor_get(v_impl_485_, 4);
lean_inc(v_r_599_);
if (lean_obj_tag(v_r_599_) == 0)
{
lean_object* v_k_600_; lean_object* v_v_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_612_; 
v_k_600_ = lean_ctor_get(v_impl_485_, 1);
v_v_601_ = lean_ctor_get(v_impl_485_, 2);
v_isSharedCheck_612_ = !lean_is_exclusive(v_impl_485_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_613_ = lean_ctor_get(v_impl_485_, 4);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_impl_485_, 3);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_impl_485_, 0);
lean_dec(v_unused_615_);
v___x_603_ = v_impl_485_;
v_isShared_604_ = v_isSharedCheck_612_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_v_601_);
lean_inc(v_k_600_);
lean_dec(v_impl_485_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_612_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(3u);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 4, v_l_570_);
lean_ctor_set(v___x_603_, 2, v_v_338_);
lean_ctor_set(v___x_603_, 1, v_k_337_);
lean_ctor_set(v___x_603_, 0, v___x_486_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_l_570_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_l_570_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_r_599_);
lean_ctor_set(v___x_342_, 3, v___x_607_);
lean_ctor_set(v___x_342_, 2, v_v_601_);
lean_ctor_set(v___x_342_, 1, v_k_600_);
lean_ctor_set(v___x_342_, 0, v___x_605_);
v___x_609_ = v___x_342_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_601_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_r_599_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_unsigned_to_nat(2u);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_impl_485_);
lean_ctor_set(v___x_342_, 3, v_r_599_);
lean_ctor_set(v___x_342_, 0, v___x_616_);
v___x_618_ = v___x_342_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_k_337_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_v_338_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_r_599_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_impl_485_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
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
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_k_333_);
lean_ctor_set(v___x_622_, 2, v_v_334_);
lean_ctor_set(v___x_622_, 3, v_t_335_);
lean_ctor_set(v___x_622_, 4, v_t_335_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(lean_object* v_t_623_, lean_object* v_k_624_){
_start:
{
if (lean_obj_tag(v_t_623_) == 0)
{
lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v_l_627_; lean_object* v_r_628_; uint8_t v___x_629_; 
v_k_625_ = lean_ctor_get(v_t_623_, 1);
v_v_626_ = lean_ctor_get(v_t_623_, 2);
v_l_627_ = lean_ctor_get(v_t_623_, 3);
v_r_628_ = lean_ctor_get(v_t_623_, 4);
v___x_629_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_624_, v_k_625_);
switch(v___x_629_)
{
case 0:
{
v_t_623_ = v_l_627_;
goto _start;
}
case 1:
{
lean_object* v___x_631_; 
lean_inc(v_v_626_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v_v_626_);
return v___x_631_;
}
default: 
{
v_t_623_ = v_r_628_;
goto _start;
}
}
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg___boxed(lean_object* v_t_634_, lean_object* v_k_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(v_t_634_, v_k_635_);
lean_dec(v_k_635_);
lean_dec(v_t_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14(lean_object* v_self_640_, lean_object* v_as_641_, size_t v_i_642_, size_t v_stop_643_, lean_object* v_b_644_, lean_object* v___y_645_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = lean_usize_dec_eq(v_i_642_, v_stop_643_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v_name_649_; lean_object* v_kind_650_; lean_object* v___x_651_; 
v___x_648_ = lean_array_uget_borrowed(v_as_641_, v_i_642_);
v_name_649_ = lean_ctor_get(v___x_648_, 1);
v_kind_650_ = lean_ctor_get(v___x_648_, 2);
v___x_651_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(v_b_644_, v_name_649_);
if (lean_obj_tag(v___x_651_) == 1)
{
lean_object* v_val_652_; lean_object* v_baseName_653_; lean_object* v_kind_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec(v_b_644_);
v_val_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_val_652_);
lean_dec_ref(v___x_651_);
v_baseName_653_ = lean_ctor_get(v_self_640_, 1);
lean_inc(v_baseName_653_);
lean_dec_ref(v_self_640_);
v_kind_654_ = lean_ctor_get(v_val_652_, 2);
lean_inc(v_kind_654_);
lean_dec(v_val_652_);
v___x_655_ = l_Lean_Name_toString(v_baseName_653_, v___x_647_);
v___x_656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__0));
v___x_657_ = lean_string_append(v___x_655_, v___x_656_);
v___x_658_ = 1;
lean_inc(v_name_649_);
v___x_659_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_649_, v___x_658_);
v___x_660_ = lean_string_append(v___x_657_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__1));
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
v___x_663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_654_, v___x_658_);
v___x_664_ = lean_string_append(v___x_662_, v___x_663_);
lean_dec_ref(v___x_663_);
v___x_665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___closed__2));
v___x_666_ = lean_string_append(v___x_664_, v___x_665_);
lean_inc(v_kind_650_);
v___x_667_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_650_, v___x_658_);
v___x_668_ = lean_string_append(v___x_666_, v___x_667_);
lean_dec_ref(v___x_667_);
v___x_669_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_670_ = lean_string_append(v___x_668_, v___x_669_);
v___x_671_ = 3;
v___x_672_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*1, v___x_671_);
v___x_673_ = lean_array_get_size(v___y_645_);
v___x_674_ = lean_array_push(v___y_645_, v___x_672_);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; size_t v___x_677_; size_t v___x_678_; 
lean_dec(v___x_651_);
lean_inc(v___x_648_);
lean_inc(v_name_649_);
v___x_676_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_name_649_, v___x_648_, v_b_644_);
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_add(v_i_642_, v___x_677_);
v_i_642_ = v___x_678_;
v_b_644_ = v___x_676_;
goto _start;
}
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v_self_640_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v_b_644_);
lean_ctor_set(v___x_680_, 1, v___y_645_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14___boxed(lean_object* v_self_681_, lean_object* v_as_682_, lean_object* v_i_683_, lean_object* v_stop_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
size_t v_i_boxed_688_; size_t v_stop_boxed_689_; lean_object* v_res_690_; 
v_i_boxed_688_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_stop_boxed_689_ = lean_unbox_usize(v_stop_684_);
lean_dec(v_stop_684_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14(v_self_681_, v_as_682_, v_i_boxed_688_, v_stop_boxed_689_, v_b_685_, v___y_686_);
lean_dec_ref(v_as_682_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4(lean_object* v_self_694_, size_t v_sz_695_, size_t v_i_696_, lean_object* v_bs_697_, lean_object* v___y_698_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
lean_dec_ref(v_self_694_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_bs_697_);
lean_ctor_set(v___x_701_, 1, v___y_698_);
return v___x_701_;
}
else
{
lean_object* v_v_702_; lean_object* v_pkg_703_; lean_object* v_name_704_; lean_object* v_keyName_705_; uint8_t v___x_706_; 
v_v_702_ = lean_array_uget(v_bs_697_, v_i_696_);
v_pkg_703_ = lean_ctor_get(v_v_702_, 0);
v_name_704_ = lean_ctor_get(v_v_702_, 1);
v_keyName_705_ = lean_ctor_get(v_self_694_, 2);
v___x_706_ = lean_name_eq(v_pkg_703_, v_keyName_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_inc(v_keyName_705_);
lean_inc(v_name_704_);
lean_inc(v_pkg_703_);
lean_dec(v_v_702_);
lean_dec_ref(v_bs_697_);
lean_dec_ref(v_self_694_);
v___x_707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__0));
v___x_708_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_704_, v___x_700_);
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
lean_dec_ref(v___x_708_);
v___x_710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__1));
v___x_711_ = lean_string_append(v___x_709_, v___x_710_);
v___x_712_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_703_, v___x_700_);
v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
lean_dec_ref(v___x_712_);
v___x_714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__2));
v___x_715_ = lean_string_append(v___x_713_, v___x_714_);
v___x_716_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_705_, v___x_700_);
v___x_717_ = lean_string_append(v___x_715_, v___x_716_);
lean_dec_ref(v___x_716_);
v___x_718_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_719_ = lean_string_append(v___x_717_, v___x_718_);
v___x_720_ = 3;
v___x_721_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*1, v___x_720_);
v___x_722_ = lean_array_get_size(v___y_698_);
v___x_723_ = lean_array_push(v___y_698_, v___x_721_);
v___x_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; lean_object* v_bs_x27_726_; size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v_bs_x27_726_ = lean_array_uset(v_bs_697_, v_i_696_, v___x_725_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_696_, v___x_727_);
v___x_729_ = lean_array_uset(v_bs_x27_726_, v_i_696_, v_v_702_);
v_i_696_ = v___x_728_;
v_bs_697_ = v___x_729_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___boxed(lean_object* v_self_731_, lean_object* v_sz_732_, lean_object* v_i_733_, lean_object* v_bs_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
size_t v_sz_boxed_737_; size_t v_i_boxed_738_; lean_object* v_res_739_; 
v_sz_boxed_737_ = lean_unbox_usize(v_sz_732_);
lean_dec(v_sz_732_);
v_i_boxed_738_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4(v_self_731_, v_sz_boxed_737_, v_i_boxed_738_, v_bs_734_, v___y_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9(lean_object* v_env_742_, lean_object* v_opts_743_, lean_object* v_self_744_, size_t v_sz_745_, size_t v_i_746_, lean_object* v_bs_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_a_751_; lean_object* v_a_752_; uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec_ref(v_self_744_);
lean_dec_ref(v_env_742_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_bs_747_);
lean_ctor_set(v___x_755_, 1, v___y_748_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v_v_757_; lean_object* v___x_758_; 
v___x_756_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_757_ = lean_array_uget_borrowed(v_bs_747_, v_i_746_);
lean_inc(v_v_757_);
lean_inc_ref(v_env_742_);
v___x_758_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_742_, v_opts_743_, v___x_756_, v_v_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref(v_bs_747_);
lean_dec_ref(v_self_744_);
lean_dec_ref(v_env_742_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref(v___x_758_);
v___x_760_ = 3;
v___x_761_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_761_, 0, v_a_759_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*1, v___x_760_);
v___x_762_ = lean_array_get_size(v___y_748_);
v___x_763_ = lean_array_push(v___y_748_, v___x_761_);
v_a_751_ = v___x_762_;
v_a_752_ = v___x_763_;
goto v___jp_750_;
}
else
{
lean_object* v_a_764_; lean_object* v_pkg_765_; lean_object* v_fn_766_; lean_object* v_keyName_767_; uint8_t v___x_768_; 
v_a_764_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_764_);
lean_dec_ref(v___x_758_);
v_pkg_765_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_pkg_765_);
v_fn_766_ = lean_ctor_get(v_a_764_, 1);
lean_inc_ref(v_fn_766_);
lean_dec(v_a_764_);
v_keyName_767_ = lean_ctor_get(v_self_744_, 2);
v___x_768_ = lean_name_eq(v_pkg_765_, v_keyName_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
lean_inc(v_keyName_767_);
lean_dec_ref(v_fn_766_);
lean_dec_ref(v_bs_747_);
lean_dec_ref(v_self_744_);
lean_dec_ref(v_env_742_);
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__0));
v___x_770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_765_, v___x_754_);
v___x_771_ = lean_string_append(v___x_769_, v___x_770_);
lean_dec_ref(v___x_770_);
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__1));
v___x_773_ = lean_string_append(v___x_771_, v___x_772_);
v___x_774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_767_, v___x_754_);
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = 3;
v___x_779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_778_);
v___x_780_ = lean_array_get_size(v___y_748_);
v___x_781_ = lean_array_push(v___y_748_, v___x_779_);
v_a_751_ = v___x_780_;
v_a_752_ = v___x_781_;
goto v___jp_750_;
}
else
{
lean_object* v___x_782_; lean_object* v_bs_x27_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
lean_dec(v_pkg_765_);
v___x_782_ = lean_unsigned_to_nat(0u);
v_bs_x27_783_ = lean_array_uset(v_bs_747_, v_i_746_, v___x_782_);
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_746_, v___x_784_);
v___x_786_ = lean_array_uset(v_bs_x27_783_, v_i_746_, v_fn_766_);
v_i_746_ = v___x_785_;
v_bs_747_ = v___x_786_;
goto _start;
}
}
}
v___jp_750_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v_a_751_);
lean_ctor_set(v___x_753_, 1, v_a_752_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___boxed(lean_object* v_env_788_, lean_object* v_opts_789_, lean_object* v_self_790_, lean_object* v_sz_791_, lean_object* v_i_792_, lean_object* v_bs_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
size_t v_sz_boxed_796_; size_t v_i_boxed_797_; lean_object* v_res_798_; 
v_sz_boxed_796_ = lean_unbox_usize(v_sz_791_);
lean_dec(v_sz_791_);
v_i_boxed_797_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9(v_env_788_, v_opts_789_, v_self_790_, v_sz_boxed_796_, v_i_boxed_797_, v_bs_793_, v___y_794_);
lean_dec_ref(v_opts_789_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10(lean_object* v_env_799_, lean_object* v_opts_800_, size_t v_sz_801_, size_t v_i_802_, lean_object* v_bs_803_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v_env_799_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_bs_803_);
return v___x_805_;
}
else
{
lean_object* v___x_806_; lean_object* v_v_807_; lean_object* v___x_808_; 
v___x_806_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34_;
v_v_807_ = lean_array_uget_borrowed(v_bs_803_, v_i_802_);
lean_inc(v_v_807_);
lean_inc_ref(v_env_799_);
v___x_808_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_799_, v_opts_800_, v___x_806_, v_v_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_bs_803_);
lean_dec_ref(v_env_799_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v_bs_x27_819_; size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v_a_817_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_808_);
v___x_818_ = lean_unsigned_to_nat(0u);
v_bs_x27_819_ = lean_array_uset(v_bs_803_, v_i_802_, v___x_818_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_802_, v___x_820_);
v___x_822_ = lean_array_uset(v_bs_x27_819_, v_i_802_, v_a_817_);
v_i_802_ = v___x_821_;
v_bs_803_ = v___x_822_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10___boxed(lean_object* v_env_824_, lean_object* v_opts_825_, lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_bs_828_){
_start:
{
size_t v_sz_boxed_829_; size_t v_i_boxed_830_; lean_object* v_res_831_; 
v_sz_boxed_829_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_830_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10(v_env_824_, v_opts_825_, v_sz_boxed_829_, v_i_boxed_830_, v_bs_828_);
lean_dec_ref(v_opts_825_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(lean_object* v_f_832_, lean_object* v_as_833_, size_t v_i_834_, size_t v_stop_835_, lean_object* v_b_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = lean_usize_dec_eq(v_i_834_, v_stop_835_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_array_uget_borrowed(v_as_833_, v_i_834_);
lean_inc_ref(v_f_832_);
lean_inc(v___x_838_);
v___x_839_ = lean_apply_1(v_f_832_, v___x_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_b_836_);
lean_dec_ref(v_f_832_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_849_; lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; 
v_a_848_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_839_);
v___x_849_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_838_);
v___x_850_ = l_Lake_RBArray_insert___redArg(v___x_849_, v_b_836_, v___x_838_, v_a_848_);
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_834_, v___x_851_);
v_i_834_ = v___x_852_;
v_b_836_ = v___x_850_;
goto _start;
}
}
else
{
lean_object* v___x_854_; 
lean_dec_ref(v_f_832_);
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v_b_836_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg___boxed(lean_object* v_f_855_, lean_object* v_as_856_, lean_object* v_i_857_, lean_object* v_stop_858_, lean_object* v_b_859_){
_start:
{
size_t v_i_boxed_860_; size_t v_stop_boxed_861_; lean_object* v_res_862_; 
v_i_boxed_860_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_858_);
lean_dec(v_stop_858_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_855_, v_as_856_, v_i_boxed_860_, v_stop_boxed_861_, v_b_859_);
lean_dec_ref(v_as_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(lean_object* v_env_863_, lean_object* v_attr_864_, lean_object* v_f_865_){
_start:
{
lean_object* v_entries_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_entries_866_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_864_, v_env_863_);
v___x_867_ = lean_array_get_size(v_entries_866_);
v___x_868_ = l_Lake_RBArray_mkEmpty___redArg(v___x_867_);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_nat_dec_lt(v___x_869_, v___x_867_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec_ref(v_entries_866_);
lean_dec_ref(v_f_865_);
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_868_);
return v___x_871_;
}
else
{
uint8_t v___x_872_; 
v___x_872_ = lean_nat_dec_le(v___x_867_, v___x_867_);
if (v___x_872_ == 0)
{
if (v___x_870_ == 0)
{
lean_object* v___x_873_; 
lean_dec_ref(v_entries_866_);
lean_dec_ref(v_f_865_);
v___x_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_868_);
return v___x_873_;
}
else
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)0ULL);
v___x_875_ = lean_usize_of_nat(v___x_867_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_865_, v_entries_866_, v___x_874_, v___x_875_, v___x_868_);
lean_dec_ref(v_entries_866_);
return v___x_876_;
}
}
else
{
size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; 
v___x_877_ = ((size_t)0ULL);
v___x_878_ = lean_usize_of_nat(v___x_867_);
v___x_879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_865_, v_entries_866_, v___x_877_, v___x_878_, v___x_868_);
lean_dec_ref(v_entries_866_);
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg___boxed(lean_object* v_env_880_, lean_object* v_attr_881_, lean_object* v_f_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(v_env_880_, v_attr_881_, v_f_882_);
lean_dec_ref(v_attr_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_884_, lean_object* v_as_885_, size_t v_i_886_, size_t v_stop_887_, lean_object* v_b_888_, lean_object* v___y_889_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = lean_usize_dec_eq(v_i_886_, v_stop_887_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_array_uget_borrowed(v_as_885_, v_i_886_);
lean_inc_ref(v_f_884_);
lean_inc(v___x_892_);
v___x_893_ = lean_apply_3(v_f_884_, v___x_892_, v___y_889_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_896_; size_t v___x_897_; size_t v___x_898_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
v_a_895_ = lean_ctor_get(v___x_893_, 1);
lean_inc(v_a_895_);
lean_dec_ref(v___x_893_);
lean_inc(v___x_892_);
v___x_896_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_892_, v_a_894_, v_b_888_);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_add(v_i_886_, v___x_897_);
v_i_886_ = v___x_898_;
v_b_888_ = v___x_896_;
v___y_889_ = v_a_895_;
goto _start;
}
else
{
lean_object* v_a_900_; lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_b_888_);
lean_dec_ref(v_f_884_);
v_a_900_ = lean_ctor_get(v___x_893_, 0);
v_a_901_ = lean_ctor_get(v___x_893_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_893_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_inc(v_a_900_);
lean_dec(v___x_893_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
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
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_900_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v___x_909_; 
lean_dec_ref(v_f_884_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_b_888_);
lean_ctor_set(v___x_909_, 1, v___y_889_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_910_, lean_object* v_as_911_, lean_object* v_i_912_, lean_object* v_stop_913_, lean_object* v_b_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
size_t v_i_boxed_917_; size_t v_stop_boxed_918_; lean_object* v_res_919_; 
v_i_boxed_917_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_stop_boxed_918_ = lean_unbox_usize(v_stop_913_);
lean_dec(v_stop_913_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_910_, v_as_911_, v_i_boxed_917_, v_stop_boxed_918_, v_b_914_, v___y_915_);
lean_dec_ref(v_as_911_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(lean_object* v_env_920_, lean_object* v_attr_921_, lean_object* v_f_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_entries_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_entries_925_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_921_, v_env_920_);
v___x_926_ = lean_box(1);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_get_size(v_entries_925_);
v___x_929_ = lean_nat_dec_lt(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v_entries_925_);
lean_dec_ref(v_f_922_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_926_);
lean_ctor_set(v___x_930_, 1, v___y_923_);
return v___x_930_;
}
else
{
uint8_t v___x_931_; 
v___x_931_ = lean_nat_dec_le(v___x_928_, v___x_928_);
if (v___x_931_ == 0)
{
if (v___x_929_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v_entries_925_);
lean_dec_ref(v_f_922_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_926_);
lean_ctor_set(v___x_932_, 1, v___y_923_);
return v___x_932_;
}
else
{
size_t v___x_933_; size_t v___x_934_; lean_object* v___x_935_; 
v___x_933_ = ((size_t)0ULL);
v___x_934_ = lean_usize_of_nat(v___x_928_);
v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_922_, v_entries_925_, v___x_933_, v___x_934_, v___x_926_, v___y_923_);
lean_dec_ref(v_entries_925_);
return v___x_935_;
}
}
else
{
size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; 
v___x_936_ = ((size_t)0ULL);
v___x_937_ = lean_usize_of_nat(v___x_928_);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_922_, v_entries_925_, v___x_936_, v___x_937_, v___x_926_, v___y_923_);
lean_dec_ref(v_entries_925_);
return v___x_938_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_939_, lean_object* v_attr_940_, lean_object* v_f_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(v_env_939_, v_attr_940_, v_f_941_, v___y_942_);
lean_dec_ref(v_attr_940_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(lean_object* v_t_945_, lean_object* v_k_946_){
_start:
{
if (lean_obj_tag(v_t_945_) == 0)
{
lean_object* v_k_947_; lean_object* v_v_948_; lean_object* v_l_949_; lean_object* v_r_950_; uint8_t v___x_951_; 
v_k_947_ = lean_ctor_get(v_t_945_, 1);
v_v_948_ = lean_ctor_get(v_t_945_, 2);
v_l_949_ = lean_ctor_get(v_t_945_, 3);
v_r_950_ = lean_ctor_get(v_t_945_, 4);
v___x_951_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_946_, v_k_947_);
switch(v___x_951_)
{
case 0:
{
v_t_945_ = v_l_949_;
goto _start;
}
case 1:
{
lean_object* v___x_953_; 
lean_inc(v_v_948_);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v_v_948_);
return v___x_953_;
}
default: 
{
v_t_945_ = v_r_950_;
goto _start;
}
}
}
else
{
lean_object* v___x_955_; 
v___x_955_ = lean_box(0);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_956_, lean_object* v_k_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_t_956_, v_k_957_);
lean_dec(v_k_957_);
lean_dec(v_t_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8(lean_object* v_a_961_, lean_object* v_self_962_, size_t v_sz_963_, size_t v_i_964_, lean_object* v_bs_965_, lean_object* v___y_966_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = lean_usize_dec_lt(v_i_964_, v_sz_963_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
lean_dec_ref(v_self_962_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_bs_965_);
lean_ctor_set(v___x_969_, 1, v___y_966_);
return v___x_969_;
}
else
{
lean_object* v_v_970_; lean_object* v___x_971_; 
v_v_970_ = lean_array_uget_borrowed(v_bs_965_, v_i_964_);
v___x_971_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_a_961_, v_v_970_);
if (lean_obj_tag(v___x_971_) == 1)
{
lean_object* v_val_972_; lean_object* v___x_973_; lean_object* v_bs_x27_974_; size_t v___x_975_; size_t v___x_976_; lean_object* v___x_977_; 
v_val_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_val_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = lean_unsigned_to_nat(0u);
v_bs_x27_974_ = lean_array_uset(v_bs_965_, v_i_964_, v___x_973_);
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_add(v_i_964_, v___x_975_);
v___x_977_ = lean_array_uset(v_bs_x27_974_, v_i_964_, v_val_972_);
v_i_964_ = v___x_976_;
v_bs_965_ = v___x_977_;
goto _start;
}
else
{
lean_object* v_baseName_979_; uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_inc(v_v_970_);
lean_dec(v___x_971_);
lean_dec_ref(v_bs_965_);
v_baseName_979_ = lean_ctor_get(v_self_962_, 1);
lean_inc(v_baseName_979_);
lean_dec_ref(v_self_962_);
v___x_980_ = 0;
v___x_981_ = l_Lean_Name_toString(v_baseName_979_, v___x_980_);
v___x_982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__0));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_970_, v___x_968_);
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__1));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
v___x_988_ = 3;
v___x_989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_988_);
v___x_990_ = lean_array_get_size(v___y_966_);
v___x_991_ = lean_array_push(v___y_966_, v___x_989_);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___boxed(lean_object* v_a_993_, lean_object* v_self_994_, lean_object* v_sz_995_, lean_object* v_i_996_, lean_object* v_bs_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
size_t v_sz_boxed_1000_; size_t v_i_boxed_1001_; lean_object* v_res_1002_; 
v_sz_boxed_1000_ = lean_unbox_usize(v_sz_995_);
lean_dec(v_sz_995_);
v_i_boxed_1001_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8(v_a_993_, v_self_994_, v_sz_boxed_1000_, v_i_boxed_1001_, v_bs_997_, v___y_998_);
lean_dec(v_a_993_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11(lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_self_1007_, size_t v_sz_1008_, size_t v_i_1009_, lean_object* v_bs_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_lt(v_i_1009_, v_sz_1008_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec_ref(v_self_1007_);
lean_dec_ref(v_a_1005_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_bs_1010_);
lean_ctor_set(v___x_1014_, 1, v___y_1011_);
return v___x_1014_;
}
else
{
lean_object* v_toTreeMap_1015_; lean_object* v_v_1016_; lean_object* v___x_1017_; lean_object* v_bs_x27_1018_; lean_object* v_a_1020_; lean_object* v_a_1021_; lean_object* v___x_1026_; 
v_toTreeMap_1015_ = lean_ctor_get(v_a_1005_, 0);
v_v_1016_ = lean_array_uget(v_bs_1010_, v_i_1009_);
v___x_1017_ = lean_unsigned_to_nat(0u);
v_bs_x27_1018_ = lean_array_uset(v_bs_1010_, v_i_1009_, v___x_1017_);
v___x_1026_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_toTreeMap_1015_, v_v_1016_);
if (lean_obj_tag(v___x_1026_) == 1)
{
lean_object* v_val_1027_; lean_object* v_name_1028_; 
lean_dec(v_v_1016_);
v_val_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1027_);
lean_dec_ref(v___x_1026_);
v_name_1028_ = lean_ctor_get(v_val_1027_, 1);
lean_inc(v_name_1028_);
lean_dec(v_val_1027_);
v_a_1020_ = v_name_1028_;
v_a_1021_ = v___y_1011_;
goto v___jp_1019_;
}
else
{
uint8_t v___x_1029_; 
lean_dec(v___x_1026_);
v___x_1029_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_1016_, v_a_1006_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1048_; 
lean_dec_ref(v_bs_x27_1018_);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_a_1005_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; lean_object* v_unused_1050_; 
v_unused_1049_ = lean_ctor_get(v_a_1005_, 1);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_a_1005_, 0);
lean_dec(v_unused_1050_);
v___x_1031_ = v_a_1005_;
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v_a_1005_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1048_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_baseName_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v_baseName_1033_ = lean_ctor_get(v_self_1007_, 1);
lean_inc(v_baseName_1033_);
lean_dec_ref(v_self_1007_);
v___x_1034_ = l_Lean_Name_toString(v_baseName_1033_, v___x_1029_);
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__0));
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
v___x_1037_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1016_, v___x_1013_);
v___x_1038_ = lean_string_append(v___x_1036_, v___x_1037_);
lean_dec_ref(v___x_1037_);
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__1));
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
v___x_1041_ = 3;
v___x_1042_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*1, v___x_1041_);
v___x_1043_ = lean_array_get_size(v___y_1011_);
v___x_1044_ = lean_array_push(v___y_1011_, v___x_1042_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 1);
lean_ctor_set(v___x_1031_, 1, v___x_1044_);
lean_ctor_set(v___x_1031_, 0, v___x_1043_);
v___x_1046_ = v___x_1031_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
v_a_1020_ = v_v_1016_;
v_a_1021_ = v___y_1011_;
goto v___jp_1019_;
}
}
v___jp_1019_:
{
size_t v___x_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1009_, v___x_1022_);
v___x_1024_ = lean_array_uset(v_bs_x27_1018_, v_i_1009_, v_a_1020_);
v_i_1009_ = v___x_1023_;
v_bs_1010_ = v___x_1024_;
v___y_1011_ = v_a_1021_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___boxed(lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_self_1053_, lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_bs_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
size_t v_sz_boxed_1059_; size_t v_i_boxed_1060_; lean_object* v_res_1061_; 
v_sz_boxed_1059_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1060_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11(v_a_1051_, v_a_1052_, v_self_1053_, v_sz_boxed_1059_, v_i_boxed_1060_, v_bs_1056_, v___y_1057_);
lean_dec(v_a_1052_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6(lean_object* v_a_1063_, lean_object* v_self_1064_, size_t v_sz_1065_, size_t v_i_1066_, lean_object* v_bs_1067_, lean_object* v___y_1068_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_lt(v_i_1066_, v_sz_1065_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec_ref(v_self_1064_);
lean_dec_ref(v_a_1063_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_bs_1067_);
lean_ctor_set(v___x_1071_, 1, v___y_1068_);
return v___x_1071_;
}
else
{
lean_object* v_toTreeMap_1072_; lean_object* v_v_1073_; lean_object* v___x_1074_; 
v_toTreeMap_1072_ = lean_ctor_get(v_a_1063_, 0);
v_v_1073_ = lean_array_uget_borrowed(v_bs_1067_, v_i_1066_);
v___x_1074_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_toTreeMap_1072_, v_v_1073_);
if (lean_obj_tag(v___x_1074_) == 1)
{
lean_object* v_val_1075_; lean_object* v_name_1076_; lean_object* v___x_1077_; lean_object* v_bs_x27_1078_; size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v_val_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_val_1075_);
lean_dec_ref(v___x_1074_);
v_name_1076_ = lean_ctor_get(v_val_1075_, 1);
lean_inc(v_name_1076_);
lean_dec(v_val_1075_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v_bs_x27_1078_ = lean_array_uset(v_bs_1067_, v_i_1066_, v___x_1077_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_add(v_i_1066_, v___x_1079_);
v___x_1081_ = lean_array_uset(v_bs_x27_1078_, v_i_1066_, v_name_1076_);
v_i_1066_ = v___x_1080_;
v_bs_1067_ = v___x_1081_;
goto _start;
}
else
{
lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1102_; 
lean_inc(v_v_1073_);
lean_dec(v___x_1074_);
lean_dec_ref(v_bs_1067_);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_a_1063_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; 
v_unused_1103_ = lean_ctor_get(v_a_1063_, 1);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_a_1063_, 0);
lean_dec(v_unused_1104_);
v___x_1084_ = v_a_1063_;
v_isShared_1085_ = v_isSharedCheck_1102_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v_a_1063_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1102_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_baseName_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v_baseName_1086_ = lean_ctor_get(v_self_1064_, 1);
lean_inc(v_baseName_1086_);
lean_dec_ref(v_self_1064_);
v___x_1087_ = 0;
v___x_1088_ = l_Lean_Name_toString(v_baseName_1086_, v___x_1087_);
v___x_1089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___closed__0));
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
v___x_1091_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1073_, v___x_1070_);
v___x_1092_ = lean_string_append(v___x_1090_, v___x_1091_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__1));
v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
v___x_1095_ = 3;
v___x_1096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*1, v___x_1095_);
v___x_1097_ = lean_array_get_size(v___y_1068_);
v___x_1098_ = lean_array_push(v___y_1068_, v___x_1096_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 1);
lean_ctor_set(v___x_1084_, 1, v___x_1098_);
lean_ctor_set(v___x_1084_, 0, v___x_1097_);
v___x_1100_ = v___x_1084_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___boxed(lean_object* v_a_1105_, lean_object* v_self_1106_, lean_object* v_sz_1107_, lean_object* v_i_1108_, lean_object* v_bs_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
size_t v_sz_boxed_1112_; size_t v_i_boxed_1113_; lean_object* v_res_1114_; 
v_sz_boxed_1112_ = lean_unbox_usize(v_sz_1107_);
lean_dec(v_sz_1107_);
v_i_boxed_1113_ = lean_unbox_usize(v_i_1108_);
lean_dec(v_i_1108_);
v_res_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6(v_a_1105_, v_self_1106_, v_sz_boxed_1112_, v_i_boxed_1113_, v_bs_1109_, v___y_1110_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12(lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_self_1118_, size_t v_sz_1119_, size_t v_i_1120_, lean_object* v_bs_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_usize_dec_lt(v_i_1120_, v_sz_1119_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_self_1118_);
lean_dec_ref(v_a_1116_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_bs_1121_);
lean_ctor_set(v___x_1125_, 1, v___y_1122_);
return v___x_1125_;
}
else
{
lean_object* v_toTreeMap_1126_; lean_object* v_v_1127_; lean_object* v___x_1128_; lean_object* v_bs_x27_1129_; lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1137_; 
v_toTreeMap_1126_ = lean_ctor_get(v_a_1116_, 0);
v_v_1127_ = lean_array_uget(v_bs_1121_, v_i_1120_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v_bs_x27_1129_ = lean_array_uset(v_bs_1121_, v_i_1120_, v___x_1128_);
v___x_1137_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_toTreeMap_1126_, v_v_1127_);
if (lean_obj_tag(v___x_1137_) == 1)
{
lean_object* v_val_1138_; lean_object* v_name_1139_; 
lean_dec(v_v_1127_);
v_val_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v___x_1137_);
v_name_1139_ = lean_ctor_get(v_val_1138_, 1);
lean_inc(v_name_1139_);
lean_dec(v_val_1138_);
v_a_1131_ = v_name_1139_;
v_a_1132_ = v___y_1122_;
goto v___jp_1130_;
}
else
{
uint8_t v___x_1140_; 
lean_dec(v___x_1137_);
v___x_1140_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_1127_, v_a_1117_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_bs_x27_1129_);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_a_1116_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; lean_object* v_unused_1161_; 
v_unused_1160_ = lean_ctor_get(v_a_1116_, 1);
lean_dec(v_unused_1160_);
v_unused_1161_ = lean_ctor_get(v_a_1116_, 0);
lean_dec(v_unused_1161_);
v___x_1142_ = v_a_1116_;
v_isShared_1143_ = v_isSharedCheck_1159_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_a_1116_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1159_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_baseName_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v_baseName_1144_ = lean_ctor_get(v_self_1118_, 1);
lean_inc(v_baseName_1144_);
lean_dec_ref(v_self_1118_);
v___x_1145_ = l_Lean_Name_toString(v_baseName_1144_, v___x_1140_);
v___x_1146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__0));
v___x_1147_ = lean_string_append(v___x_1145_, v___x_1146_);
v___x_1148_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_1127_, v___x_1124_);
v___x_1149_ = lean_string_append(v___x_1147_, v___x_1148_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___closed__0));
v___x_1151_ = lean_string_append(v___x_1149_, v___x_1150_);
v___x_1152_ = 3;
v___x_1153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*1, v___x_1152_);
v___x_1154_ = lean_array_get_size(v___y_1122_);
v___x_1155_ = lean_array_push(v___y_1122_, v___x_1153_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 1);
lean_ctor_set(v___x_1142_, 1, v___x_1155_);
lean_ctor_set(v___x_1142_, 0, v___x_1154_);
v___x_1157_ = v___x_1142_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
v_a_1131_ = v_v_1127_;
v_a_1132_ = v___y_1122_;
goto v___jp_1130_;
}
}
v___jp_1130_:
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_add(v_i_1120_, v___x_1133_);
v___x_1135_ = lean_array_uset(v_bs_x27_1129_, v_i_1120_, v_a_1131_);
v_i_1120_ = v___x_1134_;
v_bs_1121_ = v___x_1135_;
v___y_1122_ = v_a_1132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___boxed(lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_self_1164_, lean_object* v_sz_1165_, lean_object* v_i_1166_, lean_object* v_bs_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_sz_boxed_1170_; size_t v_i_boxed_1171_; lean_object* v_res_1172_; 
v_sz_boxed_1170_ = lean_unbox_usize(v_sz_1165_);
lean_dec(v_sz_1165_);
v_i_boxed_1171_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12(v_a_1162_, v_a_1163_, v_self_1164_, v_sz_boxed_1170_, v_i_boxed_1171_, v_bs_1167_, v___y_1168_);
lean_dec(v_a_1163_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(lean_object* v_self_1176_, lean_object* v_as_1177_, size_t v_i_1178_, size_t v_stop_1179_, lean_object* v_b_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_a_1184_; lean_object* v_a_1185_; uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_eq(v_i_1178_, v_stop_1179_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v_name_1191_; lean_object* v_kind_1192_; lean_object* v_config_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1190_ = lean_array_uget_borrowed(v_as_1177_, v_i_1178_);
v_name_1191_ = lean_ctor_get(v___x_1190_, 1);
v_kind_1192_ = lean_ctor_get(v___x_1190_, 2);
v_config_1193_ = lean_ctor_get(v___x_1190_, 3);
v___x_1194_ = l_Lake_LeanExe_keyword;
v___x_1195_ = lean_name_eq(v_kind_1192_, v___x_1194_);
if (v___x_1195_ == 0)
{
v_a_1184_ = v_b_1180_;
v_a_1185_ = v___y_1181_;
goto v___jp_1183_;
}
else
{
lean_object* v_root_1196_; lean_object* v___x_1197_; 
v_root_1196_ = lean_ctor_get(v_config_1193_, 2);
v___x_1197_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_b_1180_, v_root_1196_);
if (lean_obj_tag(v___x_1197_) == 1)
{
lean_object* v_val_1198_; lean_object* v_baseName_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_b_1180_);
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref(v___x_1197_);
v_baseName_1199_ = lean_ctor_get(v_self_1176_, 1);
lean_inc(v_baseName_1199_);
lean_dec_ref(v_self_1176_);
v___x_1200_ = l_Lean_Name_toString(v_baseName_1199_, v___x_1189_);
v___x_1201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0));
v___x_1202_ = lean_string_append(v___x_1200_, v___x_1201_);
lean_inc(v_name_1191_);
v___x_1203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1191_, v___x_1195_);
v___x_1204_ = lean_string_append(v___x_1202_, v___x_1203_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1));
v___x_1206_ = lean_string_append(v___x_1204_, v___x_1205_);
lean_inc(v_root_1196_);
v___x_1207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_root_1196_, v___x_1195_);
v___x_1208_ = lean_string_append(v___x_1206_, v___x_1207_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2));
v___x_1210_ = lean_string_append(v___x_1208_, v___x_1209_);
v___x_1211_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1198_, v___x_1195_);
v___x_1212_ = lean_string_append(v___x_1210_, v___x_1211_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1214_ = lean_string_append(v___x_1212_, v___x_1213_);
v___x_1215_ = 3;
v___x_1216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*1, v___x_1215_);
v___x_1217_ = lean_array_get_size(v___y_1181_);
v___x_1218_ = lean_array_push(v___y_1181_, v___x_1216_);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; 
lean_dec(v___x_1197_);
lean_inc(v_name_1191_);
lean_inc(v_root_1196_);
v___x_1220_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_root_1196_, v_name_1191_, v_b_1180_);
v_a_1184_ = v___x_1220_;
v_a_1185_ = v___y_1181_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v___x_1221_; 
lean_dec_ref(v_self_1176_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_b_1180_);
lean_ctor_set(v___x_1221_, 1, v___y_1181_);
return v___x_1221_;
}
v___jp_1183_:
{
size_t v___x_1186_; size_t v___x_1187_; 
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1178_, v___x_1186_);
v_i_1178_ = v___x_1187_;
v_b_1180_ = v_a_1184_;
v___y_1181_ = v_a_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___boxed(lean_object* v_self_1222_, lean_object* v_as_1223_, lean_object* v_i_1224_, lean_object* v_stop_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
size_t v_i_boxed_1229_; size_t v_stop_boxed_1230_; lean_object* v_res_1231_; 
v_i_boxed_1229_ = lean_unbox_usize(v_i_1224_);
lean_dec(v_i_1224_);
v_stop_boxed_1230_ = lean_unbox_usize(v_stop_1225_);
lean_dec(v_stop_1225_);
v_res_1231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(v_self_1222_, v_as_1223_, v_i_boxed_1229_, v_stop_boxed_1230_, v_b_1226_, v___y_1227_);
lean_dec_ref(v_as_1223_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv(lean_object* v_self_1236_, lean_object* v_env_1237_, lean_object* v_opts_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1241_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1238_);
lean_inc_ref_n(v_env_1237_, 2);
v___f_1242_ = lean_alloc_closure((void*)(l_Lake_Package_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1242_, 0, v_env_1237_);
lean_closure_set(v___f_1242_, 1, v_opts_1238_);
lean_closure_set(v___f_1242_, 2, v___x_1241_);
v___x_1243_ = l_Lake_targetAttr;
v___x_1244_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(v_env_1237_, v___x_1243_, v___f_1242_);
v___x_1245_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(v___x_1244_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_toArray_1247_; size_t v_sz_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v_toArray_1247_ = lean_ctor_get(v_a_1246_, 1);
v_sz_1248_ = lean_array_size(v_toArray_1247_);
v___x_1249_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1247_);
lean_inc_ref(v_self_1236_);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4(v_self_1236_, v_sz_1248_, v___x_1249_, v_toArray_1247_, v_a_1239_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1541_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_a_1252_ = lean_ctor_get(v___x_1250_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1254_ = v___x_1250_;
v_isShared_1255_ = v_isSharedCheck_1541_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1541_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v_lintDriver_1264_; lean_object* v___y_1265_; lean_object* v___x_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v_testDriver_1309_; lean_object* v___y_1310_; lean_object* v___y_1366_; lean_object* v_a_1367_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___x_1512_; lean_object* v_a_1514_; lean_object* v_a_1515_; lean_object* v___y_1523_; uint8_t v___x_1535_; 
v___x_1298_ = l_Lake_instTypeNameScriptFn_unsafe__1;
lean_inc_ref(v_self_1236_);
lean_inc_ref(v_opts_1238_);
lean_inc_ref(v_env_1237_);
v___f_1299_ = lean_alloc_closure((void*)(l_Lake_Package_loadFromEnv___lam__1___boxed), 7, 4);
lean_closure_set(v___f_1299_, 0, v_env_1237_);
lean_closure_set(v___f_1299_, 1, v_opts_1238_);
lean_closure_set(v___f_1299_, 2, v___x_1298_);
lean_closure_set(v___f_1299_, 3, v_self_1236_);
v___x_1300_ = lean_box(1);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1512_ = lean_array_get_size(v_a_1251_);
v___x_1535_ = lean_nat_dec_lt(v___x_1301_, v___x_1512_);
if (v___x_1535_ == 0)
{
v_a_1514_ = v___x_1300_;
v_a_1515_ = v_a_1252_;
goto v___jp_1513_;
}
else
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
if (v___x_1536_ == 0)
{
if (v___x_1535_ == 0)
{
v_a_1514_ = v___x_1300_;
v_a_1515_ = v_a_1252_;
goto v___jp_1513_;
}
else
{
size_t v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_usize_of_nat(v___x_1512_);
lean_inc_ref(v_self_1236_);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14(v_self_1236_, v_a_1251_, v___x_1249_, v___x_1537_, v___x_1300_, v_a_1252_);
v___y_1523_ = v___x_1538_;
goto v___jp_1522_;
}
}
else
{
size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_usize_of_nat(v___x_1512_);
lean_inc_ref(v_self_1236_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__14(v_self_1236_, v_a_1251_, v___x_1249_, v___x_1539_, v___x_1300_, v_a_1252_);
v___y_1523_ = v___x_1540_;
goto v___jp_1522_;
}
}
v___jp_1256_:
{
lean_object* v_wsIdx_1266_; lean_object* v_baseName_1267_; lean_object* v_keyName_1268_; lean_object* v_origName_1269_; lean_object* v_dir_1270_; lean_object* v_relDir_1271_; lean_object* v_config_1272_; lean_object* v_configFile_1273_; lean_object* v_relConfigFile_1274_; lean_object* v_relManifestFile_1275_; lean_object* v_scope_1276_; lean_object* v_remoteUrl_1277_; lean_object* v_buildArchive_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1288_; 
v_wsIdx_1266_ = lean_ctor_get(v_self_1236_, 0);
v_baseName_1267_ = lean_ctor_get(v_self_1236_, 1);
v_keyName_1268_ = lean_ctor_get(v_self_1236_, 2);
v_origName_1269_ = lean_ctor_get(v_self_1236_, 3);
v_dir_1270_ = lean_ctor_get(v_self_1236_, 4);
v_relDir_1271_ = lean_ctor_get(v_self_1236_, 5);
v_config_1272_ = lean_ctor_get(v_self_1236_, 6);
v_configFile_1273_ = lean_ctor_get(v_self_1236_, 7);
v_relConfigFile_1274_ = lean_ctor_get(v_self_1236_, 8);
v_relManifestFile_1275_ = lean_ctor_get(v_self_1236_, 9);
v_scope_1276_ = lean_ctor_get(v_self_1236_, 10);
v_remoteUrl_1277_ = lean_ctor_get(v_self_1236_, 11);
v_buildArchive_1278_ = lean_ctor_get(v_self_1236_, 19);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_self_1236_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; lean_object* v_unused_1290_; lean_object* v_unused_1291_; lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1289_ = lean_ctor_get(v_self_1236_, 21);
lean_dec(v_unused_1289_);
v_unused_1290_ = lean_ctor_get(v_self_1236_, 20);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v_self_1236_, 18);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v_self_1236_, 17);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_self_1236_, 16);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_self_1236_, 15);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_self_1236_, 14);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v_self_1236_, 13);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_self_1236_, 12);
lean_dec(v_unused_1297_);
v___x_1280_ = v_self_1236_;
v_isShared_1281_ = v_isSharedCheck_1288_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_buildArchive_1278_);
lean_inc(v_remoteUrl_1277_);
lean_inc(v_scope_1276_);
lean_inc(v_relManifestFile_1275_);
lean_inc(v_relConfigFile_1274_);
lean_inc(v_configFile_1273_);
lean_inc(v_config_1272_);
lean_inc(v_relDir_1271_);
lean_inc(v_dir_1270_);
lean_inc(v_origName_1269_);
lean_inc(v_keyName_1268_);
lean_inc(v_baseName_1267_);
lean_inc(v_wsIdx_1266_);
lean_dec(v_self_1236_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1288_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 21, v_lintDriver_1264_);
lean_ctor_set(v___x_1280_, 20, v___y_1263_);
lean_ctor_set(v___x_1280_, 18, v___y_1258_);
lean_ctor_set(v___x_1280_, 17, v___y_1260_);
lean_ctor_set(v___x_1280_, 16, v___y_1257_);
lean_ctor_set(v___x_1280_, 15, v___y_1261_);
lean_ctor_set(v___x_1280_, 14, v___y_1259_);
lean_ctor_set(v___x_1280_, 13, v_a_1251_);
lean_ctor_set(v___x_1280_, 12, v___y_1262_);
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_wsIdx_1266_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_baseName_1267_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_keyName_1268_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_origName_1269_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_dir_1270_);
lean_ctor_set(v_reuseFailAlloc_1287_, 5, v_relDir_1271_);
lean_ctor_set(v_reuseFailAlloc_1287_, 6, v_config_1272_);
lean_ctor_set(v_reuseFailAlloc_1287_, 7, v_configFile_1273_);
lean_ctor_set(v_reuseFailAlloc_1287_, 8, v_relConfigFile_1274_);
lean_ctor_set(v_reuseFailAlloc_1287_, 9, v_relManifestFile_1275_);
lean_ctor_set(v_reuseFailAlloc_1287_, 10, v_scope_1276_);
lean_ctor_set(v_reuseFailAlloc_1287_, 11, v_remoteUrl_1277_);
lean_ctor_set(v_reuseFailAlloc_1287_, 12, v___y_1262_);
lean_ctor_set(v_reuseFailAlloc_1287_, 13, v_a_1251_);
lean_ctor_set(v_reuseFailAlloc_1287_, 14, v___y_1259_);
lean_ctor_set(v_reuseFailAlloc_1287_, 15, v___y_1261_);
lean_ctor_set(v_reuseFailAlloc_1287_, 16, v___y_1257_);
lean_ctor_set(v_reuseFailAlloc_1287_, 17, v___y_1260_);
lean_ctor_set(v_reuseFailAlloc_1287_, 18, v___y_1258_);
lean_ctor_set(v_reuseFailAlloc_1287_, 19, v_buildArchive_1278_);
lean_ctor_set(v_reuseFailAlloc_1287_, 20, v___y_1263_);
lean_ctor_set(v_reuseFailAlloc_1287_, 21, v_lintDriver_1264_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___y_1265_);
lean_ctor_set(v___x_1254_, 0, v___x_1283_);
v___x_1285_ = v___x_1254_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___y_1265_);
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
v___jp_1302_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; size_t v_sz_1313_; lean_object* v___x_1314_; 
v___x_1311_ = l_Lake_lintDriverAttr;
v___x_1312_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1311_, v_env_1237_);
v_sz_1313_ = lean_array_size(v___x_1312_);
lean_inc_ref(v_self_1236_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11(v_a_1246_, v___y_1303_, v_self_1236_, v_sz_1313_, v___x_1249_, v___x_1312_, v___y_1310_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1355_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_a_1316_ = lean_ctor_get(v___x_1314_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1318_ = v___x_1314_;
v_isShared_1319_ = v_isSharedCheck_1355_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1355_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_unsigned_to_nat(1u);
v___x_1321_ = lean_array_get_size(v_a_1315_);
v___x_1322_ = lean_nat_dec_lt(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_nat_dec_lt(v___x_1301_, v___x_1321_);
if (v___x_1323_ == 0)
{
lean_object* v_config_1324_; lean_object* v_lintDriver_1325_; 
lean_del_object(v___x_1318_);
lean_dec(v_a_1315_);
v_config_1324_ = lean_ctor_get(v_self_1236_, 6);
v_lintDriver_1325_ = lean_ctor_get(v_config_1324_, 14);
lean_inc_ref(v_lintDriver_1325_);
v___y_1257_ = v___y_1303_;
v___y_1258_ = v___y_1305_;
v___y_1259_ = v___y_1304_;
v___y_1260_ = v___y_1308_;
v___y_1261_ = v___y_1307_;
v___y_1262_ = v___y_1306_;
v___y_1263_ = v_testDriver_1309_;
v_lintDriver_1264_ = v_lintDriver_1325_;
v___y_1265_ = v_a_1316_;
goto v___jp_1256_;
}
else
{
lean_object* v_config_1326_; lean_object* v_baseName_1327_; lean_object* v_lintDriver_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_config_1326_ = lean_ctor_get(v_self_1236_, 6);
v_baseName_1327_ = lean_ctor_get(v_self_1236_, 1);
v_lintDriver_1328_ = lean_ctor_get(v_config_1326_, 14);
v___x_1329_ = lean_string_utf8_byte_size(v_lintDriver_1328_);
v___x_1330_ = lean_nat_dec_eq(v___x_1329_, v___x_1301_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_inc(v_baseName_1327_);
lean_dec(v_a_1315_);
lean_dec_ref(v_testDriver_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec_ref(v_self_1236_);
v___x_1331_ = l_Lean_Name_toString(v_baseName_1327_, v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__0));
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
v___x_1334_ = 3;
v___x_1335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*1, v___x_1334_);
v___x_1336_ = lean_array_get_size(v_a_1316_);
v___x_1337_ = lean_array_push(v_a_1316_, v___x_1335_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 1);
lean_ctor_set(v___x_1318_, 1, v___x_1337_);
lean_ctor_set(v___x_1318_, 0, v___x_1336_);
v___x_1339_ = v___x_1318_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_del_object(v___x_1318_);
v___x_1341_ = lean_array_fget(v_a_1315_, v___x_1301_);
lean_dec(v_a_1315_);
v___x_1342_ = l_Lean_Name_toString(v___x_1341_, v___x_1330_);
v___y_1257_ = v___y_1303_;
v___y_1258_ = v___y_1305_;
v___y_1259_ = v___y_1304_;
v___y_1260_ = v___y_1308_;
v___y_1261_ = v___y_1307_;
v___y_1262_ = v___y_1306_;
v___y_1263_ = v_testDriver_1309_;
v_lintDriver_1264_ = v___x_1342_;
v___y_1265_ = v_a_1316_;
goto v___jp_1256_;
}
}
}
else
{
lean_object* v_baseName_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec(v_a_1315_);
lean_dec_ref(v_testDriver_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
v_baseName_1343_ = lean_ctor_get(v_self_1236_, 1);
lean_inc(v_baseName_1343_);
lean_dec_ref(v_self_1236_);
v___x_1344_ = 0;
v___x_1345_ = l_Lean_Name_toString(v_baseName_1343_, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__1));
v___x_1347_ = lean_string_append(v___x_1345_, v___x_1346_);
v___x_1348_ = 3;
v___x_1349_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1, v___x_1348_);
v___x_1350_ = lean_array_get_size(v_a_1316_);
v___x_1351_ = lean_array_push(v_a_1316_, v___x_1349_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 1);
lean_ctor_set(v___x_1318_, 1, v___x_1351_);
lean_ctor_set(v___x_1318_, 0, v___x_1350_);
v___x_1353_ = v___x_1318_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_testDriver_1309_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec_ref(v_self_1236_);
v_a_1356_ = lean_ctor_get(v___x_1314_, 0);
v_a_1357_ = lean_ctor_get(v___x_1314_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1314_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_inc(v_a_1356_);
lean_dec(v___x_1314_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1356_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; size_t v_sz_1370_; lean_object* v___x_1371_; 
v___x_1368_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1237_);
v___x_1369_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1368_, v_env_1237_);
v_sz_1370_ = lean_array_size(v___x_1369_);
lean_inc_ref(v_self_1236_);
lean_inc(v_a_1246_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6(v_a_1246_, v_self_1236_, v_sz_1370_, v___x_1249_, v___x_1369_, v_a_1367_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
v_a_1373_ = lean_ctor_get(v___x_1371_, 1);
lean_inc(v_a_1373_);
lean_dec_ref(v___x_1371_);
v___x_1374_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1237_);
v___x_1375_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(v_env_1237_, v___x_1374_, v___f_1299_, v_a_1373_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; size_t v_sz_1380_; lean_object* v___x_1381_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
v_a_1377_ = lean_ctor_get(v___x_1375_, 1);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1375_);
v___x_1378_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1237_);
v___x_1379_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1378_, v_env_1237_);
v_sz_1380_ = lean_array_size(v___x_1379_);
lean_inc_ref(v_self_1236_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8(v_a_1376_, v_self_1236_, v_sz_1380_, v___x_1249_, v___x_1379_, v_a_1377_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; size_t v_sz_1386_; lean_object* v___x_1387_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
v_a_1383_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1381_);
v___x_1384_ = l_Lake_postUpdateAttr;
lean_inc_ref_n(v_env_1237_, 2);
v___x_1385_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1384_, v_env_1237_);
v_sz_1386_ = lean_array_size(v___x_1385_);
lean_inc_ref(v_self_1236_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9(v_env_1237_, v_opts_1238_, v_self_1236_, v_sz_1386_, v___x_1249_, v___x_1385_, v_a_1383_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1462_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_a_1389_ = lean_ctor_get(v___x_1387_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1391_ = v___x_1387_;
v_isShared_1392_ = v_isSharedCheck_1462_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1462_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; size_t v_sz_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1393_ = l_Lake_packageDepAttr;
lean_inc_ref_n(v_env_1237_, 2);
v___x_1394_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1393_, v_env_1237_);
v_sz_1395_ = lean_array_size(v___x_1394_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10(v_env_1237_, v_opts_1238_, v_sz_1395_, v___x_1249_, v___x_1394_);
lean_dec_ref(v_opts_1238_);
v___x_1397_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(v___x_1396_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; size_t v_sz_1401_; lean_object* v___x_1402_; 
lean_del_object(v___x_1391_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref(v___x_1397_);
v___x_1399_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1237_);
v___x_1400_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1399_, v_env_1237_);
v_sz_1401_ = lean_array_size(v___x_1400_);
lean_inc_ref(v_self_1236_);
lean_inc(v_a_1246_);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12(v_a_1246_, v_a_1376_, v_self_1236_, v_sz_1401_, v___x_1249_, v___x_1400_, v_a_1389_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1443_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_a_1404_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1406_ = v___x_1402_;
v_isShared_1407_ = v_isSharedCheck_1443_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1443_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_array_get_size(v_a_1403_);
v___x_1410_ = lean_nat_dec_lt(v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_nat_dec_lt(v___x_1301_, v___x_1409_);
if (v___x_1411_ == 0)
{
lean_object* v_config_1412_; lean_object* v_testDriver_1413_; 
lean_del_object(v___x_1406_);
lean_dec(v_a_1403_);
v_config_1412_ = lean_ctor_get(v_self_1236_, 6);
v_testDriver_1413_ = lean_ctor_get(v_config_1412_, 12);
lean_inc_ref(v_testDriver_1413_);
v___y_1303_ = v_a_1376_;
v___y_1304_ = v___y_1366_;
v___y_1305_ = v_a_1388_;
v___y_1306_ = v_a_1398_;
v___y_1307_ = v_a_1372_;
v___y_1308_ = v_a_1382_;
v_testDriver_1309_ = v_testDriver_1413_;
v___y_1310_ = v_a_1404_;
goto v___jp_1302_;
}
else
{
lean_object* v_config_1414_; lean_object* v_baseName_1415_; lean_object* v_testDriver_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_config_1414_ = lean_ctor_get(v_self_1236_, 6);
v_baseName_1415_ = lean_ctor_get(v_self_1236_, 1);
v_testDriver_1416_ = lean_ctor_get(v_config_1414_, 12);
v___x_1417_ = lean_string_utf8_byte_size(v_testDriver_1416_);
v___x_1418_ = lean_nat_dec_eq(v___x_1417_, v___x_1301_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_inc(v_baseName_1415_);
lean_dec(v_a_1403_);
lean_dec(v_a_1398_);
lean_dec(v_a_1388_);
lean_dec(v_a_1382_);
lean_dec(v_a_1376_);
lean_dec(v_a_1372_);
lean_dec(v___y_1366_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v___x_1419_ = l_Lean_Name_toString(v_baseName_1415_, v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__2));
v___x_1421_ = lean_string_append(v___x_1419_, v___x_1420_);
v___x_1422_ = 3;
v___x_1423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set_uint8(v___x_1423_, sizeof(void*)*1, v___x_1422_);
v___x_1424_ = lean_array_get_size(v_a_1404_);
v___x_1425_ = lean_array_push(v_a_1404_, v___x_1423_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 1);
lean_ctor_set(v___x_1406_, 1, v___x_1425_);
lean_ctor_set(v___x_1406_, 0, v___x_1424_);
v___x_1427_ = v___x_1406_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_del_object(v___x_1406_);
v___x_1429_ = lean_array_fget(v_a_1403_, v___x_1301_);
lean_dec(v_a_1403_);
v___x_1430_ = l_Lean_Name_toString(v___x_1429_, v___x_1418_);
v___y_1303_ = v_a_1376_;
v___y_1304_ = v___y_1366_;
v___y_1305_ = v_a_1388_;
v___y_1306_ = v_a_1398_;
v___y_1307_ = v_a_1372_;
v___y_1308_ = v_a_1382_;
v_testDriver_1309_ = v___x_1430_;
v___y_1310_ = v_a_1404_;
goto v___jp_1302_;
}
}
}
else
{
lean_object* v_baseName_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec(v_a_1403_);
lean_dec(v_a_1398_);
lean_dec(v_a_1388_);
lean_dec(v_a_1382_);
lean_dec(v_a_1376_);
lean_dec(v_a_1372_);
lean_dec(v___y_1366_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_env_1237_);
v_baseName_1431_ = lean_ctor_get(v_self_1236_, 1);
lean_inc(v_baseName_1431_);
lean_dec_ref(v_self_1236_);
v___x_1432_ = 0;
v___x_1433_ = l_Lean_Name_toString(v_baseName_1431_, v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__3));
v___x_1435_ = lean_string_append(v___x_1433_, v___x_1434_);
v___x_1436_ = 3;
v___x_1437_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*1, v___x_1436_);
v___x_1438_ = lean_array_get_size(v_a_1404_);
v___x_1439_ = lean_array_push(v_a_1404_, v___x_1437_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set_tag(v___x_1406_, 1);
lean_ctor_set(v___x_1406_, 1, v___x_1439_);
lean_ctor_set(v___x_1406_, 0, v___x_1438_);
v___x_1441_ = v___x_1406_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_a_1398_);
lean_dec(v_a_1388_);
lean_dec(v_a_1382_);
lean_dec(v_a_1376_);
lean_dec(v_a_1372_);
lean_dec(v___y_1366_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1444_ = lean_ctor_get(v___x_1402_, 0);
v_a_1445_ = lean_ctor_get(v___x_1402_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1402_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_inc(v_a_1444_);
lean_dec(v___x_1402_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1444_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec(v_a_1388_);
lean_dec(v_a_1382_);
lean_dec(v_a_1376_);
lean_dec(v_a_1372_);
lean_dec(v___y_1366_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1453_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1397_);
v___x_1454_ = lean_io_error_to_string(v_a_1453_);
v___x_1455_ = 3;
v___x_1456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*1, v___x_1455_);
v___x_1457_ = lean_array_get_size(v_a_1389_);
v___x_1458_ = lean_array_push(v_a_1389_, v___x_1456_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 1);
lean_ctor_set(v___x_1391_, 1, v___x_1458_);
lean_ctor_set(v___x_1391_, 0, v___x_1457_);
v___x_1460_ = v___x_1391_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1458_);
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
else
{
lean_object* v_a_1463_; lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1382_);
lean_dec(v_a_1376_);
lean_dec(v_a_1372_);
lean_dec(v___y_1366_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1463_ = lean_ctor_get(v___x_1387_, 0);
v_a_1464_ = lean_ctor_get(v___x_1387_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1387_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_inc(v_a_1463_);
lean_dec(v___x_1387_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1463_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1376_);
lean_dec(v_a_1372_);
lean_dec(v___y_1366_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1472_ = lean_ctor_get(v___x_1381_, 0);
v_a_1473_ = lean_ctor_get(v___x_1381_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1381_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_inc(v_a_1472_);
lean_dec(v___x_1381_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1472_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_a_1372_);
lean_dec(v___y_1366_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1481_ = lean_ctor_get(v___x_1375_, 0);
v_a_1482_ = lean_ctor_get(v___x_1375_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1375_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_inc(v_a_1481_);
lean_dec(v___x_1375_);
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
else
{
lean_object* v_a_1490_; lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v___y_1366_);
lean_dec_ref(v___f_1299_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1490_ = lean_ctor_get(v___x_1371_, 0);
v_a_1491_ = lean_ctor_get(v___x_1371_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1371_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_inc(v_a_1490_);
lean_dec(v___x_1371_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1490_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
v___jp_1499_:
{
if (lean_obj_tag(v___y_1501_) == 0)
{
lean_object* v_a_1502_; 
v_a_1502_ = lean_ctor_get(v___y_1501_, 1);
lean_inc(v_a_1502_);
lean_dec_ref(v___y_1501_);
v___y_1366_ = v___y_1500_;
v_a_1367_ = v_a_1502_;
goto v___jp_1365_;
}
else
{
lean_object* v_a_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v___y_1500_);
lean_dec_ref(v___f_1299_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1503_ = lean_ctor_get(v___y_1501_, 0);
v_a_1504_ = lean_ctor_get(v___y_1501_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___y_1501_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___y_1501_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_inc(v_a_1503_);
lean_dec(v___y_1501_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
v___jp_1513_:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_nat_dec_lt(v___x_1301_, v___x_1512_);
if (v___x_1516_ == 0)
{
v___y_1366_ = v_a_1514_;
v_a_1367_ = v_a_1515_;
goto v___jp_1365_;
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
if (v___x_1517_ == 0)
{
if (v___x_1516_ == 0)
{
v___y_1366_ = v_a_1514_;
v_a_1367_ = v_a_1515_;
goto v___jp_1365_;
}
else
{
size_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_usize_of_nat(v___x_1512_);
lean_inc_ref(v_self_1236_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(v_self_1236_, v_a_1251_, v___x_1249_, v___x_1518_, v___x_1300_, v_a_1515_);
v___y_1500_ = v_a_1514_;
v___y_1501_ = v___x_1519_;
goto v___jp_1499_;
}
}
else
{
size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_usize_of_nat(v___x_1512_);
lean_inc_ref(v_self_1236_);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(v_self_1236_, v_a_1251_, v___x_1249_, v___x_1520_, v___x_1300_, v_a_1515_);
v___y_1500_ = v_a_1514_;
v___y_1501_ = v___x_1521_;
goto v___jp_1499_;
}
}
}
v___jp_1522_:
{
if (lean_obj_tag(v___y_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_a_1525_; 
v_a_1524_ = lean_ctor_get(v___y_1523_, 0);
lean_inc(v_a_1524_);
v_a_1525_ = lean_ctor_get(v___y_1523_, 1);
lean_inc(v_a_1525_);
lean_dec_ref(v___y_1523_);
v_a_1514_ = v_a_1524_;
v_a_1515_ = v_a_1525_;
goto v___jp_1513_;
}
else
{
lean_object* v_a_1526_; lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v___f_1299_);
lean_del_object(v___x_1254_);
lean_dec(v_a_1251_);
lean_dec(v_a_1246_);
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1526_ = lean_ctor_get(v___y_1523_, 0);
v_a_1527_ = lean_ctor_get(v___y_1523_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___y_1523_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___y_1523_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_inc(v_a_1526_);
lean_dec(v___y_1523_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1526_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_a_1246_);
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1542_ = lean_ctor_get(v___x_1250_, 0);
v_a_1543_ = lean_ctor_get(v___x_1250_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1250_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_inc(v_a_1542_);
lean_dec(v___x_1250_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1542_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v_opts_1238_);
lean_dec_ref(v_env_1237_);
lean_dec_ref(v_self_1236_);
v_a_1551_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1245_);
v___x_1552_ = lean_io_error_to_string(v_a_1551_);
v___x_1553_ = 3;
v___x_1554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*1, v___x_1553_);
v___x_1555_ = lean_array_get_size(v_a_1239_);
v___x_1556_ = lean_array_push(v_a_1239_, v___x_1554_);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___boxed(lean_object* v_self_1558_, lean_object* v_env_1559_, lean_object* v_opts_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lake_Package_loadFromEnv(v_self_1558_, v_env_1559_, v_opts_1560_, v_a_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0(lean_object* v_00_u03b2_1564_, lean_object* v_inst_1565_, lean_object* v_t_1566_, lean_object* v_k_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(v_t_1566_, v_k_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___boxed(lean_object* v_00_u03b2_1569_, lean_object* v_inst_1570_, lean_object* v_t_1571_, lean_object* v_k_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0(v_00_u03b2_1569_, v_inst_1570_, v_t_1571_, v_k_1572_);
lean_dec(v_k_1572_);
lean_dec(v_t_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1(lean_object* v_00_u03b2_1574_, lean_object* v_k_1575_, lean_object* v_v_1576_, lean_object* v_t_1577_, lean_object* v_hl_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_k_1575_, v_v_1576_, v_t_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3(lean_object* v_00_u03b2_1580_, lean_object* v_env_1581_, lean_object* v_attr_1582_, lean_object* v_f_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(v_env_1581_, v_attr_1582_, v_f_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1585_, lean_object* v_env_1586_, lean_object* v_attr_1587_, lean_object* v_f_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3(v_00_u03b2_1585_, v_env_1586_, v_attr_1587_, v_f_1588_);
lean_dec_ref(v_attr_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5(lean_object* v_00_u03b4_1590_, lean_object* v_t_1591_, lean_object* v_k_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_t_1591_, v_k_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1594_, lean_object* v_t_1595_, lean_object* v_k_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5(v_00_u03b4_1594_, v_t_1595_, v_k_1596_);
lean_dec(v_k_1596_);
lean_dec(v_t_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7(lean_object* v_00_u03b2_1598_, lean_object* v_env_1599_, lean_object* v_attr_1600_, lean_object* v_f_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(v_env_1599_, v_attr_1600_, v_f_1601_, v___y_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1605_, lean_object* v_env_1606_, lean_object* v_attr_1607_, lean_object* v_f_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7(v_00_u03b2_1605_, v_env_1606_, v_attr_1607_, v_f_1608_, v___y_1609_);
lean_dec_ref(v_attr_1607_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3(lean_object* v_00_u03b2_1612_, lean_object* v_f_1613_, lean_object* v_as_1614_, size_t v_i_1615_, size_t v_stop_1616_, lean_object* v_b_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_1613_, v_as_1614_, v_i_1615_, v_stop_1616_, v_b_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1619_, lean_object* v_f_1620_, lean_object* v_as_1621_, lean_object* v_i_1622_, lean_object* v_stop_1623_, lean_object* v_b_1624_){
_start:
{
size_t v_i_boxed_1625_; size_t v_stop_boxed_1626_; lean_object* v_res_1627_; 
v_i_boxed_1625_ = lean_unbox_usize(v_i_1622_);
lean_dec(v_i_1622_);
v_stop_boxed_1626_ = lean_unbox_usize(v_stop_1623_);
lean_dec(v_stop_1623_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3(v_00_u03b2_1619_, v_f_1620_, v_as_1621_, v_i_boxed_1625_, v_stop_boxed_1626_, v_b_1624_);
lean_dec_ref(v_as_1621_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1628_, lean_object* v_f_1629_, lean_object* v_as_1630_, size_t v_i_1631_, size_t v_stop_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_1629_, v_as_1630_, v_i_1631_, v_stop_1632_, v_b_1633_, v___y_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_f_1638_, lean_object* v_as_1639_, lean_object* v_i_1640_, lean_object* v_stop_1641_, lean_object* v_b_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
size_t v_i_boxed_1645_; size_t v_stop_boxed_1646_; lean_object* v_res_1647_; 
v_i_boxed_1645_ = lean_unbox_usize(v_i_1640_);
lean_dec(v_i_1640_);
v_stop_boxed_1646_ = lean_unbox_usize(v_stop_1641_);
lean_dec(v_stop_1641_);
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8(v_00_u03b2_1637_, v_f_1638_, v_as_1639_, v_i_boxed_1645_, v_stop_boxed_1646_, v_b_1642_, v___y_1643_);
lean_dec_ref(v_as_1639_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1(lean_object* v_env_1648_, lean_object* v_opts_1649_, lean_object* v_as_1650_, size_t v_sz_1651_, size_t v_i_1652_, lean_object* v_b_1653_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = lean_usize_dec_lt(v_i_1652_, v_sz_1651_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_dec_ref(v_env_1648_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_b_1653_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v_a_1657_; lean_object* v___x_1658_; 
v___x_1656_ = l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
v_a_1657_ = lean_array_uget_borrowed(v_as_1650_, v_i_1652_);
lean_inc(v_a_1657_);
lean_inc_ref(v_env_1648_);
v___x_1658_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1648_, v_opts_1649_, v___x_1656_, v_a_1657_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_b_1653_);
lean_dec_ref(v_env_1648_);
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v_name_1668_; lean_object* v_config_1669_; lean_object* v___x_1670_; size_t v___x_1671_; size_t v___x_1672_; 
v_a_1667_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1658_);
v_name_1668_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_name_1668_);
v_config_1669_ = lean_ctor_get(v_a_1667_, 1);
lean_inc(v_config_1669_);
lean_dec(v_a_1667_);
v___x_1670_ = l_Lake_Workspace_addPackageFacetConfig(v_name_1668_, v_config_1669_, v_b_1653_);
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1652_, v___x_1671_);
v_i_1652_ = v___x_1672_;
v_b_1653_ = v___x_1670_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1___boxed(lean_object* v_env_1674_, lean_object* v_opts_1675_, lean_object* v_as_1676_, lean_object* v_sz_1677_, lean_object* v_i_1678_, lean_object* v_b_1679_){
_start:
{
size_t v_sz_boxed_1680_; size_t v_i_boxed_1681_; lean_object* v_res_1682_; 
v_sz_boxed_1680_ = lean_unbox_usize(v_sz_1677_);
lean_dec(v_sz_1677_);
v_i_boxed_1681_ = lean_unbox_usize(v_i_1678_);
lean_dec(v_i_1678_);
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1(v_env_1674_, v_opts_1675_, v_as_1676_, v_sz_boxed_1680_, v_i_boxed_1681_, v_b_1679_);
lean_dec_ref(v_as_1676_);
lean_dec_ref(v_opts_1675_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0(lean_object* v_env_1683_, lean_object* v_opts_1684_, lean_object* v_as_1685_, size_t v_sz_1686_, size_t v_i_1687_, lean_object* v_b_1688_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_usize_dec_lt(v_i_1687_, v_sz_1686_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v_env_1683_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_b_1688_);
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; lean_object* v_a_1692_; lean_object* v___x_1693_; 
v___x_1691_ = l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
v_a_1692_ = lean_array_uget_borrowed(v_as_1685_, v_i_1687_);
lean_inc(v_a_1692_);
lean_inc_ref(v_env_1683_);
v___x_1693_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1683_, v_opts_1684_, v___x_1691_, v_a_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v_b_1688_);
lean_dec_ref(v_env_1683_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v_name_1703_; lean_object* v_config_1704_; lean_object* v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; 
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1693_);
v_name_1703_ = lean_ctor_get(v_a_1702_, 0);
lean_inc(v_name_1703_);
v_config_1704_ = lean_ctor_get(v_a_1702_, 1);
lean_inc(v_config_1704_);
lean_dec(v_a_1702_);
v___x_1705_ = l_Lake_Workspace_addModuleFacetConfig(v_name_1703_, v_config_1704_, v_b_1688_);
v___x_1706_ = ((size_t)1ULL);
v___x_1707_ = lean_usize_add(v_i_1687_, v___x_1706_);
v_i_1687_ = v___x_1707_;
v_b_1688_ = v___x_1705_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0___boxed(lean_object* v_env_1709_, lean_object* v_opts_1710_, lean_object* v_as_1711_, lean_object* v_sz_1712_, lean_object* v_i_1713_, lean_object* v_b_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1712_);
lean_dec(v_sz_1712_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0(v_env_1709_, v_opts_1710_, v_as_1711_, v_sz_boxed_1715_, v_i_boxed_1716_, v_b_1714_);
lean_dec_ref(v_as_1711_);
lean_dec_ref(v_opts_1710_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2(lean_object* v_env_1718_, lean_object* v_opts_1719_, lean_object* v_as_1720_, size_t v_sz_1721_, size_t v_i_1722_, lean_object* v_b_1723_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_lt(v_i_1722_, v_sz_1721_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_env_1718_);
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_b_1723_);
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; lean_object* v_a_1727_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
v_a_1727_ = lean_array_uget_borrowed(v_as_1720_, v_i_1722_);
lean_inc(v_a_1727_);
lean_inc_ref(v_env_1718_);
v___x_1728_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1718_, v_opts_1719_, v___x_1726_, v_a_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_b_1723_);
lean_dec_ref(v_env_1718_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v_name_1738_; lean_object* v_config_1739_; lean_object* v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; 
v_a_1737_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1728_);
v_name_1738_ = lean_ctor_get(v_a_1737_, 0);
lean_inc(v_name_1738_);
v_config_1739_ = lean_ctor_get(v_a_1737_, 1);
lean_inc(v_config_1739_);
lean_dec(v_a_1737_);
v___x_1740_ = l_Lake_Workspace_addLibraryFacetConfig(v_name_1738_, v_config_1739_, v_b_1723_);
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1722_, v___x_1741_);
v_i_1722_ = v___x_1742_;
v_b_1723_ = v___x_1740_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2___boxed(lean_object* v_env_1744_, lean_object* v_opts_1745_, lean_object* v_as_1746_, lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_b_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2(v_env_1744_, v_opts_1745_, v_as_1746_, v_sz_boxed_1750_, v_i_boxed_1751_, v_b_1749_);
lean_dec_ref(v_as_1746_);
lean_dec_ref(v_opts_1745_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object* v_env_1753_, lean_object* v_opts_1754_, lean_object* v_self_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; size_t v_sz_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1756_ = l_Lake_moduleFacetAttr;
lean_inc_ref_n(v_env_1753_, 2);
v___x_1757_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1756_, v_env_1753_);
v_sz_1758_ = lean_array_size(v___x_1757_);
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0(v_env_1753_, v_opts_1754_, v___x_1757_, v_sz_1758_, v___x_1759_, v_self_1755_);
lean_dec_ref(v___x_1757_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_dec_ref(v_env_1753_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; size_t v_sz_1764_; lean_object* v___x_1765_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = l_Lake_packageFacetAttr;
lean_inc_ref_n(v_env_1753_, 2);
v___x_1763_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1762_, v_env_1753_);
v_sz_1764_ = lean_array_size(v___x_1763_);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1(v_env_1753_, v_opts_1754_, v___x_1763_, v_sz_1764_, v___x_1759_, v_a_1761_);
lean_dec_ref(v___x_1763_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_dec_ref(v_env_1753_);
return v___x_1765_;
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; size_t v_sz_1769_; lean_object* v___x_1770_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1753_);
v___x_1768_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1767_, v_env_1753_);
v_sz_1769_ = lean_array_size(v___x_1768_);
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2(v_env_1753_, v_opts_1754_, v___x_1768_, v_sz_1769_, v___x_1759_, v_a_1766_);
lean_dec_ref(v___x_1768_);
return v___x_1770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetsFromEnv___boxed(lean_object* v_env_1771_, lean_object* v_opts_1772_, lean_object* v_self_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lake_Workspace_addFacetsFromEnv(v_env_1771_, v_opts_1772_, v_self_1773_);
lean_dec_ref(v_opts_1772_);
return v_res_1774_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
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
