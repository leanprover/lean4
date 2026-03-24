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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": target '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' was already defined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "', but then redefined as a '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_loadFromEnv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = ": package configuration option 'manifestFile' is deprecated"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__0 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__0_value;
static const lean_string_object l_Lake_Package_loadFromEnv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = ": cannot both set lintDriver and use @[lint_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__1 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__1_value;
static const lean_string_object l_Lake_Package_loadFromEnv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = ": only one script or executable can be tagged @[lint_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__2 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__2_value;
static const lean_string_object l_Lake_Package_loadFromEnv___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = ": cannot both set testDriver and use @[test_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__3 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__3_value;
static const lean_string_object l_Lake_Package_loadFromEnv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = ": only one script, executable, or library can be tagged @[test_driver]"};
static const lean_object* l_Lake_Package_loadFromEnv___closed__4 = (const lean_object*)&l_Lake_Package_loadFromEnv___closed__4_value;
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
lean_dec(v_tail_240_);
lean_dec_ref(v___x_238_);
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
lean_inc(v_scriptName_293_);
v___x_297_ = l_Lean_Name_toString(v_scriptName_293_, v___x_296_);
lean_inc(v_scriptName_293_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4(lean_object* v_self_336_, size_t v_sz_337_, size_t v_i_338_, lean_object* v_bs_339_, lean_object* v___y_340_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_lt(v_i_338_, v_sz_337_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v_self_336_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_bs_339_);
lean_ctor_set(v___x_343_, 1, v___y_340_);
return v___x_343_;
}
else
{
lean_object* v_v_344_; lean_object* v_pkg_345_; lean_object* v_name_346_; lean_object* v_keyName_347_; uint8_t v___x_348_; 
v_v_344_ = lean_array_uget(v_bs_339_, v_i_338_);
v_pkg_345_ = lean_ctor_get(v_v_344_, 0);
v_name_346_ = lean_ctor_get(v_v_344_, 1);
v_keyName_347_ = lean_ctor_get(v_self_336_, 2);
v___x_348_ = lean_name_eq(v_pkg_345_, v_keyName_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
lean_inc(v_keyName_347_);
lean_inc(v_name_346_);
lean_inc(v_pkg_345_);
lean_dec(v_v_344_);
lean_dec_ref(v_bs_339_);
lean_dec_ref(v_self_336_);
v___x_349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__0));
v___x_350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_346_, v___x_342_);
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
lean_dec_ref(v___x_350_);
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__1));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
v___x_354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_345_, v___x_342_);
v___x_355_ = lean_string_append(v___x_353_, v___x_354_);
lean_dec_ref(v___x_354_);
v___x_356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___closed__2));
v___x_357_ = lean_string_append(v___x_355_, v___x_356_);
v___x_358_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_347_, v___x_342_);
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
lean_dec_ref(v___x_358_);
v___x_360_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_361_ = lean_string_append(v___x_359_, v___x_360_);
v___x_362_ = 3;
v___x_363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*1, v___x_362_);
v___x_364_ = lean_array_get_size(v___y_340_);
v___x_365_ = lean_array_push(v___y_340_, v___x_363_);
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v_bs_x27_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v_bs_x27_368_ = lean_array_uset(v_bs_339_, v_i_338_, v___x_367_);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_338_, v___x_369_);
v___x_371_ = lean_array_uset(v_bs_x27_368_, v_i_338_, v_v_344_);
v_i_338_ = v___x_370_;
v_bs_339_ = v___x_371_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4___boxed(lean_object* v_self_373_, lean_object* v_sz_374_, lean_object* v_i_375_, lean_object* v_bs_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
size_t v_sz_boxed_379_; size_t v_i_boxed_380_; lean_object* v_res_381_; 
v_sz_boxed_379_ = lean_unbox_usize(v_sz_374_);
lean_dec(v_sz_374_);
v_i_boxed_380_ = lean_unbox_usize(v_i_375_);
lean_dec(v_i_375_);
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4(v_self_373_, v_sz_boxed_379_, v_i_boxed_380_, v_bs_376_, v___y_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9(lean_object* v_env_384_, lean_object* v_opts_385_, lean_object* v_self_386_, size_t v_sz_387_, size_t v_i_388_, lean_object* v_bs_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_a_393_; lean_object* v_a_394_; uint8_t v___x_396_; 
v___x_396_ = lean_usize_dec_lt(v_i_388_, v_sz_387_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_dec_ref(v_self_386_);
lean_dec_ref(v_env_384_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_bs_389_);
lean_ctor_set(v___x_397_, 1, v___y_390_);
return v___x_397_;
}
else
{
lean_object* v___x_398_; lean_object* v_v_399_; lean_object* v___x_400_; 
v___x_398_ = l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_;
v_v_399_ = lean_array_uget_borrowed(v_bs_389_, v_i_388_);
lean_inc(v_v_399_);
lean_inc_ref(v_env_384_);
v___x_400_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_384_, v_opts_385_, v___x_398_, v_v_399_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_bs_389_);
lean_dec_ref(v_self_386_);
lean_dec_ref(v_env_384_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v___x_402_ = 3;
v___x_403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_403_, 0, v_a_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_402_);
v___x_404_ = lean_array_get_size(v___y_390_);
v___x_405_ = lean_array_push(v___y_390_, v___x_403_);
v_a_393_ = v___x_404_;
v_a_394_ = v___x_405_;
goto v___jp_392_;
}
else
{
lean_object* v_a_406_; lean_object* v_pkg_407_; lean_object* v_fn_408_; lean_object* v_keyName_409_; uint8_t v___x_410_; 
v_a_406_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v___x_400_);
v_pkg_407_ = lean_ctor_get(v_a_406_, 0);
lean_inc(v_pkg_407_);
v_fn_408_ = lean_ctor_get(v_a_406_, 1);
lean_inc_ref(v_fn_408_);
lean_dec(v_a_406_);
v_keyName_409_ = lean_ctor_get(v_self_386_, 2);
v___x_410_ = lean_name_eq(v_pkg_407_, v_keyName_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_inc(v_keyName_409_);
lean_dec_ref(v_fn_408_);
lean_dec_ref(v_bs_389_);
lean_dec_ref(v_self_386_);
lean_dec_ref(v_env_384_);
v___x_411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__0));
v___x_412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_pkg_407_, v___x_396_);
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
lean_dec_ref(v___x_412_);
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___closed__1));
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
v___x_416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_409_, v___x_396_);
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
lean_dec_ref(v___x_416_);
v___x_418_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_419_ = lean_string_append(v___x_417_, v___x_418_);
v___x_420_ = 3;
v___x_421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*1, v___x_420_);
v___x_422_ = lean_array_get_size(v___y_390_);
v___x_423_ = lean_array_push(v___y_390_, v___x_421_);
v_a_393_ = v___x_422_;
v_a_394_ = v___x_423_;
goto v___jp_392_;
}
else
{
lean_object* v___x_424_; lean_object* v_bs_x27_425_; size_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
lean_dec(v_pkg_407_);
v___x_424_ = lean_unsigned_to_nat(0u);
v_bs_x27_425_ = lean_array_uset(v_bs_389_, v_i_388_, v___x_424_);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_add(v_i_388_, v___x_426_);
v___x_428_ = lean_array_uset(v_bs_x27_425_, v_i_388_, v_fn_408_);
v_i_388_ = v___x_427_;
v_bs_389_ = v___x_428_;
goto _start;
}
}
}
v___jp_392_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_395_, 0, v_a_393_);
lean_ctor_set(v___x_395_, 1, v_a_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9___boxed(lean_object* v_env_430_, lean_object* v_opts_431_, lean_object* v_self_432_, lean_object* v_sz_433_, lean_object* v_i_434_, lean_object* v_bs_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
size_t v_sz_boxed_438_; size_t v_i_boxed_439_; lean_object* v_res_440_; 
v_sz_boxed_438_ = lean_unbox_usize(v_sz_433_);
lean_dec(v_sz_433_);
v_i_boxed_439_ = lean_unbox_usize(v_i_434_);
lean_dec(v_i_434_);
v_res_440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9(v_env_430_, v_opts_431_, v_self_432_, v_sz_boxed_438_, v_i_boxed_439_, v_bs_435_, v___y_436_);
lean_dec_ref(v_opts_431_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10(lean_object* v_env_441_, lean_object* v_opts_442_, size_t v_sz_443_, size_t v_i_444_, lean_object* v_bs_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_lt(v_i_444_, v_sz_443_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v_env_441_);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_bs_445_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v_v_449_; lean_object* v___x_450_; 
v___x_448_ = l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_34_;
v_v_449_ = lean_array_uget_borrowed(v_bs_445_, v_i_444_);
lean_inc(v_v_449_);
lean_inc_ref(v_env_441_);
v___x_450_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_441_, v_opts_442_, v___x_448_, v_v_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_bs_445_);
lean_dec_ref(v_env_441_);
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v_bs_x27_461_; size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v_a_459_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_450_);
v___x_460_ = lean_unsigned_to_nat(0u);
v_bs_x27_461_ = lean_array_uset(v_bs_445_, v_i_444_, v___x_460_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_add(v_i_444_, v___x_462_);
v___x_464_ = lean_array_uset(v_bs_x27_461_, v_i_444_, v_a_459_);
v_i_444_ = v___x_463_;
v_bs_445_ = v___x_464_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10___boxed(lean_object* v_env_466_, lean_object* v_opts_467_, lean_object* v_sz_468_, lean_object* v_i_469_, lean_object* v_bs_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10(v_env_466_, v_opts_467_, v_sz_boxed_471_, v_i_boxed_472_, v_bs_470_);
lean_dec_ref(v_opts_467_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(lean_object* v_f_474_, lean_object* v_as_475_, size_t v_i_476_, size_t v_stop_477_, lean_object* v_b_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_usize_dec_eq(v_i_476_, v_stop_477_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_array_uget_borrowed(v_as_475_, v_i_476_);
lean_inc_ref(v_f_474_);
lean_inc(v___x_480_);
v___x_481_ = lean_apply_1(v_f_474_, v___x_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v_b_478_);
lean_dec_ref(v_f_474_);
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; 
v_a_490_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_490_);
lean_dec_ref(v___x_481_);
v___x_491_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_mkDTagMap___redArg___lam__0___closed__0));
lean_inc(v___x_480_);
v___x_492_ = l_Lake_RBArray_insert___redArg(v___x_491_, v_b_478_, v___x_480_, v_a_490_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_476_, v___x_493_);
v_i_476_ = v___x_494_;
v_b_478_ = v___x_492_;
goto _start;
}
}
else
{
lean_object* v___x_496_; 
lean_dec_ref(v_f_474_);
v___x_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_496_, 0, v_b_478_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg___boxed(lean_object* v_f_497_, lean_object* v_as_498_, lean_object* v_i_499_, lean_object* v_stop_500_, lean_object* v_b_501_){
_start:
{
size_t v_i_boxed_502_; size_t v_stop_boxed_503_; lean_object* v_res_504_; 
v_i_boxed_502_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_stop_boxed_503_ = lean_unbox_usize(v_stop_500_);
lean_dec(v_stop_500_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_497_, v_as_498_, v_i_boxed_502_, v_stop_boxed_503_, v_b_501_);
lean_dec_ref(v_as_498_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(lean_object* v_env_505_, lean_object* v_attr_506_, lean_object* v_f_507_){
_start:
{
lean_object* v_entries_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_entries_508_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_506_, v_env_505_);
v___x_509_ = lean_array_get_size(v_entries_508_);
v___x_510_ = l_Lake_RBArray_mkEmpty___redArg(v___x_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_nat_dec_lt(v___x_511_, v___x_509_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec_ref(v_entries_508_);
lean_dec_ref(v_f_507_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_510_);
return v___x_513_;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = lean_nat_dec_le(v___x_509_, v___x_509_);
if (v___x_514_ == 0)
{
if (v___x_512_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v_entries_508_);
lean_dec_ref(v_f_507_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_510_);
return v___x_515_;
}
else
{
size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; 
v___x_516_ = ((size_t)0ULL);
v___x_517_ = lean_usize_of_nat(v___x_509_);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_507_, v_entries_508_, v___x_516_, v___x_517_, v___x_510_);
lean_dec_ref(v_entries_508_);
return v___x_518_;
}
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___x_509_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_507_, v_entries_508_, v___x_519_, v___x_520_, v___x_510_);
lean_dec_ref(v_entries_508_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg___boxed(lean_object* v_env_522_, lean_object* v_attr_523_, lean_object* v_f_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(v_env_522_, v_attr_523_, v_f_524_);
lean_dec_ref(v_attr_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(lean_object* v_f_526_, lean_object* v_as_527_, size_t v_i_528_, size_t v_stop_529_, lean_object* v_b_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = lean_usize_dec_eq(v_i_528_, v_stop_529_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_array_uget_borrowed(v_as_527_, v_i_528_);
lean_inc_ref(v_f_526_);
lean_inc(v___x_534_);
v___x_535_ = lean_apply_3(v_f_526_, v___x_534_, v___y_531_, lean_box(0));
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_a_537_; lean_object* v___x_538_; size_t v___x_539_; size_t v___x_540_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
v_a_537_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_a_537_);
lean_dec_ref(v___x_535_);
lean_inc(v___x_534_);
v___x_538_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_534_, v_a_536_, v_b_530_);
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_add(v_i_528_, v___x_539_);
v_i_528_ = v___x_540_;
v_b_530_ = v___x_538_;
v___y_531_ = v_a_537_;
goto _start;
}
else
{
lean_object* v_a_542_; lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_b_530_);
lean_dec_ref(v_f_526_);
v_a_542_ = lean_ctor_get(v___x_535_, 0);
v_a_543_ = lean_ctor_get(v___x_535_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_535_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_inc(v_a_542_);
lean_dec(v___x_535_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_542_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_a_543_);
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
else
{
lean_object* v___x_551_; 
lean_dec_ref(v_f_526_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_b_530_);
lean_ctor_set(v___x_551_, 1, v___y_531_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg___boxed(lean_object* v_f_552_, lean_object* v_as_553_, lean_object* v_i_554_, lean_object* v_stop_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
size_t v_i_boxed_559_; size_t v_stop_boxed_560_; lean_object* v_res_561_; 
v_i_boxed_559_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_stop_boxed_560_ = lean_unbox_usize(v_stop_555_);
lean_dec(v_stop_555_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_552_, v_as_553_, v_i_boxed_559_, v_stop_boxed_560_, v_b_556_, v___y_557_);
lean_dec_ref(v_as_553_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(lean_object* v_env_562_, lean_object* v_attr_563_, lean_object* v_f_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_entries_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_entries_567_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_563_, v_env_562_);
v___x_568_ = lean_box(1);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_array_get_size(v_entries_567_);
v___x_571_ = lean_nat_dec_lt(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_dec_ref(v_entries_567_);
lean_dec_ref(v_f_564_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_568_);
lean_ctor_set(v___x_572_, 1, v___y_565_);
return v___x_572_;
}
else
{
uint8_t v___x_573_; 
v___x_573_ = lean_nat_dec_le(v___x_570_, v___x_570_);
if (v___x_573_ == 0)
{
if (v___x_571_ == 0)
{
lean_object* v___x_574_; 
lean_dec_ref(v_entries_567_);
lean_dec_ref(v_f_564_);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_568_);
lean_ctor_set(v___x_574_, 1, v___y_565_);
return v___x_574_;
}
else
{
size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
v___x_575_ = ((size_t)0ULL);
v___x_576_ = lean_usize_of_nat(v___x_570_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_564_, v_entries_567_, v___x_575_, v___x_576_, v___x_568_, v___y_565_);
lean_dec_ref(v_entries_567_);
return v___x_577_;
}
}
else
{
size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_570_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_564_, v_entries_567_, v___x_578_, v___x_579_, v___x_568_, v___y_565_);
lean_dec_ref(v_entries_567_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg___boxed(lean_object* v_env_581_, lean_object* v_attr_582_, lean_object* v_f_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(v_env_581_, v_attr_582_, v_f_583_, v___y_584_);
lean_dec_ref(v_attr_582_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(lean_object* v_t_587_, lean_object* v_k_588_){
_start:
{
if (lean_obj_tag(v_t_587_) == 0)
{
lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_l_591_; lean_object* v_r_592_; uint8_t v___x_593_; 
v_k_589_ = lean_ctor_get(v_t_587_, 1);
v_v_590_ = lean_ctor_get(v_t_587_, 2);
v_l_591_ = lean_ctor_get(v_t_587_, 3);
v_r_592_ = lean_ctor_get(v_t_587_, 4);
v___x_593_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_588_, v_k_589_);
switch(v___x_593_)
{
case 0:
{
v_t_587_ = v_l_591_;
goto _start;
}
case 1:
{
lean_object* v___x_595_; 
lean_inc(v_v_590_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_v_590_);
return v___x_595_;
}
default: 
{
v_t_587_ = v_r_592_;
goto _start;
}
}
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg___boxed(lean_object* v_t_598_, lean_object* v_k_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_t_598_, v_k_599_);
lean_dec(v_k_599_);
lean_dec(v_t_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8(lean_object* v_a_603_, lean_object* v_self_604_, size_t v_sz_605_, size_t v_i_606_, lean_object* v_bs_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___x_610_; 
v___x_610_ = lean_usize_dec_lt(v_i_606_, v_sz_605_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_dec_ref(v_self_604_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v_bs_607_);
lean_ctor_set(v___x_611_, 1, v___y_608_);
return v___x_611_;
}
else
{
lean_object* v_v_612_; lean_object* v___x_613_; 
v_v_612_ = lean_array_uget_borrowed(v_bs_607_, v_i_606_);
v___x_613_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_a_603_, v_v_612_);
if (lean_obj_tag(v___x_613_) == 1)
{
lean_object* v_val_614_; lean_object* v___x_615_; lean_object* v_bs_x27_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v_val_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_val_614_);
lean_dec_ref(v___x_613_);
v___x_615_ = lean_unsigned_to_nat(0u);
v_bs_x27_616_ = lean_array_uset(v_bs_607_, v_i_606_, v___x_615_);
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_606_, v___x_617_);
v___x_619_ = lean_array_uset(v_bs_x27_616_, v_i_606_, v_val_614_);
v_i_606_ = v___x_618_;
v_bs_607_ = v___x_619_;
goto _start;
}
else
{
lean_object* v_baseName_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_inc(v_v_612_);
lean_dec(v___x_613_);
lean_dec_ref(v_bs_607_);
v_baseName_621_ = lean_ctor_get(v_self_604_, 1);
lean_inc(v_baseName_621_);
lean_dec_ref(v_self_604_);
v___x_622_ = 0;
v___x_623_ = l_Lean_Name_toString(v_baseName_621_, v___x_622_);
v___x_624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__0));
v___x_625_ = lean_string_append(v___x_623_, v___x_624_);
v___x_626_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_612_, v___x_610_);
v___x_627_ = lean_string_append(v___x_625_, v___x_626_);
lean_dec_ref(v___x_626_);
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__1));
v___x_629_ = lean_string_append(v___x_627_, v___x_628_);
v___x_630_ = 3;
v___x_631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*1, v___x_630_);
v___x_632_ = lean_array_get_size(v___y_608_);
v___x_633_ = lean_array_push(v___y_608_, v___x_631_);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___boxed(lean_object* v_a_635_, lean_object* v_self_636_, lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_bs_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_643_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8(v_a_635_, v_self_636_, v_sz_boxed_642_, v_i_boxed_643_, v_bs_639_, v___y_640_);
lean_dec(v_a_635_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11(lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_self_649_, size_t v_sz_650_, size_t v_i_651_, lean_object* v_bs_652_, lean_object* v___y_653_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_lt(v_i_651_, v_sz_650_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_self_649_);
lean_dec_ref(v_a_647_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_bs_652_);
lean_ctor_set(v___x_656_, 1, v___y_653_);
return v___x_656_;
}
else
{
lean_object* v_toTreeMap_657_; lean_object* v_v_658_; lean_object* v___x_659_; lean_object* v_bs_x27_660_; lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___x_668_; 
v_toTreeMap_657_ = lean_ctor_get(v_a_647_, 0);
v_v_658_ = lean_array_uget(v_bs_652_, v_i_651_);
v___x_659_ = lean_unsigned_to_nat(0u);
v_bs_x27_660_ = lean_array_uset(v_bs_652_, v_i_651_, v___x_659_);
v___x_668_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_toTreeMap_657_, v_v_658_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; lean_object* v_name_670_; 
lean_dec(v_v_658_);
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v___x_668_);
v_name_670_ = lean_ctor_get(v_val_669_, 1);
lean_inc(v_name_670_);
lean_dec(v_val_669_);
v_a_662_ = v_name_670_;
v_a_663_ = v___y_653_;
goto v___jp_661_;
}
else
{
uint8_t v___x_671_; 
lean_dec(v___x_668_);
v___x_671_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_658_, v_a_648_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_bs_x27_660_);
v_isSharedCheck_690_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; lean_object* v_unused_692_; 
v_unused_691_ = lean_ctor_get(v_a_647_, 1);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v_a_647_, 0);
lean_dec(v_unused_692_);
v___x_673_ = v_a_647_;
v_isShared_674_ = v_isSharedCheck_690_;
goto v_resetjp_672_;
}
else
{
lean_dec(v_a_647_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_690_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_baseName_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v_baseName_675_ = lean_ctor_get(v_self_649_, 1);
lean_inc(v_baseName_675_);
lean_dec_ref(v_self_649_);
v___x_676_ = l_Lean_Name_toString(v_baseName_675_, v___x_671_);
v___x_677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__0));
v___x_678_ = lean_string_append(v___x_676_, v___x_677_);
v___x_679_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_658_, v___x_655_);
v___x_680_ = lean_string_append(v___x_678_, v___x_679_);
lean_dec_ref(v___x_679_);
v___x_681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__1));
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
v___x_683_ = 3;
v___x_684_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*1, v___x_683_);
v___x_685_ = lean_array_get_size(v___y_653_);
v___x_686_ = lean_array_push(v___y_653_, v___x_684_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 1);
lean_ctor_set(v___x_673_, 1, v___x_686_);
lean_ctor_set(v___x_673_, 0, v___x_685_);
v___x_688_ = v___x_673_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
v_a_662_ = v_v_658_;
v_a_663_ = v___y_653_;
goto v___jp_661_;
}
}
v___jp_661_:
{
size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_add(v_i_651_, v___x_664_);
v___x_666_ = lean_array_uset(v_bs_x27_660_, v_i_651_, v_a_662_);
v_i_651_ = v___x_665_;
v_bs_652_ = v___x_666_;
v___y_653_ = v_a_663_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___boxed(lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_self_695_, lean_object* v_sz_696_, lean_object* v_i_697_, lean_object* v_bs_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_sz_boxed_701_; size_t v_i_boxed_702_; lean_object* v_res_703_; 
v_sz_boxed_701_ = lean_unbox_usize(v_sz_696_);
lean_dec(v_sz_696_);
v_i_boxed_702_ = lean_unbox_usize(v_i_697_);
lean_dec(v_i_697_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11(v_a_693_, v_a_694_, v_self_695_, v_sz_boxed_701_, v_i_boxed_702_, v_bs_698_, v___y_699_);
lean_dec(v_a_694_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6(lean_object* v_a_705_, lean_object* v_self_706_, size_t v_sz_707_, size_t v_i_708_, lean_object* v_bs_709_, lean_object* v___y_710_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_lt(v_i_708_, v_sz_707_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v_self_706_);
lean_dec_ref(v_a_705_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_bs_709_);
lean_ctor_set(v___x_713_, 1, v___y_710_);
return v___x_713_;
}
else
{
lean_object* v_toTreeMap_714_; lean_object* v_v_715_; lean_object* v___x_716_; 
v_toTreeMap_714_ = lean_ctor_get(v_a_705_, 0);
v_v_715_ = lean_array_uget_borrowed(v_bs_709_, v_i_708_);
v___x_716_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_toTreeMap_714_, v_v_715_);
if (lean_obj_tag(v___x_716_) == 1)
{
lean_object* v_val_717_; lean_object* v_name_718_; lean_object* v___x_719_; lean_object* v_bs_x27_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v_val_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v___x_716_);
v_name_718_ = lean_ctor_get(v_val_717_, 1);
lean_inc(v_name_718_);
lean_dec(v_val_717_);
v___x_719_ = lean_unsigned_to_nat(0u);
v_bs_x27_720_ = lean_array_uset(v_bs_709_, v_i_708_, v___x_719_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_708_, v___x_721_);
v___x_723_ = lean_array_uset(v_bs_x27_720_, v_i_708_, v_name_718_);
v_i_708_ = v___x_722_;
v_bs_709_ = v___x_723_;
goto _start;
}
else
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_744_; 
lean_inc(v_v_715_);
lean_dec(v___x_716_);
lean_dec_ref(v_bs_709_);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_705_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; lean_object* v_unused_746_; 
v_unused_745_ = lean_ctor_get(v_a_705_, 1);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_a_705_, 0);
lean_dec(v_unused_746_);
v___x_726_ = v_a_705_;
v_isShared_727_ = v_isSharedCheck_744_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_a_705_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_744_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_baseName_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v_baseName_728_ = lean_ctor_get(v_self_706_, 1);
lean_inc(v_baseName_728_);
lean_dec_ref(v_self_706_);
v___x_729_ = 0;
v___x_730_ = l_Lean_Name_toString(v_baseName_728_, v___x_729_);
v___x_731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___closed__0));
v___x_732_ = lean_string_append(v___x_730_, v___x_731_);
v___x_733_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_715_, v___x_712_);
v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
lean_dec_ref(v___x_733_);
v___x_735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8___closed__1));
v___x_736_ = lean_string_append(v___x_734_, v___x_735_);
v___x_737_ = 3;
v___x_738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set_uint8(v___x_738_, sizeof(void*)*1, v___x_737_);
v___x_739_ = lean_array_get_size(v___y_710_);
v___x_740_ = lean_array_push(v___y_710_, v___x_738_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
lean_ctor_set(v___x_726_, 1, v___x_740_);
lean_ctor_set(v___x_726_, 0, v___x_739_);
v___x_742_ = v___x_726_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6___boxed(lean_object* v_a_747_, lean_object* v_self_748_, lean_object* v_sz_749_, lean_object* v_i_750_, lean_object* v_bs_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_749_);
lean_dec(v_sz_749_);
v_i_boxed_755_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6(v_a_747_, v_self_748_, v_sz_boxed_754_, v_i_boxed_755_, v_bs_751_, v___y_752_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12(lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_self_760_, size_t v_sz_761_, size_t v_i_762_, lean_object* v_bs_763_, lean_object* v___y_764_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_lt(v_i_762_, v_sz_761_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v_self_760_);
lean_dec_ref(v_a_758_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_bs_763_);
lean_ctor_set(v___x_767_, 1, v___y_764_);
return v___x_767_;
}
else
{
lean_object* v_toTreeMap_768_; lean_object* v_v_769_; lean_object* v___x_770_; lean_object* v_bs_x27_771_; lean_object* v_a_773_; lean_object* v_a_774_; lean_object* v___x_779_; 
v_toTreeMap_768_ = lean_ctor_get(v_a_758_, 0);
v_v_769_ = lean_array_uget(v_bs_763_, v_i_762_);
v___x_770_ = lean_unsigned_to_nat(0u);
v_bs_x27_771_ = lean_array_uset(v_bs_763_, v_i_762_, v___x_770_);
v___x_779_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_toTreeMap_768_, v_v_769_);
if (lean_obj_tag(v___x_779_) == 1)
{
lean_object* v_val_780_; lean_object* v_name_781_; 
lean_dec(v_v_769_);
v_val_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref(v___x_779_);
v_name_781_ = lean_ctor_get(v_val_780_, 1);
lean_inc(v_name_781_);
lean_dec(v_val_780_);
v_a_773_ = v_name_781_;
v_a_774_ = v___y_764_;
goto v___jp_772_;
}
else
{
uint8_t v___x_782_; 
lean_dec(v___x_779_);
v___x_782_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_v_769_, v_a_759_);
if (v___x_782_ == 0)
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_bs_x27_771_);
v_isSharedCheck_801_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_802_ = lean_ctor_get(v_a_758_, 1);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_a_758_, 0);
lean_dec(v_unused_803_);
v___x_784_ = v_a_758_;
v_isShared_785_ = v_isSharedCheck_801_;
goto v_resetjp_783_;
}
else
{
lean_dec(v_a_758_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_801_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_baseName_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v_baseName_786_ = lean_ctor_get(v_self_760_, 1);
lean_inc(v_baseName_786_);
lean_dec_ref(v_self_760_);
v___x_787_ = l_Lean_Name_toString(v_baseName_786_, v___x_782_);
v___x_788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11___closed__0));
v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
v___x_790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_v_769_, v___x_766_);
v___x_791_ = lean_string_append(v___x_789_, v___x_790_);
lean_dec_ref(v___x_790_);
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___closed__0));
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
v___x_794_ = 3;
v___x_795_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*1, v___x_794_);
v___x_796_ = lean_array_get_size(v___y_764_);
v___x_797_ = lean_array_push(v___y_764_, v___x_795_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 1);
lean_ctor_set(v___x_784_, 1, v___x_797_);
lean_ctor_set(v___x_784_, 0, v___x_796_);
v___x_799_ = v___x_784_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
v_a_773_ = v_v_769_;
v_a_774_ = v___y_764_;
goto v___jp_772_;
}
}
v___jp_772_:
{
size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_add(v_i_762_, v___x_775_);
v___x_777_ = lean_array_uset(v_bs_x27_771_, v_i_762_, v_a_773_);
v_i_762_ = v___x_776_;
v_bs_763_ = v___x_777_;
v___y_764_ = v_a_774_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12___boxed(lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_self_806_, lean_object* v_sz_807_, lean_object* v_i_808_, lean_object* v_bs_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
size_t v_sz_boxed_812_; size_t v_i_boxed_813_; lean_object* v_res_814_; 
v_sz_boxed_812_ = lean_unbox_usize(v_sz_807_);
lean_dec(v_sz_807_);
v_i_boxed_813_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12(v_a_804_, v_a_805_, v_self_806_, v_sz_boxed_812_, v_i_boxed_813_, v_bs_809_, v___y_810_);
lean_dec(v_a_805_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(lean_object* v_k_815_, lean_object* v_v_816_, lean_object* v_t_817_){
_start:
{
if (lean_obj_tag(v_t_817_) == 0)
{
lean_object* v_size_818_; lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v_l_821_; lean_object* v_r_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_1102_; 
v_size_818_ = lean_ctor_get(v_t_817_, 0);
v_k_819_ = lean_ctor_get(v_t_817_, 1);
v_v_820_ = lean_ctor_get(v_t_817_, 2);
v_l_821_ = lean_ctor_get(v_t_817_, 3);
v_r_822_ = lean_ctor_get(v_t_817_, 4);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_t_817_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_824_ = v_t_817_;
v_isShared_825_ = v_isSharedCheck_1102_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_r_822_);
lean_inc(v_l_821_);
lean_inc(v_v_820_);
lean_inc(v_k_819_);
lean_inc(v_size_818_);
lean_dec(v_t_817_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_1102_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
uint8_t v___x_826_; 
v___x_826_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_815_, v_k_819_);
switch(v___x_826_)
{
case 0:
{
lean_object* v_impl_827_; lean_object* v___x_828_; 
lean_dec(v_size_818_);
v_impl_827_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_k_815_, v_v_816_, v_l_821_);
v___x_828_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_822_) == 0)
{
lean_object* v_size_829_; lean_object* v_size_830_; lean_object* v_k_831_; lean_object* v_v_832_; lean_object* v_l_833_; lean_object* v_r_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_size_829_ = lean_ctor_get(v_r_822_, 0);
v_size_830_ = lean_ctor_get(v_impl_827_, 0);
lean_inc(v_size_830_);
v_k_831_ = lean_ctor_get(v_impl_827_, 1);
lean_inc(v_k_831_);
v_v_832_ = lean_ctor_get(v_impl_827_, 2);
lean_inc(v_v_832_);
v_l_833_ = lean_ctor_get(v_impl_827_, 3);
lean_inc(v_l_833_);
v_r_834_ = lean_ctor_get(v_impl_827_, 4);
lean_inc(v_r_834_);
v___x_835_ = lean_unsigned_to_nat(3u);
v___x_836_ = lean_nat_mul(v___x_835_, v_size_829_);
v___x_837_ = lean_nat_dec_lt(v___x_836_, v_size_830_);
lean_dec(v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
lean_dec(v_r_834_);
lean_dec(v_l_833_);
lean_dec(v_v_832_);
lean_dec(v_k_831_);
v___x_838_ = lean_nat_add(v___x_828_, v_size_830_);
lean_dec(v_size_830_);
v___x_839_ = lean_nat_add(v___x_838_, v_size_829_);
lean_dec(v___x_838_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 3, v_impl_827_);
lean_ctor_set(v___x_824_, 0, v___x_839_);
v___x_841_ = v___x_824_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_impl_827_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_r_822_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_908_; 
v_isSharedCheck_908_ = !lean_is_exclusive(v_impl_827_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_909_ = lean_ctor_get(v_impl_827_, 4);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_impl_827_, 3);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_impl_827_, 2);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_impl_827_, 1);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_impl_827_, 0);
lean_dec(v_unused_913_);
v___x_844_ = v_impl_827_;
v_isShared_845_ = v_isSharedCheck_908_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_impl_827_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_908_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_size_846_; lean_object* v_size_847_; lean_object* v_k_848_; lean_object* v_v_849_; lean_object* v_l_850_; lean_object* v_r_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_size_846_ = lean_ctor_get(v_l_833_, 0);
v_size_847_ = lean_ctor_get(v_r_834_, 0);
v_k_848_ = lean_ctor_get(v_r_834_, 1);
v_v_849_ = lean_ctor_get(v_r_834_, 2);
v_l_850_ = lean_ctor_get(v_r_834_, 3);
v_r_851_ = lean_ctor_get(v_r_834_, 4);
v___x_852_ = lean_unsigned_to_nat(2u);
v___x_853_ = lean_nat_mul(v___x_852_, v_size_846_);
v___x_854_ = lean_nat_dec_lt(v_size_847_, v___x_853_);
lean_dec(v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_883_; 
lean_inc(v_r_851_);
lean_inc(v_l_850_);
lean_inc(v_v_849_);
lean_inc(v_k_848_);
v_isSharedCheck_883_ = !lean_is_exclusive(v_r_834_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; lean_object* v_unused_888_; 
v_unused_884_ = lean_ctor_get(v_r_834_, 4);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_r_834_, 3);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_r_834_, 2);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_r_834_, 1);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_r_834_, 0);
lean_dec(v_unused_888_);
v___x_856_ = v_r_834_;
v_isShared_857_ = v_isSharedCheck_883_;
goto v_resetjp_855_;
}
else
{
lean_dec(v_r_834_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_883_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___x_871_; lean_object* v___y_873_; 
v___x_858_ = lean_nat_add(v___x_828_, v_size_830_);
lean_dec(v_size_830_);
v___x_859_ = lean_nat_add(v___x_858_, v_size_829_);
lean_dec(v___x_858_);
v___x_871_ = lean_nat_add(v___x_828_, v_size_846_);
if (lean_obj_tag(v_l_850_) == 0)
{
lean_object* v_size_881_; 
v_size_881_ = lean_ctor_get(v_l_850_, 0);
lean_inc(v_size_881_);
v___y_873_ = v_size_881_;
goto v___jp_872_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___y_873_ = v___x_882_;
goto v___jp_872_;
}
v___jp_860_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_nat_add(v___y_861_, v___y_863_);
lean_dec(v___y_863_);
lean_dec(v___y_861_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 4, v_r_822_);
lean_ctor_set(v___x_856_, 3, v_r_851_);
lean_ctor_set(v___x_856_, 2, v_v_820_);
lean_ctor_set(v___x_856_, 1, v_k_819_);
lean_ctor_set(v___x_856_, 0, v___x_864_);
v___x_866_ = v___x_856_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_r_851_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_r_822_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v___x_866_);
lean_ctor_set(v___x_844_, 3, v___y_862_);
lean_ctor_set(v___x_844_, 2, v_v_849_);
lean_ctor_set(v___x_844_, 1, v_k_848_);
lean_ctor_set(v___x_844_, 0, v___x_859_);
v___x_868_ = v___x_844_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v___y_862_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_nat_add(v___x_871_, v___y_873_);
lean_dec(v___y_873_);
lean_dec(v___x_871_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_l_850_);
lean_ctor_set(v___x_824_, 3, v_l_833_);
lean_ctor_set(v___x_824_, 2, v_v_832_);
lean_ctor_set(v___x_824_, 1, v_k_831_);
lean_ctor_set(v___x_824_, 0, v___x_874_);
v___x_876_ = v___x_824_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_k_831_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_v_832_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v_l_833_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v_l_850_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_nat_add(v___x_828_, v_size_829_);
if (lean_obj_tag(v_r_851_) == 0)
{
lean_object* v_size_878_; 
v_size_878_ = lean_ctor_get(v_r_851_, 0);
lean_inc(v_size_878_);
v___y_861_ = v___x_877_;
v___y_862_ = v___x_876_;
v___y_863_ = v_size_878_;
goto v___jp_860_;
}
else
{
lean_object* v___x_879_; 
v___x_879_ = lean_unsigned_to_nat(0u);
v___y_861_ = v___x_877_;
v___y_862_ = v___x_876_;
v___y_863_ = v___x_879_;
goto v___jp_860_;
}
}
}
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
lean_del_object(v___x_824_);
v___x_889_ = lean_nat_add(v___x_828_, v_size_830_);
lean_dec(v_size_830_);
v___x_890_ = lean_nat_add(v___x_889_, v_size_829_);
lean_dec(v___x_889_);
v___x_891_ = lean_nat_add(v___x_828_, v_size_829_);
v___x_892_ = lean_nat_add(v___x_891_, v_size_847_);
lean_dec(v___x_891_);
lean_inc_ref(v_r_822_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_r_822_);
lean_ctor_set(v___x_844_, 3, v_r_834_);
lean_ctor_set(v___x_844_, 2, v_v_820_);
lean_ctor_set(v___x_844_, 1, v_k_819_);
lean_ctor_set(v___x_844_, 0, v___x_892_);
v___x_894_ = v___x_844_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_r_834_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_r_822_);
v___x_894_ = v_reuseFailAlloc_907_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
v_isSharedCheck_901_ = !lean_is_exclusive(v_r_822_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; lean_object* v_unused_903_; lean_object* v_unused_904_; lean_object* v_unused_905_; lean_object* v_unused_906_; 
v_unused_902_ = lean_ctor_get(v_r_822_, 4);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_r_822_, 3);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_r_822_, 2);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_r_822_, 1);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_r_822_, 0);
lean_dec(v_unused_906_);
v___x_896_ = v_r_822_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_dec(v_r_822_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 4, v___x_894_);
lean_ctor_set(v___x_896_, 3, v_l_833_);
lean_ctor_set(v___x_896_, 2, v_v_832_);
lean_ctor_set(v___x_896_, 1, v_k_831_);
lean_ctor_set(v___x_896_, 0, v___x_890_);
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_k_831_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_v_832_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_l_833_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v___x_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_914_; 
v_l_914_ = lean_ctor_get(v_impl_827_, 3);
lean_inc(v_l_914_);
if (lean_obj_tag(v_l_914_) == 0)
{
lean_object* v_r_915_; lean_object* v_k_916_; lean_object* v_v_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_928_; 
v_r_915_ = lean_ctor_get(v_impl_827_, 4);
v_k_916_ = lean_ctor_get(v_impl_827_, 1);
v_v_917_ = lean_ctor_get(v_impl_827_, 2);
v_isSharedCheck_928_ = !lean_is_exclusive(v_impl_827_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; lean_object* v_unused_930_; 
v_unused_929_ = lean_ctor_get(v_impl_827_, 3);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_impl_827_, 0);
lean_dec(v_unused_930_);
v___x_919_ = v_impl_827_;
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_r_915_);
lean_inc(v_v_917_);
lean_inc(v_k_916_);
lean_dec(v_impl_827_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_915_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 3, v_r_915_);
lean_ctor_set(v___x_919_, 2, v_v_820_);
lean_ctor_set(v___x_919_, 1, v_k_819_);
lean_ctor_set(v___x_919_, 0, v___x_828_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_r_915_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_r_915_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v___x_923_);
lean_ctor_set(v___x_824_, 3, v_l_914_);
lean_ctor_set(v___x_824_, 2, v_v_917_);
lean_ctor_set(v___x_824_, 1, v_k_916_);
lean_ctor_set(v___x_824_, 0, v___x_921_);
v___x_925_ = v___x_824_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_k_916_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_v_917_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_l_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_r_931_; 
v_r_931_ = lean_ctor_get(v_impl_827_, 4);
lean_inc(v_r_931_);
if (lean_obj_tag(v_r_931_) == 0)
{
lean_object* v_k_932_; lean_object* v_v_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_956_; 
v_k_932_ = lean_ctor_get(v_impl_827_, 1);
v_v_933_ = lean_ctor_get(v_impl_827_, 2);
v_isSharedCheck_956_ = !lean_is_exclusive(v_impl_827_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; lean_object* v_unused_958_; lean_object* v_unused_959_; 
v_unused_957_ = lean_ctor_get(v_impl_827_, 4);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_impl_827_, 3);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_impl_827_, 0);
lean_dec(v_unused_959_);
v___x_935_ = v_impl_827_;
v_isShared_936_ = v_isSharedCheck_956_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_v_933_);
lean_inc(v_k_932_);
lean_dec(v_impl_827_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_956_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_k_937_; lean_object* v_v_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_952_; 
v_k_937_ = lean_ctor_get(v_r_931_, 1);
v_v_938_ = lean_ctor_get(v_r_931_, 2);
v_isSharedCheck_952_ = !lean_is_exclusive(v_r_931_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; 
v_unused_953_ = lean_ctor_get(v_r_931_, 4);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_r_931_, 3);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_r_931_, 0);
lean_dec(v_unused_955_);
v___x_940_ = v_r_931_;
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_v_938_);
lean_inc(v_k_937_);
lean_dec(v_r_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_unsigned_to_nat(3u);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_l_914_);
lean_ctor_set(v___x_940_, 3, v_l_914_);
lean_ctor_set(v___x_940_, 2, v_v_933_);
lean_ctor_set(v___x_940_, 1, v_k_932_);
lean_ctor_set(v___x_940_, 0, v___x_828_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_l_914_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_l_914_);
v___x_944_ = v_reuseFailAlloc_951_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v_l_914_);
lean_ctor_set(v___x_935_, 2, v_v_820_);
lean_ctor_set(v___x_935_, 1, v_k_819_);
lean_ctor_set(v___x_935_, 0, v___x_828_);
v___x_946_ = v___x_935_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_l_914_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_l_914_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v___x_946_);
lean_ctor_set(v___x_824_, 3, v___x_944_);
lean_ctor_set(v___x_824_, 2, v_v_938_);
lean_ctor_set(v___x_824_, 1, v_k_937_);
lean_ctor_set(v___x_824_, 0, v___x_942_);
v___x_948_ = v___x_824_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_938_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_unsigned_to_nat(2u);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_r_931_);
lean_ctor_set(v___x_824_, 3, v_impl_827_);
lean_ctor_set(v___x_824_, 0, v___x_960_);
v___x_962_ = v___x_824_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_impl_827_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_r_931_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
case 1:
{
lean_object* v___x_965_; 
lean_dec(v_v_820_);
lean_dec(v_k_819_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 2, v_v_816_);
lean_ctor_set(v___x_824_, 1, v_k_815_);
v___x_965_ = v___x_824_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_size_818_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_k_815_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_v_816_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_l_821_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_r_822_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
default: 
{
lean_object* v_impl_967_; lean_object* v___x_968_; 
lean_dec(v_size_818_);
v_impl_967_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_k_815_, v_v_816_, v_r_822_);
v___x_968_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_821_) == 0)
{
lean_object* v_size_969_; lean_object* v_size_970_; lean_object* v_k_971_; lean_object* v_v_972_; lean_object* v_l_973_; lean_object* v_r_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_size_969_ = lean_ctor_get(v_l_821_, 0);
v_size_970_ = lean_ctor_get(v_impl_967_, 0);
lean_inc(v_size_970_);
v_k_971_ = lean_ctor_get(v_impl_967_, 1);
lean_inc(v_k_971_);
v_v_972_ = lean_ctor_get(v_impl_967_, 2);
lean_inc(v_v_972_);
v_l_973_ = lean_ctor_get(v_impl_967_, 3);
lean_inc(v_l_973_);
v_r_974_ = lean_ctor_get(v_impl_967_, 4);
lean_inc(v_r_974_);
v___x_975_ = lean_unsigned_to_nat(3u);
v___x_976_ = lean_nat_mul(v___x_975_, v_size_969_);
v___x_977_ = lean_nat_dec_lt(v___x_976_, v_size_970_);
lean_dec(v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v_r_974_);
lean_dec(v_l_973_);
lean_dec(v_v_972_);
lean_dec(v_k_971_);
v___x_978_ = lean_nat_add(v___x_968_, v_size_969_);
v___x_979_ = lean_nat_add(v___x_978_, v_size_970_);
lean_dec(v_size_970_);
lean_dec(v___x_978_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_impl_967_);
lean_ctor_set(v___x_824_, 0, v___x_979_);
v___x_981_ = v___x_824_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_l_821_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_impl_967_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1046_; 
v_isSharedCheck_1046_ = !lean_is_exclusive(v_impl_967_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; lean_object* v_unused_1048_; lean_object* v_unused_1049_; lean_object* v_unused_1050_; lean_object* v_unused_1051_; 
v_unused_1047_ = lean_ctor_get(v_impl_967_, 4);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_impl_967_, 3);
lean_dec(v_unused_1048_);
v_unused_1049_ = lean_ctor_get(v_impl_967_, 2);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_impl_967_, 1);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_impl_967_, 0);
lean_dec(v_unused_1051_);
v___x_984_ = v_impl_967_;
v_isShared_985_ = v_isSharedCheck_1046_;
goto v_resetjp_983_;
}
else
{
lean_dec(v_impl_967_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1046_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_size_986_; lean_object* v_k_987_; lean_object* v_v_988_; lean_object* v_l_989_; lean_object* v_r_990_; lean_object* v_size_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_size_986_ = lean_ctor_get(v_l_973_, 0);
v_k_987_ = lean_ctor_get(v_l_973_, 1);
v_v_988_ = lean_ctor_get(v_l_973_, 2);
v_l_989_ = lean_ctor_get(v_l_973_, 3);
v_r_990_ = lean_ctor_get(v_l_973_, 4);
v_size_991_ = lean_ctor_get(v_r_974_, 0);
v___x_992_ = lean_unsigned_to_nat(2u);
v___x_993_ = lean_nat_mul(v___x_992_, v_size_991_);
v___x_994_ = lean_nat_dec_lt(v_size_986_, v___x_993_);
lean_dec(v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1022_; 
lean_inc(v_r_990_);
lean_inc(v_l_989_);
lean_inc(v_v_988_);
lean_inc(v_k_987_);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_l_973_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; 
v_unused_1023_ = lean_ctor_get(v_l_973_, 4);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_l_973_, 3);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_l_973_, 2);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_l_973_, 1);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_l_973_, 0);
lean_dec(v_unused_1027_);
v___x_996_ = v_l_973_;
v_isShared_997_ = v_isSharedCheck_1022_;
goto v_resetjp_995_;
}
else
{
lean_dec(v_l_973_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1022_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1012_; 
v___x_998_ = lean_nat_add(v___x_968_, v_size_969_);
v___x_999_ = lean_nat_add(v___x_998_, v_size_970_);
lean_dec(v_size_970_);
if (lean_obj_tag(v_l_989_) == 0)
{
lean_object* v_size_1020_; 
v_size_1020_ = lean_ctor_get(v_l_989_, 0);
lean_inc(v_size_1020_);
v___y_1012_ = v_size_1020_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_unsigned_to_nat(0u);
v___y_1012_ = v___x_1021_;
goto v___jp_1011_;
}
v___jp_1000_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_nat_add(v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 4, v_r_974_);
lean_ctor_set(v___x_996_, 3, v_r_990_);
lean_ctor_set(v___x_996_, 2, v_v_972_);
lean_ctor_set(v___x_996_, 1, v_k_971_);
lean_ctor_set(v___x_996_, 0, v___x_1004_);
v___x_1006_ = v___x_996_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_971_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_972_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_r_990_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_r_974_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 4, v___x_1006_);
lean_ctor_set(v___x_984_, 3, v___y_1001_);
lean_ctor_set(v___x_984_, 2, v_v_988_);
lean_ctor_set(v___x_984_, 1, v_k_987_);
lean_ctor_set(v___x_984_, 0, v___x_999_);
v___x_1008_ = v___x_984_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_987_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_v_988_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v___y_1001_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_nat_add(v___x_998_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec(v___x_998_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_l_989_);
lean_ctor_set(v___x_824_, 0, v___x_1013_);
v___x_1015_ = v___x_824_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_l_821_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_l_989_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_nat_add(v___x_968_, v_size_991_);
if (lean_obj_tag(v_r_990_) == 0)
{
lean_object* v_size_1017_; 
v_size_1017_ = lean_ctor_get(v_r_990_, 0);
lean_inc(v_size_1017_);
v___y_1001_ = v___x_1015_;
v___y_1002_ = v___x_1016_;
v___y_1003_ = v_size_1017_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___y_1001_ = v___x_1015_;
v___y_1002_ = v___x_1016_;
v___y_1003_ = v___x_1018_;
goto v___jp_1000_;
}
}
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_del_object(v___x_824_);
v___x_1028_ = lean_nat_add(v___x_968_, v_size_969_);
v___x_1029_ = lean_nat_add(v___x_1028_, v_size_970_);
lean_dec(v_size_970_);
v___x_1030_ = lean_nat_add(v___x_1028_, v_size_986_);
lean_dec(v___x_1028_);
lean_inc_ref(v_l_821_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 4, v_l_973_);
lean_ctor_set(v___x_984_, 3, v_l_821_);
lean_ctor_set(v___x_984_, 2, v_v_820_);
lean_ctor_set(v___x_984_, 1, v_k_819_);
lean_ctor_set(v___x_984_, 0, v___x_1030_);
v___x_1032_ = v___x_984_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_l_821_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_l_973_);
v___x_1032_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_isSharedCheck_1039_ = !lean_is_exclusive(v_l_821_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; lean_object* v_unused_1041_; lean_object* v_unused_1042_; lean_object* v_unused_1043_; lean_object* v_unused_1044_; 
v_unused_1040_ = lean_ctor_get(v_l_821_, 4);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_l_821_, 3);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_l_821_, 2);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_l_821_, 1);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_l_821_, 0);
lean_dec(v_unused_1044_);
v___x_1034_ = v_l_821_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v_l_821_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v_r_974_);
lean_ctor_set(v___x_1034_, 3, v___x_1032_);
lean_ctor_set(v___x_1034_, 2, v_v_972_);
lean_ctor_set(v___x_1034_, 1, v_k_971_);
lean_ctor_set(v___x_1034_, 0, v___x_1029_);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_k_971_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_v_972_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v_r_974_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1052_; 
v_l_1052_ = lean_ctor_get(v_impl_967_, 3);
lean_inc(v_l_1052_);
if (lean_obj_tag(v_l_1052_) == 0)
{
lean_object* v_r_1053_; lean_object* v_k_1054_; lean_object* v_v_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1078_; 
v_r_1053_ = lean_ctor_get(v_impl_967_, 4);
v_k_1054_ = lean_ctor_get(v_impl_967_, 1);
v_v_1055_ = lean_ctor_get(v_impl_967_, 2);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_impl_967_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; lean_object* v_unused_1080_; 
v_unused_1079_ = lean_ctor_get(v_impl_967_, 3);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_impl_967_, 0);
lean_dec(v_unused_1080_);
v___x_1057_ = v_impl_967_;
v_isShared_1058_ = v_isSharedCheck_1078_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_r_1053_);
lean_inc(v_v_1055_);
lean_inc(v_k_1054_);
lean_dec(v_impl_967_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1078_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_k_1059_; lean_object* v_v_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1074_; 
v_k_1059_ = lean_ctor_get(v_l_1052_, 1);
v_v_1060_ = lean_ctor_get(v_l_1052_, 2);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_l_1052_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; lean_object* v_unused_1076_; lean_object* v_unused_1077_; 
v_unused_1075_ = lean_ctor_get(v_l_1052_, 4);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_l_1052_, 3);
lean_dec(v_unused_1076_);
v_unused_1077_ = lean_ctor_get(v_l_1052_, 0);
lean_dec(v_unused_1077_);
v___x_1062_ = v_l_1052_;
v_isShared_1063_ = v_isSharedCheck_1074_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_v_1060_);
lean_inc(v_k_1059_);
lean_dec(v_l_1052_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1074_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1053_, 2);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v_r_1053_);
lean_ctor_set(v___x_1062_, 3, v_r_1053_);
lean_ctor_set(v___x_1062_, 2, v_v_820_);
lean_ctor_set(v___x_1062_, 1, v_k_819_);
lean_ctor_set(v___x_1062_, 0, v___x_968_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_r_1053_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_r_1053_);
v___x_1066_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
lean_inc(v_r_1053_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 3, v_r_1053_);
lean_ctor_set(v___x_1057_, 0, v___x_968_);
v___x_1068_ = v___x_1057_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_k_1054_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_v_1055_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v_r_1053_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v_r_1053_);
v___x_1068_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v___x_1068_);
lean_ctor_set(v___x_824_, 3, v___x_1066_);
lean_ctor_set(v___x_824_, 2, v_v_1060_);
lean_ctor_set(v___x_824_, 1, v_k_1059_);
lean_ctor_set(v___x_824_, 0, v___x_1064_);
v___x_1070_ = v___x_824_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_k_1059_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_v_1060_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
else
{
lean_object* v_r_1081_; 
v_r_1081_ = lean_ctor_get(v_impl_967_, 4);
lean_inc(v_r_1081_);
if (lean_obj_tag(v_r_1081_) == 0)
{
lean_object* v_k_1082_; lean_object* v_v_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1094_; 
v_k_1082_ = lean_ctor_get(v_impl_967_, 1);
v_v_1083_ = lean_ctor_get(v_impl_967_, 2);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_impl_967_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; 
v_unused_1095_ = lean_ctor_get(v_impl_967_, 4);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_impl_967_, 3);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_impl_967_, 0);
lean_dec(v_unused_1097_);
v___x_1085_ = v_impl_967_;
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_v_1083_);
lean_inc(v_k_1082_);
lean_dec(v_impl_967_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_unsigned_to_nat(3u);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 4, v_l_1052_);
lean_ctor_set(v___x_1085_, 2, v_v_820_);
lean_ctor_set(v___x_1085_, 1, v_k_819_);
lean_ctor_set(v___x_1085_, 0, v___x_968_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_l_1052_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_l_1052_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_r_1081_);
lean_ctor_set(v___x_824_, 3, v___x_1089_);
lean_ctor_set(v___x_824_, 2, v_v_1083_);
lean_ctor_set(v___x_824_, 1, v_k_1082_);
lean_ctor_set(v___x_824_, 0, v___x_1087_);
v___x_1091_ = v___x_824_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_k_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_v_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_r_1081_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_unsigned_to_nat(2u);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 4, v_impl_967_);
lean_ctor_set(v___x_824_, 3, v_r_1081_);
lean_ctor_set(v___x_824_, 0, v___x_1098_);
v___x_1100_ = v___x_824_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_r_1081_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_impl_967_);
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
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v_k_815_);
lean_ctor_set(v___x_1104_, 2, v_v_816_);
lean_ctor_set(v___x_1104_, 3, v_t_817_);
lean_ctor_set(v___x_1104_, 4, v_t_817_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(lean_object* v_t_1105_, lean_object* v_k_1106_){
_start:
{
if (lean_obj_tag(v_t_1105_) == 0)
{
lean_object* v_k_1107_; lean_object* v_v_1108_; lean_object* v_l_1109_; lean_object* v_r_1110_; uint8_t v___x_1111_; 
v_k_1107_ = lean_ctor_get(v_t_1105_, 1);
v_v_1108_ = lean_ctor_get(v_t_1105_, 2);
v_l_1109_ = lean_ctor_get(v_t_1105_, 3);
v_r_1110_ = lean_ctor_get(v_t_1105_, 4);
v___x_1111_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1106_, v_k_1107_);
switch(v___x_1111_)
{
case 0:
{
v_t_1105_ = v_l_1109_;
goto _start;
}
case 1:
{
lean_object* v___x_1113_; 
lean_inc(v_v_1108_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_v_1108_);
return v___x_1113_;
}
default: 
{
v_t_1105_ = v_r_1110_;
goto _start;
}
}
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_box(0);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg___boxed(lean_object* v_t_1116_, lean_object* v_k_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(v_t_1116_, v_k_1117_);
lean_dec(v_k_1117_);
lean_dec(v_t_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(lean_object* v_self_1122_, lean_object* v_as_1123_, size_t v_i_1124_, size_t v_stop_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_usize_dec_eq(v_i_1124_, v_stop_1125_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v_name_1131_; lean_object* v_kind_1132_; lean_object* v___x_1133_; 
v___x_1130_ = lean_array_uget_borrowed(v_as_1123_, v_i_1124_);
v_name_1131_ = lean_ctor_get(v___x_1130_, 1);
v_kind_1132_ = lean_ctor_get(v___x_1130_, 2);
v___x_1133_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(v_b_1126_, v_name_1131_);
if (lean_obj_tag(v___x_1133_) == 1)
{
lean_object* v_val_1134_; lean_object* v_baseName_1135_; lean_object* v_kind_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_b_1126_);
v_val_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1134_);
lean_dec_ref(v___x_1133_);
v_baseName_1135_ = lean_ctor_get(v_self_1122_, 1);
lean_inc(v_baseName_1135_);
lean_dec_ref(v_self_1122_);
v_kind_1136_ = lean_ctor_get(v_val_1134_, 2);
lean_inc(v_kind_1136_);
lean_dec(v_val_1134_);
v___x_1137_ = l_Lean_Name_toString(v_baseName_1135_, v___x_1129_);
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__0));
v___x_1139_ = lean_string_append(v___x_1137_, v___x_1138_);
v___x_1140_ = 1;
lean_inc(v_name_1131_);
v___x_1141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1131_, v___x_1140_);
v___x_1142_ = lean_string_append(v___x_1139_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__1));
v___x_1144_ = lean_string_append(v___x_1142_, v___x_1143_);
v___x_1145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1136_, v___x_1140_);
v___x_1146_ = lean_string_append(v___x_1144_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___closed__2));
v___x_1148_ = lean_string_append(v___x_1146_, v___x_1147_);
lean_inc(v_kind_1132_);
v___x_1149_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1132_, v___x_1140_);
v___x_1150_ = lean_string_append(v___x_1148_, v___x_1149_);
lean_dec_ref(v___x_1149_);
v___x_1151_ = ((lean_object*)(l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg___closed__1));
v___x_1152_ = lean_string_append(v___x_1150_, v___x_1151_);
v___x_1153_ = 3;
v___x_1154_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set_uint8(v___x_1154_, sizeof(void*)*1, v___x_1153_);
v___x_1155_ = lean_array_get_size(v___y_1127_);
v___x_1156_ = lean_array_push(v___y_1127_, v___x_1154_);
v___x_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; 
lean_dec(v___x_1133_);
lean_inc(v___x_1130_);
lean_inc(v_name_1131_);
v___x_1158_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_name_1131_, v___x_1130_, v_b_1126_);
v___x_1159_ = ((size_t)1ULL);
v___x_1160_ = lean_usize_add(v_i_1124_, v___x_1159_);
v_i_1124_ = v___x_1160_;
v_b_1126_ = v___x_1158_;
goto _start;
}
}
else
{
lean_object* v___x_1162_; 
lean_dec_ref(v_self_1122_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1126_);
lean_ctor_set(v___x_1162_, 1, v___y_1127_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13___boxed(lean_object* v_self_1163_, lean_object* v_as_1164_, lean_object* v_i_1165_, lean_object* v_stop_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_i_boxed_1170_; size_t v_stop_boxed_1171_; lean_object* v_res_1172_; 
v_i_boxed_1170_ = lean_unbox_usize(v_i_1165_);
lean_dec(v_i_1165_);
v_stop_boxed_1171_ = lean_unbox_usize(v_stop_1166_);
lean_dec(v_stop_1166_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(v_self_1163_, v_as_1164_, v_i_boxed_1170_, v_stop_boxed_1171_, v_b_1167_, v___y_1168_);
lean_dec_ref(v_as_1164_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv(lean_object* v_self_1178_, lean_object* v_env_1179_, lean_object* v_opts_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___f_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1183_ = l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_;
lean_inc_ref(v_opts_1180_);
lean_inc_ref(v_env_1179_);
v___f_1184_ = lean_alloc_closure((void*)(l_Lake_Package_loadFromEnv___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1184_, 0, v_env_1179_);
lean_closure_set(v___f_1184_, 1, v_opts_1180_);
lean_closure_set(v___f_1184_, 2, v___x_1183_);
v___x_1185_ = l_Lake_targetAttr;
lean_inc_ref(v_env_1179_);
v___x_1186_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(v_env_1179_, v___x_1185_, v___f_1184_);
v___x_1187_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(v___x_1186_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v_toArray_1189_; size_t v_sz_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
v_toArray_1189_ = lean_ctor_get(v_a_1188_, 1);
v_sz_1190_ = lean_array_size(v_toArray_1189_);
v___x_1191_ = ((size_t)0ULL);
lean_inc_ref(v_toArray_1189_);
lean_inc_ref(v_self_1178_);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__4(v_self_1178_, v_sz_1190_, v___x_1191_, v_toArray_1189_, v_a_1181_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1483_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_a_1194_ = lean_ctor_get(v___x_1192_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1483_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1483_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v_lintDriver_1250_; lean_object* v___y_1251_; lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v_testDriver_1273_; lean_object* v___y_1274_; lean_object* v_a_1330_; lean_object* v_a_1331_; lean_object* v___y_1464_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1262_ = l_Lake_instTypeNameScriptFn_unsafe__1;
lean_inc_ref(v_self_1178_);
lean_inc_ref(v_opts_1180_);
lean_inc_ref(v_env_1179_);
v___f_1263_ = lean_alloc_closure((void*)(l_Lake_Package_loadFromEnv___lam__1___boxed), 7, 4);
lean_closure_set(v___f_1263_, 0, v_env_1179_);
lean_closure_set(v___f_1263_, 1, v_opts_1180_);
lean_closure_set(v___f_1263_, 2, v___x_1262_);
lean_closure_set(v___f_1263_, 3, v_self_1178_);
v___x_1264_ = lean_box(1);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_array_get_size(v_a_1193_);
v___x_1477_ = lean_nat_dec_lt(v___x_1265_, v___x_1476_);
if (v___x_1477_ == 0)
{
v_a_1330_ = v___x_1264_;
v_a_1331_ = v_a_1194_;
goto v___jp_1329_;
}
else
{
uint8_t v___x_1478_; 
v___x_1478_ = lean_nat_dec_le(v___x_1476_, v___x_1476_);
if (v___x_1478_ == 0)
{
if (v___x_1477_ == 0)
{
v_a_1330_ = v___x_1264_;
v_a_1331_ = v_a_1194_;
goto v___jp_1329_;
}
else
{
size_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_usize_of_nat(v___x_1476_);
lean_inc_ref(v_self_1178_);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(v_self_1178_, v_a_1193_, v___x_1191_, v___x_1479_, v___x_1264_, v_a_1194_);
v___y_1464_ = v___x_1480_;
goto v___jp_1463_;
}
}
else
{
size_t v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_usize_of_nat(v___x_1476_);
lean_inc_ref(v_self_1178_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_loadFromEnv_spec__13(v_self_1178_, v_a_1193_, v___x_1191_, v___x_1481_, v___x_1264_, v_a_1194_);
v___y_1464_ = v___x_1482_;
goto v___jp_1463_;
}
}
v___jp_1198_:
{
lean_object* v_wsIdx_1208_; lean_object* v_baseName_1209_; lean_object* v_keyName_1210_; lean_object* v_origName_1211_; lean_object* v_dir_1212_; lean_object* v_relDir_1213_; lean_object* v_config_1214_; lean_object* v_configFile_1215_; lean_object* v_relConfigFile_1216_; lean_object* v_relManifestFile_1217_; lean_object* v_scope_1218_; lean_object* v_remoteUrl_1219_; lean_object* v_buildArchive_1220_; lean_object* v_inputsRef_x3f_1221_; lean_object* v_outputsRef_x3f_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1232_; 
v_wsIdx_1208_ = lean_ctor_get(v_self_1178_, 0);
v_baseName_1209_ = lean_ctor_get(v_self_1178_, 1);
v_keyName_1210_ = lean_ctor_get(v_self_1178_, 2);
v_origName_1211_ = lean_ctor_get(v_self_1178_, 3);
v_dir_1212_ = lean_ctor_get(v_self_1178_, 4);
v_relDir_1213_ = lean_ctor_get(v_self_1178_, 5);
v_config_1214_ = lean_ctor_get(v_self_1178_, 6);
v_configFile_1215_ = lean_ctor_get(v_self_1178_, 7);
v_relConfigFile_1216_ = lean_ctor_get(v_self_1178_, 8);
v_relManifestFile_1217_ = lean_ctor_get(v_self_1178_, 9);
v_scope_1218_ = lean_ctor_get(v_self_1178_, 10);
v_remoteUrl_1219_ = lean_ctor_get(v_self_1178_, 11);
v_buildArchive_1220_ = lean_ctor_get(v_self_1178_, 19);
v_inputsRef_x3f_1221_ = lean_ctor_get(v_self_1178_, 22);
v_outputsRef_x3f_1222_ = lean_ctor_get(v_self_1178_, 23);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_self_1178_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; lean_object* v_unused_1238_; lean_object* v_unused_1239_; lean_object* v_unused_1240_; lean_object* v_unused_1241_; 
v_unused_1233_ = lean_ctor_get(v_self_1178_, 21);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_self_1178_, 20);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_self_1178_, 18);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_self_1178_, 17);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_self_1178_, 16);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_self_1178_, 15);
lean_dec(v_unused_1238_);
v_unused_1239_ = lean_ctor_get(v_self_1178_, 14);
lean_dec(v_unused_1239_);
v_unused_1240_ = lean_ctor_get(v_self_1178_, 13);
lean_dec(v_unused_1240_);
v_unused_1241_ = lean_ctor_get(v_self_1178_, 12);
lean_dec(v_unused_1241_);
v___x_1224_ = v_self_1178_;
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_outputsRef_x3f_1222_);
lean_inc(v_inputsRef_x3f_1221_);
lean_inc(v_buildArchive_1220_);
lean_inc(v_remoteUrl_1219_);
lean_inc(v_scope_1218_);
lean_inc(v_relManifestFile_1217_);
lean_inc(v_relConfigFile_1216_);
lean_inc(v_configFile_1215_);
lean_inc(v_config_1214_);
lean_inc(v_relDir_1213_);
lean_inc(v_dir_1212_);
lean_inc(v_origName_1211_);
lean_inc(v_keyName_1210_);
lean_inc(v_baseName_1209_);
lean_inc(v_wsIdx_1208_);
lean_dec(v_self_1178_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 21, v___y_1205_);
lean_ctor_set(v___x_1224_, 20, v___y_1201_);
lean_ctor_set(v___x_1224_, 18, v___y_1203_);
lean_ctor_set(v___x_1224_, 17, v___y_1202_);
lean_ctor_set(v___x_1224_, 16, v___y_1204_);
lean_ctor_set(v___x_1224_, 15, v___y_1199_);
lean_ctor_set(v___x_1224_, 14, v___y_1206_);
lean_ctor_set(v___x_1224_, 13, v_a_1193_);
lean_ctor_set(v___x_1224_, 12, v___y_1200_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_wsIdx_1208_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_baseName_1209_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_keyName_1210_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_origName_1211_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_dir_1212_);
lean_ctor_set(v_reuseFailAlloc_1231_, 5, v_relDir_1213_);
lean_ctor_set(v_reuseFailAlloc_1231_, 6, v_config_1214_);
lean_ctor_set(v_reuseFailAlloc_1231_, 7, v_configFile_1215_);
lean_ctor_set(v_reuseFailAlloc_1231_, 8, v_relConfigFile_1216_);
lean_ctor_set(v_reuseFailAlloc_1231_, 9, v_relManifestFile_1217_);
lean_ctor_set(v_reuseFailAlloc_1231_, 10, v_scope_1218_);
lean_ctor_set(v_reuseFailAlloc_1231_, 11, v_remoteUrl_1219_);
lean_ctor_set(v_reuseFailAlloc_1231_, 12, v___y_1200_);
lean_ctor_set(v_reuseFailAlloc_1231_, 13, v_a_1193_);
lean_ctor_set(v_reuseFailAlloc_1231_, 14, v___y_1206_);
lean_ctor_set(v_reuseFailAlloc_1231_, 15, v___y_1199_);
lean_ctor_set(v_reuseFailAlloc_1231_, 16, v___y_1204_);
lean_ctor_set(v_reuseFailAlloc_1231_, 17, v___y_1202_);
lean_ctor_set(v_reuseFailAlloc_1231_, 18, v___y_1203_);
lean_ctor_set(v_reuseFailAlloc_1231_, 19, v_buildArchive_1220_);
lean_ctor_set(v_reuseFailAlloc_1231_, 20, v___y_1201_);
lean_ctor_set(v_reuseFailAlloc_1231_, 21, v___y_1205_);
lean_ctor_set(v_reuseFailAlloc_1231_, 22, v_inputsRef_x3f_1221_);
lean_ctor_set(v_reuseFailAlloc_1231_, 23, v_outputsRef_x3f_1222_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___y_1207_);
lean_ctor_set(v___x_1196_, 0, v___x_1227_);
v___x_1229_ = v___x_1196_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___y_1207_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
v___jp_1242_:
{
lean_object* v_config_1252_; lean_object* v_manifestFile_1253_; 
v_config_1252_ = lean_ctor_get(v_self_1178_, 6);
v_manifestFile_1253_ = lean_ctor_get(v_config_1252_, 2);
if (lean_obj_tag(v_manifestFile_1253_) == 0)
{
v___y_1199_ = v___y_1244_;
v___y_1200_ = v___y_1243_;
v___y_1201_ = v___y_1245_;
v___y_1202_ = v___y_1246_;
v___y_1203_ = v___y_1247_;
v___y_1204_ = v___y_1248_;
v___y_1205_ = v_lintDriver_1250_;
v___y_1206_ = v___y_1249_;
v___y_1207_ = v___y_1251_;
goto v___jp_1198_;
}
else
{
lean_object* v_baseName_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_baseName_1254_ = lean_ctor_get(v_self_1178_, 1);
v___x_1255_ = 0;
lean_inc(v_baseName_1254_);
v___x_1256_ = l_Lean_Name_toString(v_baseName_1254_, v___x_1255_);
v___x_1257_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__0));
v___x_1258_ = lean_string_append(v___x_1256_, v___x_1257_);
v___x_1259_ = 2;
v___x_1260_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set_uint8(v___x_1260_, sizeof(void*)*1, v___x_1259_);
v___x_1261_ = lean_array_push(v___y_1251_, v___x_1260_);
v___y_1199_ = v___y_1244_;
v___y_1200_ = v___y_1243_;
v___y_1201_ = v___y_1245_;
v___y_1202_ = v___y_1246_;
v___y_1203_ = v___y_1247_;
v___y_1204_ = v___y_1248_;
v___y_1205_ = v_lintDriver_1250_;
v___y_1206_ = v___y_1249_;
v___y_1207_ = v___x_1261_;
goto v___jp_1198_;
}
}
v___jp_1266_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; size_t v_sz_1277_; lean_object* v___x_1278_; 
v___x_1275_ = l_Lake_lintDriverAttr;
v___x_1276_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1275_, v_env_1179_);
v_sz_1277_ = lean_array_size(v___x_1276_);
lean_inc_ref(v_self_1178_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__11(v_a_1188_, v___y_1271_, v_self_1178_, v_sz_1277_, v___x_1191_, v___x_1276_, v___y_1274_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1319_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_a_1280_ = lean_ctor_get(v___x_1278_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1282_ = v___x_1278_;
v_isShared_1283_ = v_isSharedCheck_1319_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1319_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_unsigned_to_nat(1u);
v___x_1285_ = lean_array_get_size(v_a_1279_);
v___x_1286_ = lean_nat_dec_lt(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_lt(v___x_1265_, v___x_1285_);
if (v___x_1287_ == 0)
{
lean_object* v_config_1288_; lean_object* v_lintDriver_1289_; 
lean_del_object(v___x_1282_);
lean_dec(v_a_1279_);
v_config_1288_ = lean_ctor_get(v_self_1178_, 6);
v_lintDriver_1289_ = lean_ctor_get(v_config_1288_, 15);
lean_inc_ref(v_lintDriver_1289_);
v___y_1243_ = v___y_1268_;
v___y_1244_ = v___y_1267_;
v___y_1245_ = v_testDriver_1273_;
v___y_1246_ = v___y_1269_;
v___y_1247_ = v___y_1270_;
v___y_1248_ = v___y_1271_;
v___y_1249_ = v___y_1272_;
v_lintDriver_1250_ = v_lintDriver_1289_;
v___y_1251_ = v_a_1280_;
goto v___jp_1242_;
}
else
{
lean_object* v_config_1290_; lean_object* v_baseName_1291_; lean_object* v_lintDriver_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_config_1290_ = lean_ctor_get(v_self_1178_, 6);
v_baseName_1291_ = lean_ctor_get(v_self_1178_, 1);
v_lintDriver_1292_ = lean_ctor_get(v_config_1290_, 15);
v___x_1293_ = lean_string_utf8_byte_size(v_lintDriver_1292_);
v___x_1294_ = lean_nat_dec_eq(v___x_1293_, v___x_1265_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_inc(v_baseName_1291_);
lean_dec(v_a_1279_);
lean_dec_ref(v_testDriver_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec_ref(v_self_1178_);
v___x_1295_ = l_Lean_Name_toString(v_baseName_1291_, v___x_1294_);
v___x_1296_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__1));
v___x_1297_ = lean_string_append(v___x_1295_, v___x_1296_);
v___x_1298_ = 3;
v___x_1299_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*1, v___x_1298_);
v___x_1300_ = lean_array_get_size(v_a_1280_);
v___x_1301_ = lean_array_push(v_a_1280_, v___x_1299_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 1);
lean_ctor_set(v___x_1282_, 1, v___x_1301_);
lean_ctor_set(v___x_1282_, 0, v___x_1300_);
v___x_1303_ = v___x_1282_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_del_object(v___x_1282_);
v___x_1305_ = lean_array_fget(v_a_1279_, v___x_1265_);
lean_dec(v_a_1279_);
v___x_1306_ = l_Lean_Name_toString(v___x_1305_, v___x_1294_);
v___y_1243_ = v___y_1268_;
v___y_1244_ = v___y_1267_;
v___y_1245_ = v_testDriver_1273_;
v___y_1246_ = v___y_1269_;
v___y_1247_ = v___y_1270_;
v___y_1248_ = v___y_1271_;
v___y_1249_ = v___y_1272_;
v_lintDriver_1250_ = v___x_1306_;
v___y_1251_ = v_a_1280_;
goto v___jp_1242_;
}
}
}
else
{
lean_object* v_baseName_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_dec(v_a_1279_);
lean_dec_ref(v_testDriver_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
v_baseName_1307_ = lean_ctor_get(v_self_1178_, 1);
lean_inc(v_baseName_1307_);
lean_dec_ref(v_self_1178_);
v___x_1308_ = 0;
v___x_1309_ = l_Lean_Name_toString(v_baseName_1307_, v___x_1308_);
v___x_1310_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__2));
v___x_1311_ = lean_string_append(v___x_1309_, v___x_1310_);
v___x_1312_ = 3;
v___x_1313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*1, v___x_1312_);
v___x_1314_ = lean_array_get_size(v_a_1280_);
v___x_1315_ = lean_array_push(v_a_1280_, v___x_1313_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 1);
lean_ctor_set(v___x_1282_, 1, v___x_1315_);
lean_ctor_set(v___x_1282_, 0, v___x_1314_);
v___x_1317_ = v___x_1282_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_testDriver_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec_ref(v_self_1178_);
v_a_1320_ = lean_ctor_get(v___x_1278_, 0);
v_a_1321_ = lean_ctor_get(v___x_1278_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1278_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_inc(v_a_1320_);
lean_dec(v___x_1278_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1320_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
v___jp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; size_t v_sz_1334_; lean_object* v___x_1335_; 
v___x_1332_ = l_Lake_defaultTargetAttr;
lean_inc_ref(v_env_1179_);
v___x_1333_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1332_, v_env_1179_);
v_sz_1334_ = lean_array_size(v___x_1333_);
lean_inc_ref(v_self_1178_);
lean_inc(v_a_1188_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__6(v_a_1188_, v_self_1178_, v_sz_1334_, v___x_1191_, v___x_1333_, v_a_1331_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_a_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
v_a_1337_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1335_);
v___x_1338_ = l_Lake_scriptAttr;
lean_inc_ref(v_env_1179_);
v___x_1339_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(v_env_1179_, v___x_1338_, v___f_1263_, v_a_1337_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; size_t v_sz_1344_; lean_object* v___x_1345_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
v_a_1341_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1339_);
v___x_1342_ = l_Lake_defaultScriptAttr;
lean_inc_ref(v_env_1179_);
v___x_1343_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1342_, v_env_1179_);
v_sz_1344_ = lean_array_size(v___x_1343_);
lean_inc_ref(v_self_1178_);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__8(v_a_1340_, v_self_1178_, v_sz_1344_, v___x_1191_, v___x_1343_, v_a_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; size_t v_sz_1350_; lean_object* v___x_1351_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
v_a_1347_ = lean_ctor_get(v___x_1345_, 1);
lean_inc(v_a_1347_);
lean_dec_ref(v___x_1345_);
v___x_1348_ = l_Lake_postUpdateAttr;
lean_inc_ref(v_env_1179_);
v___x_1349_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1348_, v_env_1179_);
v_sz_1350_ = lean_array_size(v___x_1349_);
lean_inc_ref(v_self_1178_);
lean_inc_ref(v_env_1179_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__9(v_env_1179_, v_opts_1180_, v_self_1178_, v_sz_1350_, v___x_1191_, v___x_1349_, v_a_1347_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1426_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_a_1353_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1355_ = v___x_1351_;
v_isShared_1356_ = v_isSharedCheck_1426_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1426_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; size_t v_sz_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1357_ = l_Lake_packageDepAttr;
lean_inc_ref(v_env_1179_);
v___x_1358_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1357_, v_env_1179_);
v_sz_1359_ = lean_array_size(v___x_1358_);
lean_inc_ref(v_env_1179_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__10(v_env_1179_, v_opts_1180_, v_sz_1359_, v___x_1191_, v___x_1358_);
lean_dec_ref(v_opts_1180_);
v___x_1361_ = l_IO_ofExcept___at___00Lake_Package_loadFromEnv_spec__2___redArg(v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; size_t v_sz_1365_; lean_object* v___x_1366_; 
lean_del_object(v___x_1355_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1361_);
v___x_1363_ = l_Lake_testDriverAttr;
lean_inc_ref(v_env_1179_);
v___x_1364_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1363_, v_env_1179_);
v_sz_1365_ = lean_array_size(v___x_1364_);
lean_inc_ref(v_self_1178_);
lean_inc(v_a_1188_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Package_loadFromEnv_spec__12(v_a_1188_, v_a_1340_, v_self_1178_, v_sz_1365_, v___x_1191_, v___x_1364_, v_a_1353_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1407_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_a_1368_ = lean_ctor_get(v___x_1366_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1407_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1407_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = lean_unsigned_to_nat(1u);
v___x_1373_ = lean_array_get_size(v_a_1367_);
v___x_1374_ = lean_nat_dec_lt(v___x_1372_, v___x_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_nat_dec_lt(v___x_1265_, v___x_1373_);
if (v___x_1375_ == 0)
{
lean_object* v_config_1376_; lean_object* v_testDriver_1377_; 
lean_del_object(v___x_1370_);
lean_dec(v_a_1367_);
v_config_1376_ = lean_ctor_get(v_self_1178_, 6);
v_testDriver_1377_ = lean_ctor_get(v_config_1376_, 13);
lean_inc_ref(v_testDriver_1377_);
v___y_1267_ = v_a_1336_;
v___y_1268_ = v_a_1362_;
v___y_1269_ = v_a_1346_;
v___y_1270_ = v_a_1352_;
v___y_1271_ = v_a_1340_;
v___y_1272_ = v_a_1330_;
v_testDriver_1273_ = v_testDriver_1377_;
v___y_1274_ = v_a_1368_;
goto v___jp_1266_;
}
else
{
lean_object* v_config_1378_; lean_object* v_baseName_1379_; lean_object* v_testDriver_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_config_1378_ = lean_ctor_get(v_self_1178_, 6);
v_baseName_1379_ = lean_ctor_get(v_self_1178_, 1);
v_testDriver_1380_ = lean_ctor_get(v_config_1378_, 13);
v___x_1381_ = lean_string_utf8_byte_size(v_testDriver_1380_);
v___x_1382_ = lean_nat_dec_eq(v___x_1381_, v___x_1265_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_inc(v_baseName_1379_);
lean_dec(v_a_1367_);
lean_dec(v_a_1362_);
lean_dec(v_a_1352_);
lean_dec(v_a_1346_);
lean_dec(v_a_1340_);
lean_dec(v_a_1336_);
lean_dec(v_a_1330_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v___x_1383_ = l_Lean_Name_toString(v_baseName_1379_, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__3));
v___x_1385_ = lean_string_append(v___x_1383_, v___x_1384_);
v___x_1386_ = 3;
v___x_1387_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*1, v___x_1386_);
v___x_1388_ = lean_array_get_size(v_a_1368_);
v___x_1389_ = lean_array_push(v_a_1368_, v___x_1387_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 1);
lean_ctor_set(v___x_1370_, 1, v___x_1389_);
lean_ctor_set(v___x_1370_, 0, v___x_1388_);
v___x_1391_ = v___x_1370_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_del_object(v___x_1370_);
v___x_1393_ = lean_array_fget(v_a_1367_, v___x_1265_);
lean_dec(v_a_1367_);
v___x_1394_ = l_Lean_Name_toString(v___x_1393_, v___x_1382_);
v___y_1267_ = v_a_1336_;
v___y_1268_ = v_a_1362_;
v___y_1269_ = v_a_1346_;
v___y_1270_ = v_a_1352_;
v___y_1271_ = v_a_1340_;
v___y_1272_ = v_a_1330_;
v_testDriver_1273_ = v___x_1394_;
v___y_1274_ = v_a_1368_;
goto v___jp_1266_;
}
}
}
else
{
lean_object* v_baseName_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
lean_dec(v_a_1367_);
lean_dec(v_a_1362_);
lean_dec(v_a_1352_);
lean_dec(v_a_1346_);
lean_dec(v_a_1340_);
lean_dec(v_a_1336_);
lean_dec(v_a_1330_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_env_1179_);
v_baseName_1395_ = lean_ctor_get(v_self_1178_, 1);
lean_inc(v_baseName_1395_);
lean_dec_ref(v_self_1178_);
v___x_1396_ = 0;
v___x_1397_ = l_Lean_Name_toString(v_baseName_1395_, v___x_1396_);
v___x_1398_ = ((lean_object*)(l_Lake_Package_loadFromEnv___closed__4));
v___x_1399_ = lean_string_append(v___x_1397_, v___x_1398_);
v___x_1400_ = 3;
v___x_1401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*1, v___x_1400_);
v___x_1402_ = lean_array_get_size(v_a_1368_);
v___x_1403_ = lean_array_push(v_a_1368_, v___x_1401_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 1);
lean_ctor_set(v___x_1370_, 1, v___x_1403_);
lean_ctor_set(v___x_1370_, 0, v___x_1402_);
v___x_1405_ = v___x_1370_;
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
}
else
{
lean_object* v_a_1408_; lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_a_1362_);
lean_dec(v_a_1352_);
lean_dec(v_a_1346_);
lean_dec(v_a_1340_);
lean_dec(v_a_1336_);
lean_dec(v_a_1330_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1408_ = lean_ctor_get(v___x_1366_, 0);
v_a_1409_ = lean_ctor_get(v___x_1366_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1366_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_inc(v_a_1408_);
lean_dec(v___x_1366_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1408_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec(v_a_1352_);
lean_dec(v_a_1346_);
lean_dec(v_a_1340_);
lean_dec(v_a_1336_);
lean_dec(v_a_1330_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1417_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1361_);
v___x_1418_ = lean_io_error_to_string(v_a_1417_);
v___x_1419_ = 3;
v___x_1420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*1, v___x_1419_);
v___x_1421_ = lean_array_get_size(v_a_1353_);
v___x_1422_ = lean_array_push(v_a_1353_, v___x_1420_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 1);
lean_ctor_set(v___x_1355_, 1, v___x_1422_);
lean_ctor_set(v___x_1355_, 0, v___x_1421_);
v___x_1424_ = v___x_1355_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_a_1346_);
lean_dec(v_a_1340_);
lean_dec(v_a_1336_);
lean_dec(v_a_1330_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_opts_1180_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1427_ = lean_ctor_get(v___x_1351_, 0);
v_a_1428_ = lean_ctor_get(v___x_1351_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1351_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_inc(v_a_1427_);
lean_dec(v___x_1351_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_a_1340_);
lean_dec(v_a_1336_);
lean_dec(v_a_1330_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_opts_1180_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1436_ = lean_ctor_get(v___x_1345_, 0);
v_a_1437_ = lean_ctor_get(v___x_1345_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1345_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_inc(v_a_1436_);
lean_dec(v___x_1345_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1336_);
lean_dec(v_a_1330_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_opts_1180_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1445_ = lean_ctor_get(v___x_1339_, 0);
v_a_1446_ = lean_ctor_get(v___x_1339_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1339_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_inc(v_a_1445_);
lean_dec(v___x_1339_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1445_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1330_);
lean_dec_ref(v___f_1263_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_opts_1180_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1454_ = lean_ctor_get(v___x_1335_, 0);
v_a_1455_ = lean_ctor_get(v___x_1335_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1335_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_inc(v_a_1454_);
lean_dec(v___x_1335_);
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
if (lean_obj_tag(v___y_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v_a_1466_; 
v_a_1465_ = lean_ctor_get(v___y_1464_, 0);
lean_inc(v_a_1465_);
v_a_1466_ = lean_ctor_get(v___y_1464_, 1);
lean_inc(v_a_1466_);
lean_dec_ref(v___y_1464_);
v_a_1330_ = v_a_1465_;
v_a_1331_ = v_a_1466_;
goto v___jp_1329_;
}
else
{
lean_object* v_a_1467_; lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v___f_1263_);
lean_del_object(v___x_1196_);
lean_dec(v_a_1193_);
lean_dec(v_a_1188_);
lean_dec_ref(v_opts_1180_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1467_ = lean_ctor_get(v___y_1464_, 0);
v_a_1468_ = lean_ctor_get(v___y_1464_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___y_1464_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___y_1464_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_inc(v_a_1467_);
lean_dec(v___y_1464_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1467_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1188_);
lean_dec_ref(v_opts_1180_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1484_ = lean_ctor_get(v___x_1192_, 0);
v_a_1485_ = lean_ctor_get(v___x_1192_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1192_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_inc(v_a_1484_);
lean_dec(v___x_1192_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1484_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v_opts_1180_);
lean_dec_ref(v_env_1179_);
lean_dec_ref(v_self_1178_);
v_a_1493_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1187_);
v___x_1494_ = lean_io_error_to_string(v_a_1493_);
v___x_1495_ = 3;
v___x_1496_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*1, v___x_1495_);
v___x_1497_ = lean_array_get_size(v_a_1181_);
v___x_1498_ = lean_array_push(v_a_1181_, v___x_1496_);
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_loadFromEnv___boxed(lean_object* v_self_1500_, lean_object* v_env_1501_, lean_object* v_opts_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lake_Package_loadFromEnv(v_self_1500_, v_env_1501_, v_opts_1502_, v_a_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0(lean_object* v_00_u03b2_1506_, lean_object* v_inst_1507_, lean_object* v_t_1508_, lean_object* v_k_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___redArg(v_t_1508_, v_k_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0___boxed(lean_object* v_00_u03b2_1511_, lean_object* v_inst_1512_, lean_object* v_t_1513_, lean_object* v_k_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_loadFromEnv_spec__0(v_00_u03b2_1511_, v_inst_1512_, v_t_1513_, v_k_1514_);
lean_dec(v_k_1514_);
lean_dec(v_t_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1(lean_object* v_00_u03b2_1516_, lean_object* v_k_1517_, lean_object* v_v_1518_, lean_object* v_t_1519_, lean_object* v_hl_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_loadFromEnv_spec__1___redArg(v_k_1517_, v_v_1518_, v_t_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3(lean_object* v_00_u03b2_1522_, lean_object* v_env_1523_, lean_object* v_attr_1524_, lean_object* v_f_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___redArg(v_env_1523_, v_attr_1524_, v_f_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3___boxed(lean_object* v_00_u03b2_1527_, lean_object* v_env_1528_, lean_object* v_attr_1529_, lean_object* v_f_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3(v_00_u03b2_1527_, v_env_1528_, v_attr_1529_, v_f_1530_);
lean_dec_ref(v_attr_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5(lean_object* v_00_u03b4_1532_, lean_object* v_t_1533_, lean_object* v_k_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___redArg(v_t_1533_, v_k_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5___boxed(lean_object* v_00_u03b4_1536_, lean_object* v_t_1537_, lean_object* v_k_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Package_loadFromEnv_spec__5(v_00_u03b4_1536_, v_t_1537_, v_k_1538_);
lean_dec(v_k_1538_);
lean_dec(v_t_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7(lean_object* v_00_u03b2_1540_, lean_object* v_env_1541_, lean_object* v_attr_1542_, lean_object* v_f_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___redArg(v_env_1541_, v_attr_1542_, v_f_1543_, v___y_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7___boxed(lean_object* v_00_u03b2_1547_, lean_object* v_env_1548_, lean_object* v_attr_1549_, lean_object* v_f_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7(v_00_u03b2_1547_, v_env_1548_, v_attr_1549_, v_f_1550_, v___y_1551_);
lean_dec_ref(v_attr_1549_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3(lean_object* v_00_u03b2_1554_, lean_object* v_f_1555_, lean_object* v_as_1556_, size_t v_i_1557_, size_t v_stop_1558_, lean_object* v_b_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___redArg(v_f_1555_, v_as_1556_, v_i_1557_, v_stop_1558_, v_b_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1561_, lean_object* v_f_1562_, lean_object* v_as_1563_, lean_object* v_i_1564_, lean_object* v_stop_1565_, lean_object* v_b_1566_){
_start:
{
size_t v_i_boxed_1567_; size_t v_stop_boxed_1568_; lean_object* v_res_1569_; 
v_i_boxed_1567_ = lean_unbox_usize(v_i_1564_);
lean_dec(v_i_1564_);
v_stop_boxed_1568_ = lean_unbox_usize(v_stop_1565_);
lean_dec(v_stop_1565_);
v_res_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkOrdTagMap___at___00Lake_Package_loadFromEnv_spec__3_spec__3(v_00_u03b2_1561_, v_f_1562_, v_as_1563_, v_i_boxed_1567_, v_stop_boxed_1568_, v_b_1566_);
lean_dec_ref(v_as_1563_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8(lean_object* v_00_u03b2_1570_, lean_object* v_f_1571_, lean_object* v_as_1572_, size_t v_i_1573_, size_t v_stop_1574_, lean_object* v_b_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___redArg(v_f_1571_, v_as_1572_, v_i_1573_, v_stop_1574_, v_b_1575_, v___y_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1579_, lean_object* v_f_1580_, lean_object* v_as_1581_, lean_object* v_i_1582_, lean_object* v_stop_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
size_t v_i_boxed_1587_; size_t v_stop_boxed_1588_; lean_object* v_res_1589_; 
v_i_boxed_1587_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_stop_boxed_1588_ = lean_unbox_usize(v_stop_1583_);
lean_dec(v_stop_1583_);
v_res_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Lean_Eval_0__Lake_mkTagMap___at___00Lake_Package_loadFromEnv_spec__7_spec__8(v_00_u03b2_1579_, v_f_1580_, v_as_1581_, v_i_boxed_1587_, v_stop_boxed_1588_, v_b_1584_, v___y_1585_);
lean_dec_ref(v_as_1581_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1(lean_object* v_env_1590_, lean_object* v_opts_1591_, lean_object* v_as_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_b_1595_){
_start:
{
uint8_t v___x_1596_; 
v___x_1596_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref(v_env_1590_);
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_b_1595_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; lean_object* v_a_1599_; lean_object* v___x_1600_; 
v___x_1598_ = l_Lake_instTypeNamePackageFacetDecl_unsafe__1;
v_a_1599_ = lean_array_uget_borrowed(v_as_1592_, v_i_1594_);
lean_inc(v_a_1599_);
lean_inc_ref(v_env_1590_);
v___x_1600_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1590_, v_opts_1591_, v___x_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_b_1595_);
lean_dec_ref(v_env_1590_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
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
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v_name_1610_; lean_object* v_config_1611_; lean_object* v___x_1612_; size_t v___x_1613_; size_t v___x_1614_; 
v_a_1609_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1600_);
v_name_1610_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_name_1610_);
v_config_1611_ = lean_ctor_get(v_a_1609_, 1);
lean_inc(v_config_1611_);
lean_dec(v_a_1609_);
v___x_1612_ = l_Lake_Workspace_addPackageFacetConfig(v_name_1610_, v_config_1611_, v_b_1595_);
v___x_1613_ = ((size_t)1ULL);
v___x_1614_ = lean_usize_add(v_i_1594_, v___x_1613_);
v_i_1594_ = v___x_1614_;
v_b_1595_ = v___x_1612_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1___boxed(lean_object* v_env_1616_, lean_object* v_opts_1617_, lean_object* v_as_1618_, lean_object* v_sz_1619_, lean_object* v_i_1620_, lean_object* v_b_1621_){
_start:
{
size_t v_sz_boxed_1622_; size_t v_i_boxed_1623_; lean_object* v_res_1624_; 
v_sz_boxed_1622_ = lean_unbox_usize(v_sz_1619_);
lean_dec(v_sz_1619_);
v_i_boxed_1623_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1(v_env_1616_, v_opts_1617_, v_as_1618_, v_sz_boxed_1622_, v_i_boxed_1623_, v_b_1621_);
lean_dec_ref(v_as_1618_);
lean_dec_ref(v_opts_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0(lean_object* v_env_1625_, lean_object* v_opts_1626_, lean_object* v_as_1627_, size_t v_sz_1628_, size_t v_i_1629_, lean_object* v_b_1630_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_usize_dec_lt(v_i_1629_, v_sz_1628_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v_env_1625_);
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_b_1630_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; lean_object* v_a_1634_; lean_object* v___x_1635_; 
v___x_1633_ = l_Lake_instTypeNameModuleFacetDecl_unsafe__1;
v_a_1634_ = lean_array_uget_borrowed(v_as_1627_, v_i_1629_);
lean_inc(v_a_1634_);
lean_inc_ref(v_env_1625_);
v___x_1635_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1625_, v_opts_1626_, v___x_1633_, v_a_1634_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_b_1630_);
lean_dec_ref(v_env_1625_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v_name_1645_; lean_object* v_config_1646_; lean_object* v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; 
v_a_1644_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1635_);
v_name_1645_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_name_1645_);
v_config_1646_ = lean_ctor_get(v_a_1644_, 1);
lean_inc(v_config_1646_);
lean_dec(v_a_1644_);
v___x_1647_ = l_Lake_Workspace_addModuleFacetConfig(v_name_1645_, v_config_1646_, v_b_1630_);
v___x_1648_ = ((size_t)1ULL);
v___x_1649_ = lean_usize_add(v_i_1629_, v___x_1648_);
v_i_1629_ = v___x_1649_;
v_b_1630_ = v___x_1647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0___boxed(lean_object* v_env_1651_, lean_object* v_opts_1652_, lean_object* v_as_1653_, lean_object* v_sz_1654_, lean_object* v_i_1655_, lean_object* v_b_1656_){
_start:
{
size_t v_sz_boxed_1657_; size_t v_i_boxed_1658_; lean_object* v_res_1659_; 
v_sz_boxed_1657_ = lean_unbox_usize(v_sz_1654_);
lean_dec(v_sz_1654_);
v_i_boxed_1658_ = lean_unbox_usize(v_i_1655_);
lean_dec(v_i_1655_);
v_res_1659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0(v_env_1651_, v_opts_1652_, v_as_1653_, v_sz_boxed_1657_, v_i_boxed_1658_, v_b_1656_);
lean_dec_ref(v_as_1653_);
lean_dec_ref(v_opts_1652_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2(lean_object* v_env_1660_, lean_object* v_opts_1661_, lean_object* v_as_1662_, size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_b_1665_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v_env_1660_);
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_b_1665_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; lean_object* v_a_1669_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lake_instTypeNameLibraryFacetDecl_unsafe__1;
v_a_1669_ = lean_array_uget_borrowed(v_as_1662_, v_i_1664_);
lean_inc(v_a_1669_);
lean_inc_ref(v_env_1660_);
v___x_1670_ = l___private_Lake_Load_Lean_Eval_0__Lake_unsafeEvalConstCheck___redArg(v_env_1660_, v_opts_1661_, v___x_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v_b_1665_);
lean_dec_ref(v_env_1660_);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
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
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v_name_1680_; lean_object* v_config_1681_; lean_object* v___x_1682_; size_t v___x_1683_; size_t v___x_1684_; 
v_a_1679_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1679_);
lean_dec_ref(v___x_1670_);
v_name_1680_ = lean_ctor_get(v_a_1679_, 0);
lean_inc(v_name_1680_);
v_config_1681_ = lean_ctor_get(v_a_1679_, 1);
lean_inc(v_config_1681_);
lean_dec(v_a_1679_);
v___x_1682_ = l_Lake_Workspace_addLibraryFacetConfig(v_name_1680_, v_config_1681_, v_b_1665_);
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1664_, v___x_1683_);
v_i_1664_ = v___x_1684_;
v_b_1665_ = v___x_1682_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2___boxed(lean_object* v_env_1686_, lean_object* v_opts_1687_, lean_object* v_as_1688_, lean_object* v_sz_1689_, lean_object* v_i_1690_, lean_object* v_b_1691_){
_start:
{
size_t v_sz_boxed_1692_; size_t v_i_boxed_1693_; lean_object* v_res_1694_; 
v_sz_boxed_1692_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1693_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2(v_env_1686_, v_opts_1687_, v_as_1688_, v_sz_boxed_1692_, v_i_boxed_1693_, v_b_1691_);
lean_dec_ref(v_as_1688_);
lean_dec_ref(v_opts_1687_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object* v_env_1695_, lean_object* v_opts_1696_, lean_object* v_self_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; size_t v_sz_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1698_ = l_Lake_moduleFacetAttr;
lean_inc_ref(v_env_1695_);
v___x_1699_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1698_, v_env_1695_);
v_sz_1700_ = lean_array_size(v___x_1699_);
v___x_1701_ = ((size_t)0ULL);
lean_inc_ref(v_env_1695_);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__0(v_env_1695_, v_opts_1696_, v___x_1699_, v_sz_1700_, v___x_1701_, v_self_1697_);
lean_dec_ref(v___x_1699_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_dec_ref(v_env_1695_);
return v___x_1702_;
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; size_t v_sz_1706_; lean_object* v___x_1707_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = l_Lake_packageFacetAttr;
lean_inc_ref(v_env_1695_);
v___x_1705_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1704_, v_env_1695_);
v_sz_1706_ = lean_array_size(v___x_1705_);
lean_inc_ref(v_env_1695_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__1(v_env_1695_, v_opts_1696_, v___x_1705_, v_sz_1706_, v___x_1701_, v_a_1703_);
lean_dec_ref(v___x_1705_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec_ref(v_env_1695_);
return v___x_1707_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; size_t v_sz_1711_; lean_object* v___x_1712_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = l_Lake_libraryFacetAttr;
lean_inc_ref(v_env_1695_);
v___x_1710_ = l_Lake_OrderedTagAttribute_getAllEntries(v___x_1709_, v_env_1695_);
v_sz_1711_ = lean_array_size(v___x_1710_);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_addFacetsFromEnv_spec__2(v_env_1695_, v_opts_1696_, v___x_1710_, v_sz_1711_, v___x_1701_, v_a_1708_);
lean_dec_ref(v___x_1710_);
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetsFromEnv___boxed(lean_object* v_env_1713_, lean_object* v_opts_1714_, lean_object* v_self_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lake_Workspace_addFacetsFromEnv(v_env_1713_, v_opts_1714_, v_self_1715_);
lean_dec_ref(v_opts_1714_);
return v_res_1716_;
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
