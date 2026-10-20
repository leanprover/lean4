// Lean compiler output
// Module: Lake.Config.LakeConfig
// Imports: public import Lake.Config.Cache public import Lake.Config.MetaClasses meta import Lake.Config.Meta
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedCacheServiceKind_default;
LEAN_EXPORT uint8_t l_Lake_instInhabitedCacheServiceKind;
static const lean_string_object l_Lake_CacheServiceKind_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l_Lake_CacheServiceKind_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_CacheServiceKind_ofString_x3f___closed__0_value;
static const lean_string_object l_Lake_CacheServiceKind_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s3"};
static const lean_object* l_Lake_CacheServiceKind_ofString_x3f___closed__1 = (const lean_object*)&l_Lake_CacheServiceKind_ofString_x3f___closed__1_value;
static const lean_ctor_object l_Lake_CacheServiceKind_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lake_CacheServiceKind_ofString_x3f___closed__2 = (const lean_object*)&l_Lake_CacheServiceKind_ofString_x3f___closed__2_value;
static const lean_ctor_object l_Lake_CacheServiceKind_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_CacheServiceKind_ofString_x3f___closed__3 = (const lean_object*)&l_Lake_CacheServiceKind_ofString_x3f___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f___boxed(lean_object*);
static const lean_string_object l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedCacheServiceConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedCacheServiceConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheServiceConfig_default = (const lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheServiceConfig = (const lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheServiceConfig_name___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_name___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_name___proj___closed__0 = (const lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheServiceConfig_name___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_name___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_name___proj___closed__1 = (const lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheServiceConfig_name___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_name___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_name___proj___closed__2 = (const lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__2_value;
static const lean_closure_object l_Lake_CacheServiceConfig_name___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_name___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_name___proj___closed__3 = (const lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__3_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_name___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__0_value),((lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__1_value),((lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__2_value),((lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheServiceConfig_name___proj___closed__4 = (const lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_name___proj = (const lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_name_instConfigField = (const lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__4_value;
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheServiceConfig_kind___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_kind___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_kind___proj___closed__0 = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheServiceConfig_kind___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_kind___proj___closed__1 = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheServiceConfig_kind___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_kind___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_kind___proj___closed__2 = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__2_value;
static const lean_closure_object l_Lake_CacheServiceConfig_kind___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_kind___proj___closed__3 = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__3_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_kind___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__0_value),((lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__1_value),((lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__2_value),((lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheServiceConfig_kind___proj___closed__4 = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_kind___proj = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_kind_instConfigField = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_type_instConfigField = (const lean_object*)&l_Lake_CacheServiceConfig_kind___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0 = (const lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1 = (const lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2 = (const lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__0_value),((lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__1_value),((lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__2_value),((lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3 = (const lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj = (const lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_apiEndpoint_instConfigField = (const lean_object*)&l_Lake_CacheServiceConfig_apiEndpoint___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0 = (const lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1 = (const lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2 = (const lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__0_value),((lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__1_value),((lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__2_value),((lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3 = (const lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj = (const lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_artifactEndpoint_instConfigField = (const lean_object*)&l_Lake_CacheServiceConfig_artifactEndpoint___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0 = (const lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1 = (const lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2 = (const lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__0_value),((lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__1_value),((lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__2_value),((lean_object*)&l_Lake_CacheServiceConfig_name___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3 = (const lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj = (const lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_revisionEndpoint_instConfigField = (const lean_object*)&l_Lake_CacheServiceConfig_revisionEndpoint___proj___closed__3_value;
static const lean_array_object l_Lake_CacheServiceConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__0 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__0_value;
static const lean_string_object l_Lake_CacheServiceConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__1 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__2 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__2_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__2_value),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__3 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__3_value;
static lean_once_cell_t l_Lake_CacheServiceConfig___fields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig___fields___closed__4;
static const lean_string_object l_Lake_CacheServiceConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__5 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__5_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__5_value),LEAN_SCALAR_PTR_LITERAL(90, 186, 66, 236, 16, 221, 215, 158)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__6 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__6_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__6_value),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__6_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__7 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__7_value;
static lean_once_cell_t l_Lake_CacheServiceConfig___fields___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig___fields___closed__8;
static const lean_string_object l_Lake_CacheServiceConfig___fields___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__9 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__9_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__9_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__10 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__10_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__10_value),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__11 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__11_value;
static lean_once_cell_t l_Lake_CacheServiceConfig___fields___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig___fields___closed__12;
static const lean_string_object l_Lake_CacheServiceConfig___fields___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "apiEndpoint"};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__13 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__13_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__13_value),LEAN_SCALAR_PTR_LITERAL(89, 173, 152, 220, 1, 2, 136, 98)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__14 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__14_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__14_value),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__14_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__15 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__15_value;
static lean_once_cell_t l_Lake_CacheServiceConfig___fields___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig___fields___closed__16;
static const lean_string_object l_Lake_CacheServiceConfig___fields___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "artifactEndpoint"};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__17 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__17_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__17_value),LEAN_SCALAR_PTR_LITERAL(245, 122, 147, 109, 179, 215, 132, 47)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__18 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__18_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__18_value),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__18_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__19 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__19_value;
static lean_once_cell_t l_Lake_CacheServiceConfig___fields___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig___fields___closed__20;
static const lean_string_object l_Lake_CacheServiceConfig___fields___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "revisionEndpoint"};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__21 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__21_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__21_value),LEAN_SCALAR_PTR_LITERAL(239, 62, 117, 68, 41, 112, 183, 121)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__22 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__22_value;
static const lean_ctor_object l_Lake_CacheServiceConfig___fields___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__22_value),((lean_object*)&l_Lake_CacheServiceConfig___fields___closed__22_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheServiceConfig___fields___closed__23 = (const lean_object*)&l_Lake_CacheServiceConfig___fields___closed__23_value;
static lean_once_cell_t l_Lake_CacheServiceConfig___fields___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig___fields___closed__24;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig___fields;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_instConfigFields;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_instConfigInfo___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__0;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__1 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__1_value;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__2 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__2_value;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__3 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__3_value;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__4 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__4_value;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__5 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__5_value;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__6 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__6_value;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__7 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__7_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_instConfigInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__1_value),((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__2_value)}};
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__8 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__8_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_instConfigInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__8_value),((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__3_value),((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__4_value),((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__5_value),((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__6_value)}};
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__9 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__9_value;
static const lean_ctor_object l_Lake_CacheServiceConfig_instConfigInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__9_value),((lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__7_value)}};
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__10 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__10_value;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_CacheServiceConfig_instConfigInfo___closed__11;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__12;
static const lean_closure_object l_Lake_CacheServiceConfig_instConfigInfo___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceConfig_instConfigInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__13 = (const lean_object*)&l_Lake_CacheServiceConfig_instConfigInfo___closed__13_value;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_CacheServiceConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__15;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__16;
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_instConfigInfo;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceConfig_instEmptyCollection = (const lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__1_value;
static const lean_array_object l_Lake_instInhabitedCacheConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedCacheConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedCacheConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedCacheServiceConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedCacheConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheConfig_default = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheConfig = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheConfig_defaultService___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_defaultService___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_defaultService___proj___closed__0 = (const lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheConfig_defaultService___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_defaultService___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_defaultService___proj___closed__1 = (const lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheConfig_defaultService___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_defaultService___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_defaultService___proj___closed__2 = (const lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__2_value;
static const lean_closure_object l_Lake_CacheConfig_defaultService___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_defaultService___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_defaultService___proj___closed__3 = (const lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__3_value;
static const lean_ctor_object l_Lake_CacheConfig_defaultService___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__0_value),((lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__1_value),((lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__2_value),((lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheConfig_defaultService___proj___closed__4 = (const lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheConfig_defaultService___proj = (const lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheConfig_defaultService_instConfigField = (const lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_CacheConfig_defaultUploadService___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_defaultUploadService___proj___closed__0 = (const lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheConfig_defaultUploadService___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_defaultUploadService___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_defaultUploadService___proj___closed__1 = (const lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheConfig_defaultUploadService___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_defaultUploadService___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_defaultUploadService___proj___closed__2 = (const lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__2_value;
static const lean_ctor_object l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__0_value),((lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__1_value),((lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__2_value),((lean_object*)&l_Lake_CacheConfig_defaultService___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheConfig_defaultUploadService___proj___closed__3 = (const lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheConfig_defaultUploadService___proj = (const lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_CacheConfig_defaultUploadService_instConfigField = (const lean_object*)&l_Lake_CacheConfig_defaultUploadService___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheConfig_services___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_services___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_services___proj___closed__0 = (const lean_object*)&l_Lake_CacheConfig_services___proj___closed__0_value;
static const lean_closure_object l_Lake_CacheConfig_services___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_services___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_services___proj___closed__1 = (const lean_object*)&l_Lake_CacheConfig_services___proj___closed__1_value;
static const lean_closure_object l_Lake_CacheConfig_services___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_services___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_services___proj___closed__2 = (const lean_object*)&l_Lake_CacheConfig_services___proj___closed__2_value;
static const lean_closure_object l_Lake_CacheConfig_services___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheConfig_services___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheConfig_services___proj___closed__3 = (const lean_object*)&l_Lake_CacheConfig_services___proj___closed__3_value;
static const lean_ctor_object l_Lake_CacheConfig_services___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheConfig_services___proj___closed__0_value),((lean_object*)&l_Lake_CacheConfig_services___proj___closed__1_value),((lean_object*)&l_Lake_CacheConfig_services___proj___closed__2_value),((lean_object*)&l_Lake_CacheConfig_services___proj___closed__3_value)}};
static const lean_object* l_Lake_CacheConfig_services___proj___closed__4 = (const lean_object*)&l_Lake_CacheConfig_services___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheConfig_services___proj = (const lean_object*)&l_Lake_CacheConfig_services___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_CacheConfig_service_instConfigField = (const lean_object*)&l_Lake_CacheConfig_services___proj___closed__4_value;
static const lean_string_object l_Lake_CacheConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "defaultService"};
static const lean_object* l_Lake_CacheConfig___fields___closed__0 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__0_value;
static const lean_ctor_object l_Lake_CacheConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheConfig___fields___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 73, 131, 193, 205, 87, 118, 106)}};
static const lean_object* l_Lake_CacheConfig___fields___closed__1 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_CacheConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheConfig___fields___closed__1_value),((lean_object*)&l_Lake_CacheConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheConfig___fields___closed__2 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__2_value;
static lean_once_cell_t l_Lake_CacheConfig___fields___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig___fields___closed__3;
static const lean_string_object l_Lake_CacheConfig___fields___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "defaultUploadService"};
static const lean_object* l_Lake_CacheConfig___fields___closed__4 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__4_value;
static const lean_ctor_object l_Lake_CacheConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheConfig___fields___closed__4_value),LEAN_SCALAR_PTR_LITERAL(80, 223, 100, 30, 22, 52, 44, 164)}};
static const lean_object* l_Lake_CacheConfig___fields___closed__5 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__5_value;
static const lean_ctor_object l_Lake_CacheConfig___fields___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheConfig___fields___closed__5_value),((lean_object*)&l_Lake_CacheConfig___fields___closed__5_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheConfig___fields___closed__6 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__6_value;
static lean_once_cell_t l_Lake_CacheConfig___fields___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig___fields___closed__7;
static const lean_string_object l_Lake_CacheConfig___fields___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "service"};
static const lean_object* l_Lake_CacheConfig___fields___closed__8 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__8_value;
static const lean_ctor_object l_Lake_CacheConfig___fields___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheConfig___fields___closed__8_value),LEAN_SCALAR_PTR_LITERAL(254, 133, 224, 172, 100, 98, 172, 218)}};
static const lean_object* l_Lake_CacheConfig___fields___closed__9 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__9_value;
static const lean_string_object l_Lake_CacheConfig___fields___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "services"};
static const lean_object* l_Lake_CacheConfig___fields___closed__10 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__10_value;
static const lean_ctor_object l_Lake_CacheConfig___fields___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_CacheConfig___fields___closed__10_value),LEAN_SCALAR_PTR_LITERAL(110, 53, 101, 59, 216, 160, 192, 145)}};
static const lean_object* l_Lake_CacheConfig___fields___closed__11 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__11_value;
static const lean_ctor_object l_Lake_CacheConfig___fields___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheConfig___fields___closed__9_value),((lean_object*)&l_Lake_CacheConfig___fields___closed__11_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheConfig___fields___closed__12 = (const lean_object*)&l_Lake_CacheConfig___fields___closed__12_value;
static lean_once_cell_t l_Lake_CacheConfig___fields___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig___fields___closed__13;
LEAN_EXPORT lean_object* l_Lake_CacheConfig___fields;
LEAN_EXPORT lean_object* l_Lake_CacheConfig_instConfigFields;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig_instConfigInfo___closed__0;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_CacheConfig_instConfigInfo___closed__1;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig_instConfigInfo___closed__2;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_CacheConfig_instConfigInfo___closed__3;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig_instConfigInfo___closed__4;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig_instConfigInfo___closed__5;
LEAN_EXPORT lean_object* l_Lake_CacheConfig_instConfigInfo;
LEAN_EXPORT const lean_object* l_Lake_CacheConfig_instEmptyCollection = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLakeConfig_default = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLakeConfig = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LakeConfig_cache___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LakeConfig_cache___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LakeConfig_cache___proj___closed__0 = (const lean_object*)&l_Lake_LakeConfig_cache___proj___closed__0_value;
static const lean_closure_object l_Lake_LakeConfig_cache___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LakeConfig_cache___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LakeConfig_cache___proj___closed__1 = (const lean_object*)&l_Lake_LakeConfig_cache___proj___closed__1_value;
static const lean_closure_object l_Lake_LakeConfig_cache___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LakeConfig_cache___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LakeConfig_cache___proj___closed__2 = (const lean_object*)&l_Lake_LakeConfig_cache___proj___closed__2_value;
static const lean_closure_object l_Lake_LakeConfig_cache___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LakeConfig_cache___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LakeConfig_cache___proj___closed__3 = (const lean_object*)&l_Lake_LakeConfig_cache___proj___closed__3_value;
static const lean_ctor_object l_Lake_LakeConfig_cache___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LakeConfig_cache___proj___closed__0_value),((lean_object*)&l_Lake_LakeConfig_cache___proj___closed__1_value),((lean_object*)&l_Lake_LakeConfig_cache___proj___closed__2_value),((lean_object*)&l_Lake_LakeConfig_cache___proj___closed__3_value)}};
static const lean_object* l_Lake_LakeConfig_cache___proj___closed__4 = (const lean_object*)&l_Lake_LakeConfig_cache___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LakeConfig_cache___proj = (const lean_object*)&l_Lake_LakeConfig_cache___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LakeConfig_cache_instConfigField = (const lean_object*)&l_Lake_LakeConfig_cache___proj___closed__4_value;
static const lean_string_object l_Lake_LakeConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_LakeConfig___fields___closed__0 = (const lean_object*)&l_Lake_LakeConfig___fields___closed__0_value;
static const lean_ctor_object l_Lake_LakeConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_LakeConfig___fields___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 124, 124, 22, 3, 188, 172, 87)}};
static const lean_object* l_Lake_LakeConfig___fields___closed__1 = (const lean_object*)&l_Lake_LakeConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_LakeConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LakeConfig___fields___closed__1_value),((lean_object*)&l_Lake_LakeConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LakeConfig___fields___closed__2 = (const lean_object*)&l_Lake_LakeConfig___fields___closed__2_value;
static lean_once_cell_t l_Lake_LakeConfig___fields___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeConfig___fields___closed__3;
LEAN_EXPORT lean_object* l_Lake_LakeConfig___fields;
LEAN_EXPORT lean_object* l_Lake_LakeConfig_instConfigFields;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeConfig_instConfigInfo___closed__0;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_LakeConfig_instConfigInfo___closed__1;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeConfig_instConfigInfo___closed__2;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_LakeConfig_instConfigInfo___closed__3;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeConfig_instConfigInfo___closed__4;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeConfig_instConfigInfo___closed__5;
LEAN_EXPORT lean_object* l_Lake_LakeConfig_instConfigInfo;
LEAN_EXPORT const lean_object* l_Lake_LakeConfig_instEmptyCollection = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lake_CacheServiceKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_CacheServiceKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lake_CacheServiceKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg(lean_object* v_undef_22_){
_start:
{
lean_inc(v_undef_22_);
return v_undef_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg___boxed(lean_object* v_undef_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_CacheServiceKind_undef_elim___redArg(v_undef_23_);
lean_dec(v_undef_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_undef_28_){
_start:
{
lean_inc(v_undef_28_);
return v_undef_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_undef_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lake_CacheServiceKind_undef_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_undef_32_);
lean_dec(v_undef_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg(lean_object* v_reservoir_35_){
_start:
{
lean_inc(v_reservoir_35_);
return v_reservoir_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg___boxed(lean_object* v_reservoir_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_CacheServiceKind_reservoir_elim___redArg(v_reservoir_36_);
lean_dec(v_reservoir_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_reservoir_41_){
_start:
{
lean_inc(v_reservoir_41_);
return v_reservoir_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_reservoir_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lake_CacheServiceKind_reservoir_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_reservoir_45_);
lean_dec(v_reservoir_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg(lean_object* v_s3_48_){
_start:
{
lean_inc(v_s3_48_);
return v_s3_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg___boxed(lean_object* v_s3_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_CacheServiceKind_s3_elim___redArg(v_s3_49_);
lean_dec(v_s3_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_s3_54_){
_start:
{
lean_inc(v_s3_54_);
return v_s3_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_s3_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lake_CacheServiceKind_s3_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_s3_58_);
lean_dec(v_s3_58_);
return v_res_60_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind_default(void){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f(lean_object* v_s_71_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__0));
v___x_73_ = lean_string_dec_eq(v_s_71_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__1));
v___x_75_ = lean_string_dec_eq(v_s_71_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__2));
return v___x_77_;
}
}
else
{
lean_object* v___x_78_; 
v___x_78_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__3));
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f___boxed(lean_object* v_s_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_CacheServiceKind_ofString_x3f(v_s_79_);
lean_dec_ref(v_s_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0(lean_object* v_cfg_87_){
_start:
{
lean_object* v_name_88_; 
v_name_88_ = lean_ctor_get(v_cfg_87_, 0);
lean_inc_ref(v_name_88_);
return v_name_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0___boxed(lean_object* v_cfg_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lake_CacheServiceConfig_name___proj___lam__0(v_cfg_89_);
lean_dec_ref(v_cfg_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__1(lean_object* v_val_91_, lean_object* v_cfg_92_){
_start:
{
uint8_t v_kind_93_; lean_object* v_apiEndpoint_94_; lean_object* v_artifactEndpoint_95_; lean_object* v_revisionEndpoint_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_kind_93_ = lean_ctor_get_uint8(v_cfg_92_, sizeof(void*)*4);
v_apiEndpoint_94_ = lean_ctor_get(v_cfg_92_, 1);
v_artifactEndpoint_95_ = lean_ctor_get(v_cfg_92_, 2);
v_revisionEndpoint_96_ = lean_ctor_get(v_cfg_92_, 3);
v_isSharedCheck_103_ = !lean_is_exclusive(v_cfg_92_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v_cfg_92_, 0);
lean_dec(v_unused_104_);
v___x_98_ = v_cfg_92_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_revisionEndpoint_96_);
lean_inc(v_artifactEndpoint_95_);
lean_inc(v_apiEndpoint_94_);
lean_dec(v_cfg_92_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v_val_91_);
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_val_91_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_apiEndpoint_94_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_artifactEndpoint_95_);
lean_ctor_set(v_reuseFailAlloc_102_, 3, v_revisionEndpoint_96_);
lean_ctor_set_uint8(v_reuseFailAlloc_102_, sizeof(void*)*4, v_kind_93_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__2(lean_object* v_f_105_, lean_object* v_cfg_106_){
_start:
{
lean_object* v_name_107_; uint8_t v_kind_108_; lean_object* v_apiEndpoint_109_; lean_object* v_artifactEndpoint_110_; lean_object* v_revisionEndpoint_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_119_; 
v_name_107_ = lean_ctor_get(v_cfg_106_, 0);
v_kind_108_ = lean_ctor_get_uint8(v_cfg_106_, sizeof(void*)*4);
v_apiEndpoint_109_ = lean_ctor_get(v_cfg_106_, 1);
v_artifactEndpoint_110_ = lean_ctor_get(v_cfg_106_, 2);
v_revisionEndpoint_111_ = lean_ctor_get(v_cfg_106_, 3);
v_isSharedCheck_119_ = !lean_is_exclusive(v_cfg_106_);
if (v_isSharedCheck_119_ == 0)
{
v___x_113_ = v_cfg_106_;
v_isShared_114_ = v_isSharedCheck_119_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_revisionEndpoint_111_);
lean_inc(v_artifactEndpoint_110_);
lean_inc(v_apiEndpoint_109_);
lean_inc(v_name_107_);
lean_dec(v_cfg_106_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_119_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = lean_apply_1(v_f_105_, v_name_107_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_115_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_apiEndpoint_109_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_artifactEndpoint_110_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v_revisionEndpoint_111_);
lean_ctor_set_uint8(v_reuseFailAlloc_118_, sizeof(void*)*4, v_kind_108_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3(lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3___boxed(lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lake_CacheServiceConfig_name___proj___lam__3(v_x_122_);
lean_dec_ref(v_x_122_);
return v_res_123_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__0(lean_object* v_cfg_135_){
_start:
{
uint8_t v_kind_136_; 
v_kind_136_ = lean_ctor_get_uint8(v_cfg_135_, sizeof(void*)*4);
return v_kind_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__0___boxed(lean_object* v_cfg_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lake_CacheServiceConfig_kind___proj___lam__0(v_cfg_137_);
lean_dec_ref(v_cfg_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1(uint8_t v_val_140_, lean_object* v_cfg_141_){
_start:
{
lean_object* v_name_142_; lean_object* v_apiEndpoint_143_; lean_object* v_artifactEndpoint_144_; lean_object* v_revisionEndpoint_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_name_142_ = lean_ctor_get(v_cfg_141_, 0);
v_apiEndpoint_143_ = lean_ctor_get(v_cfg_141_, 1);
v_artifactEndpoint_144_ = lean_ctor_get(v_cfg_141_, 2);
v_revisionEndpoint_145_ = lean_ctor_get(v_cfg_141_, 3);
v_isSharedCheck_152_ = !lean_is_exclusive(v_cfg_141_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v_cfg_141_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_revisionEndpoint_145_);
lean_inc(v_artifactEndpoint_144_);
lean_inc(v_apiEndpoint_143_);
lean_inc(v_name_142_);
lean_dec(v_cfg_141_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_name_142_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_apiEndpoint_143_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_artifactEndpoint_144_);
lean_ctor_set(v_reuseFailAlloc_151_, 3, v_revisionEndpoint_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*4, v_val_140_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed(lean_object* v_val_153_, lean_object* v_cfg_154_){
_start:
{
uint8_t v_val_49__boxed_155_; lean_object* v_res_156_; 
v_val_49__boxed_155_ = lean_unbox(v_val_153_);
v_res_156_ = l_Lake_CacheServiceConfig_kind___proj___lam__1(v_val_49__boxed_155_, v_cfg_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__2(lean_object* v_f_157_, lean_object* v_cfg_158_){
_start:
{
lean_object* v_name_159_; uint8_t v_kind_160_; lean_object* v_apiEndpoint_161_; lean_object* v_artifactEndpoint_162_; lean_object* v_revisionEndpoint_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_173_; 
v_name_159_ = lean_ctor_get(v_cfg_158_, 0);
v_kind_160_ = lean_ctor_get_uint8(v_cfg_158_, sizeof(void*)*4);
v_apiEndpoint_161_ = lean_ctor_get(v_cfg_158_, 1);
v_artifactEndpoint_162_ = lean_ctor_get(v_cfg_158_, 2);
v_revisionEndpoint_163_ = lean_ctor_get(v_cfg_158_, 3);
v_isSharedCheck_173_ = !lean_is_exclusive(v_cfg_158_);
if (v_isSharedCheck_173_ == 0)
{
v___x_165_ = v_cfg_158_;
v_isShared_166_ = v_isSharedCheck_173_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_revisionEndpoint_163_);
lean_inc(v_artifactEndpoint_162_);
lean_inc(v_apiEndpoint_161_);
lean_inc(v_name_159_);
lean_dec(v_cfg_158_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_173_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_167_ = lean_box(v_kind_160_);
v___x_168_ = lean_apply_1(v_f_157_, v___x_167_);
if (v_isShared_166_ == 0)
{
v___x_170_ = v___x_165_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_name_159_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_apiEndpoint_161_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_artifactEndpoint_162_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v_revisionEndpoint_163_);
v___x_170_ = v_reuseFailAlloc_172_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
uint8_t v___x_171_; 
v___x_171_ = lean_unbox(v___x_168_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*4, v___x_171_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__3(lean_object* v_x_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = 0;
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed(lean_object* v_x_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lake_CacheServiceConfig_kind___proj___lam__3(v_x_176_);
lean_dec_ref(v_x_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(lean_object* v_cfg_191_){
_start:
{
lean_object* v_apiEndpoint_192_; 
v_apiEndpoint_192_ = lean_ctor_get(v_cfg_191_, 1);
lean_inc_ref(v_apiEndpoint_192_);
return v_apiEndpoint_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed(lean_object* v_cfg_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(v_cfg_193_);
lean_dec_ref(v_cfg_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1(lean_object* v_val_195_, lean_object* v_cfg_196_){
_start:
{
lean_object* v_name_197_; uint8_t v_kind_198_; lean_object* v_artifactEndpoint_199_; lean_object* v_revisionEndpoint_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_name_197_ = lean_ctor_get(v_cfg_196_, 0);
v_kind_198_ = lean_ctor_get_uint8(v_cfg_196_, sizeof(void*)*4);
v_artifactEndpoint_199_ = lean_ctor_get(v_cfg_196_, 2);
v_revisionEndpoint_200_ = lean_ctor_get(v_cfg_196_, 3);
v_isSharedCheck_207_ = !lean_is_exclusive(v_cfg_196_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_cfg_196_, 1);
lean_dec(v_unused_208_);
v___x_202_ = v_cfg_196_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_revisionEndpoint_200_);
lean_inc(v_artifactEndpoint_199_);
lean_inc(v_name_197_);
lean_dec(v_cfg_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_val_195_);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_name_197_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_val_195_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_artifactEndpoint_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_revisionEndpoint_200_);
lean_ctor_set_uint8(v_reuseFailAlloc_206_, sizeof(void*)*4, v_kind_198_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2(lean_object* v_f_209_, lean_object* v_cfg_210_){
_start:
{
lean_object* v_name_211_; uint8_t v_kind_212_; lean_object* v_apiEndpoint_213_; lean_object* v_artifactEndpoint_214_; lean_object* v_revisionEndpoint_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_name_211_ = lean_ctor_get(v_cfg_210_, 0);
v_kind_212_ = lean_ctor_get_uint8(v_cfg_210_, sizeof(void*)*4);
v_apiEndpoint_213_ = lean_ctor_get(v_cfg_210_, 1);
v_artifactEndpoint_214_ = lean_ctor_get(v_cfg_210_, 2);
v_revisionEndpoint_215_ = lean_ctor_get(v_cfg_210_, 3);
v_isSharedCheck_223_ = !lean_is_exclusive(v_cfg_210_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v_cfg_210_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_revisionEndpoint_215_);
lean_inc(v_artifactEndpoint_214_);
lean_inc(v_apiEndpoint_213_);
lean_inc(v_name_211_);
lean_dec(v_cfg_210_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_apply_1(v_f_209_, v_apiEndpoint_213_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_name_211_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_artifactEndpoint_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v_revisionEndpoint_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_222_, sizeof(void*)*4, v_kind_212_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(lean_object* v_cfg_234_){
_start:
{
lean_object* v_artifactEndpoint_235_; 
v_artifactEndpoint_235_ = lean_ctor_get(v_cfg_234_, 2);
lean_inc_ref(v_artifactEndpoint_235_);
return v_artifactEndpoint_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed(lean_object* v_cfg_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(v_cfg_236_);
lean_dec_ref(v_cfg_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1(lean_object* v_val_238_, lean_object* v_cfg_239_){
_start:
{
lean_object* v_name_240_; uint8_t v_kind_241_; lean_object* v_apiEndpoint_242_; lean_object* v_revisionEndpoint_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
v_name_240_ = lean_ctor_get(v_cfg_239_, 0);
v_kind_241_ = lean_ctor_get_uint8(v_cfg_239_, sizeof(void*)*4);
v_apiEndpoint_242_ = lean_ctor_get(v_cfg_239_, 1);
v_revisionEndpoint_243_ = lean_ctor_get(v_cfg_239_, 3);
v_isSharedCheck_250_ = !lean_is_exclusive(v_cfg_239_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_cfg_239_, 2);
lean_dec(v_unused_251_);
v___x_245_ = v_cfg_239_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_revisionEndpoint_243_);
lean_inc(v_apiEndpoint_242_);
lean_inc(v_name_240_);
lean_dec(v_cfg_239_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 2, v_val_238_);
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_name_240_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_apiEndpoint_242_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_val_238_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_revisionEndpoint_243_);
lean_ctor_set_uint8(v_reuseFailAlloc_249_, sizeof(void*)*4, v_kind_241_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2(lean_object* v_f_252_, lean_object* v_cfg_253_){
_start:
{
lean_object* v_name_254_; uint8_t v_kind_255_; lean_object* v_apiEndpoint_256_; lean_object* v_artifactEndpoint_257_; lean_object* v_revisionEndpoint_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_name_254_ = lean_ctor_get(v_cfg_253_, 0);
v_kind_255_ = lean_ctor_get_uint8(v_cfg_253_, sizeof(void*)*4);
v_apiEndpoint_256_ = lean_ctor_get(v_cfg_253_, 1);
v_artifactEndpoint_257_ = lean_ctor_get(v_cfg_253_, 2);
v_revisionEndpoint_258_ = lean_ctor_get(v_cfg_253_, 3);
v_isSharedCheck_266_ = !lean_is_exclusive(v_cfg_253_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v_cfg_253_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_revisionEndpoint_258_);
lean_inc(v_artifactEndpoint_257_);
lean_inc(v_apiEndpoint_256_);
lean_inc(v_name_254_);
lean_dec(v_cfg_253_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_apply_1(v_f_252_, v_artifactEndpoint_257_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 2, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_name_254_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_apiEndpoint_256_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v_revisionEndpoint_258_);
lean_ctor_set_uint8(v_reuseFailAlloc_265_, sizeof(void*)*4, v_kind_255_);
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
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(lean_object* v_cfg_277_){
_start:
{
lean_object* v_revisionEndpoint_278_; 
v_revisionEndpoint_278_ = lean_ctor_get(v_cfg_277_, 3);
lean_inc_ref(v_revisionEndpoint_278_);
return v_revisionEndpoint_278_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed(lean_object* v_cfg_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(v_cfg_279_);
lean_dec_ref(v_cfg_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1(lean_object* v_val_281_, lean_object* v_cfg_282_){
_start:
{
lean_object* v_name_283_; uint8_t v_kind_284_; lean_object* v_apiEndpoint_285_; lean_object* v_artifactEndpoint_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_name_283_ = lean_ctor_get(v_cfg_282_, 0);
v_kind_284_ = lean_ctor_get_uint8(v_cfg_282_, sizeof(void*)*4);
v_apiEndpoint_285_ = lean_ctor_get(v_cfg_282_, 1);
v_artifactEndpoint_286_ = lean_ctor_get(v_cfg_282_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_cfg_282_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_cfg_282_, 3);
lean_dec(v_unused_294_);
v___x_288_ = v_cfg_282_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_artifactEndpoint_286_);
lean_inc(v_apiEndpoint_285_);
lean_inc(v_name_283_);
lean_dec(v_cfg_282_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 3, v_val_281_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_name_283_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_apiEndpoint_285_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_artifactEndpoint_286_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_val_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*4, v_kind_284_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2(lean_object* v_f_295_, lean_object* v_cfg_296_){
_start:
{
lean_object* v_name_297_; uint8_t v_kind_298_; lean_object* v_apiEndpoint_299_; lean_object* v_artifactEndpoint_300_; lean_object* v_revisionEndpoint_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_309_; 
v_name_297_ = lean_ctor_get(v_cfg_296_, 0);
v_kind_298_ = lean_ctor_get_uint8(v_cfg_296_, sizeof(void*)*4);
v_apiEndpoint_299_ = lean_ctor_get(v_cfg_296_, 1);
v_artifactEndpoint_300_ = lean_ctor_get(v_cfg_296_, 2);
v_revisionEndpoint_301_ = lean_ctor_get(v_cfg_296_, 3);
v_isSharedCheck_309_ = !lean_is_exclusive(v_cfg_296_);
if (v_isSharedCheck_309_ == 0)
{
v___x_303_ = v_cfg_296_;
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_revisionEndpoint_301_);
lean_inc(v_artifactEndpoint_300_);
lean_inc(v_apiEndpoint_299_);
lean_inc(v_name_297_);
lean_dec(v_cfg_296_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_apply_1(v_f_295_, v_revisionEndpoint_301_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 3, v___x_305_);
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_name_297_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_apiEndpoint_299_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_artifactEndpoint_300_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v___x_305_);
lean_ctor_set_uint8(v_reuseFailAlloc_308_, sizeof(void*)*4, v_kind_298_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__3));
v___x_330_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_331_ = lean_array_push(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__7));
v___x_340_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__4, &l_Lake_CacheServiceConfig___fields___closed__4_once, _init_l_Lake_CacheServiceConfig___fields___closed__4);
v___x_341_ = lean_array_push(v___x_340_, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__11));
v___x_350_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__8, &l_Lake_CacheServiceConfig___fields___closed__8_once, _init_l_Lake_CacheServiceConfig___fields___closed__8);
v___x_351_ = lean_array_push(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__15));
v___x_360_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__12, &l_Lake_CacheServiceConfig___fields___closed__12_once, _init_l_Lake_CacheServiceConfig___fields___closed__12);
v___x_361_ = lean_array_push(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__19));
v___x_370_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__16, &l_Lake_CacheServiceConfig___fields___closed__16_once, _init_l_Lake_CacheServiceConfig___fields___closed__16);
v___x_371_ = lean_array_push(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__23));
v___x_380_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__20, &l_Lake_CacheServiceConfig___fields___closed__20_once, _init_l_Lake_CacheServiceConfig___fields___closed__20);
v___x_381_ = lean_array_push(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__24, &l_Lake_CacheServiceConfig___fields___closed__24_once, _init_l_Lake_CacheServiceConfig___fields___closed__24);
return v___x_382_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigFields(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lake_CacheServiceConfig___fields;
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_instConfigInfo___lam__0(lean_object* v_x1_384_, lean_object* v_x2_385_){
_start:
{
lean_object* v_name_386_; lean_object* v___x_387_; 
v_name_386_ = lean_ctor_get(v_x2_385_, 0);
lean_inc(v_name_386_);
v___x_387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_386_, v_x2_385_, v_x1_384_);
return v___x_387_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = l_Lake_CacheServiceConfig___fields;
v___x_389_ = lean_array_get_size(v___x_388_);
return v___x_389_;
}
}
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_409_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_nat_dec_lt(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_box(1);
v___x_414_ = l_Lake_CacheServiceConfig___fields;
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_412_);
return v___x_415_;
}
}
static size_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_417_; size_t v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_418_ = lean_usize_of_nat(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_419_; size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v___f_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_419_ = lean_box(1);
v___x_420_ = lean_usize_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__14, &l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14);
v___x_421_ = ((size_t)0ULL);
v___x_422_ = l_Lake_CacheServiceConfig___fields;
v___f_423_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_424_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_424_, v___f_423_, v___x_422_, v___x_421_, v___x_420_, v___x_419_);
return v___x_425_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__15, &l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15);
v___x_428_ = l_Lake_CacheServiceConfig___fields;
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_426_);
return v___x_429_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__11, &l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__16, &l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0(lean_object* v_cfg_441_){
_start:
{
lean_object* v_defaultService_442_; 
v_defaultService_442_ = lean_ctor_get(v_cfg_441_, 0);
lean_inc_ref(v_defaultService_442_);
return v_defaultService_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0___boxed(lean_object* v_cfg_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lake_CacheConfig_defaultService___proj___lam__0(v_cfg_443_);
lean_dec_ref(v_cfg_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__1(lean_object* v_val_445_, lean_object* v_cfg_446_){
_start:
{
lean_object* v_defaultUploadService_447_; lean_object* v_services_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_defaultUploadService_447_ = lean_ctor_get(v_cfg_446_, 1);
v_services_448_ = lean_ctor_get(v_cfg_446_, 2);
v_isSharedCheck_455_ = !lean_is_exclusive(v_cfg_446_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v_cfg_446_, 0);
lean_dec(v_unused_456_);
v___x_450_ = v_cfg_446_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_services_448_);
lean_inc(v_defaultUploadService_447_);
lean_dec(v_cfg_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_val_445_);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_val_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_defaultUploadService_447_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_services_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__2(lean_object* v_f_457_, lean_object* v_cfg_458_){
_start:
{
lean_object* v_defaultService_459_; lean_object* v_defaultUploadService_460_; lean_object* v_services_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
v_defaultService_459_ = lean_ctor_get(v_cfg_458_, 0);
v_defaultUploadService_460_ = lean_ctor_get(v_cfg_458_, 1);
v_services_461_ = lean_ctor_get(v_cfg_458_, 2);
v_isSharedCheck_469_ = !lean_is_exclusive(v_cfg_458_);
if (v_isSharedCheck_469_ == 0)
{
v___x_463_ = v_cfg_458_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_services_461_);
lean_inc(v_defaultUploadService_460_);
lean_inc(v_defaultService_459_);
lean_dec(v_cfg_458_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_apply_1(v_f_457_, v_defaultService_459_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_defaultUploadService_460_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_services_461_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3(lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3___boxed(lean_object* v_x_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lake_CacheConfig_defaultService___proj___lam__3(v_x_472_);
lean_dec_ref(v_x_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0(lean_object* v_cfg_485_){
_start:
{
lean_object* v_defaultUploadService_486_; 
v_defaultUploadService_486_ = lean_ctor_get(v_cfg_485_, 1);
lean_inc_ref(v_defaultUploadService_486_);
return v_defaultUploadService_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed(lean_object* v_cfg_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lake_CacheConfig_defaultUploadService___proj___lam__0(v_cfg_487_);
lean_dec_ref(v_cfg_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__1(lean_object* v_val_489_, lean_object* v_cfg_490_){
_start:
{
lean_object* v_defaultService_491_; lean_object* v_services_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_defaultService_491_ = lean_ctor_get(v_cfg_490_, 0);
v_services_492_ = lean_ctor_get(v_cfg_490_, 2);
v_isSharedCheck_499_ = !lean_is_exclusive(v_cfg_490_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v_cfg_490_, 1);
lean_dec(v_unused_500_);
v___x_494_ = v_cfg_490_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_services_492_);
lean_inc(v_defaultService_491_);
lean_dec(v_cfg_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v_val_489_);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_defaultService_491_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_val_489_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_services_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__2(lean_object* v_f_501_, lean_object* v_cfg_502_){
_start:
{
lean_object* v_defaultService_503_; lean_object* v_defaultUploadService_504_; lean_object* v_services_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_513_; 
v_defaultService_503_ = lean_ctor_get(v_cfg_502_, 0);
v_defaultUploadService_504_ = lean_ctor_get(v_cfg_502_, 1);
v_services_505_ = lean_ctor_get(v_cfg_502_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v_cfg_502_);
if (v_isSharedCheck_513_ == 0)
{
v___x_507_ = v_cfg_502_;
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_services_505_);
lean_inc(v_defaultUploadService_504_);
lean_inc(v_defaultService_503_);
lean_dec(v_cfg_502_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_apply_1(v_f_501_, v_defaultUploadService_504_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_defaultService_503_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_services_505_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0(lean_object* v_cfg_524_){
_start:
{
lean_object* v_services_525_; 
v_services_525_ = lean_ctor_get(v_cfg_524_, 2);
lean_inc_ref(v_services_525_);
return v_services_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0___boxed(lean_object* v_cfg_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lake_CacheConfig_services___proj___lam__0(v_cfg_526_);
lean_dec_ref(v_cfg_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__1(lean_object* v_val_528_, lean_object* v_cfg_529_){
_start:
{
lean_object* v_defaultService_530_; lean_object* v_defaultUploadService_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_defaultService_530_ = lean_ctor_get(v_cfg_529_, 0);
v_defaultUploadService_531_ = lean_ctor_get(v_cfg_529_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_cfg_529_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_cfg_529_, 2);
lean_dec(v_unused_539_);
v___x_533_ = v_cfg_529_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_defaultUploadService_531_);
lean_inc(v_defaultService_530_);
lean_dec(v_cfg_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v_val_528_);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_defaultService_530_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_defaultUploadService_531_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_val_528_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__2(lean_object* v_f_540_, lean_object* v_cfg_541_){
_start:
{
lean_object* v_defaultService_542_; lean_object* v_defaultUploadService_543_; lean_object* v_services_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_defaultService_542_ = lean_ctor_get(v_cfg_541_, 0);
v_defaultUploadService_543_ = lean_ctor_get(v_cfg_541_, 1);
v_services_544_ = lean_ctor_get(v_cfg_541_, 2);
v_isSharedCheck_552_ = !lean_is_exclusive(v_cfg_541_);
if (v_isSharedCheck_552_ == 0)
{
v___x_546_ = v_cfg_541_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_services_544_);
lean_inc(v_defaultUploadService_543_);
lean_inc(v_defaultService_542_);
lean_dec(v_cfg_541_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_apply_1(v_f_540_, v_services_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 2, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_defaultService_542_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_defaultUploadService_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3(lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__0));
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3___boxed(lean_object* v_x_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lake_CacheConfig_services___proj___lam__3(v_x_555_);
lean_dec_ref(v_x_555_);
return v_res_556_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__2));
v___x_576_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_577_ = lean_array_push(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__7(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__6));
v___x_586_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__3, &l_Lake_CacheConfig___fields___closed__3_once, _init_l_Lake_CacheConfig___fields___closed__3);
v___x_587_ = lean_array_push(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__13(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__12));
v___x_600_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__7, &l_Lake_CacheConfig___fields___closed__7_once, _init_l_Lake_CacheConfig___fields___closed__7);
v___x_601_ = lean_array_push(v___x_600_, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__13, &l_Lake_CacheConfig___fields___closed__13_once, _init_l_Lake_CacheConfig___fields___closed__13);
return v___x_602_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigFields(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lake_CacheConfig___fields;
return v___x_603_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_Lake_CacheConfig___fields;
v___x_605_ = lean_array_get_size(v___x_604_);
return v___x_605_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_lt(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_box(1);
v___x_611_ = l_Lake_CacheConfig___fields;
v___x_612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
lean_ctor_set(v___x_612_, 2, v___x_609_);
return v___x_612_;
}
}
static size_t _init_l_Lake_CacheConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_613_; size_t v___x_614_; 
v___x_613_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_614_ = lean_usize_of_nat(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_615_; size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_615_ = lean_box(1);
v___x_616_ = lean_usize_once(&l_Lake_CacheConfig_instConfigInfo___closed__3, &l_Lake_CacheConfig_instConfigInfo___closed__3_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__3);
v___x_617_ = ((size_t)0ULL);
v___x_618_ = l_Lake_CacheConfig___fields;
v___f_619_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_620_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_620_, v___f_619_, v___x_618_, v___x_617_, v___x_616_, v___x_615_);
return v___x_621_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__4, &l_Lake_CacheConfig_instConfigInfo___closed__4_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__4);
v___x_624_ = l_Lake_CacheConfig___fields;
v___x_625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_622_);
return v___x_625_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__1, &l_Lake_CacheConfig_instConfigInfo___closed__1_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__1);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__5, &l_Lake_CacheConfig_instConfigInfo___closed__5_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__5);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0(lean_object* v_cfg_632_){
_start:
{
lean_inc_ref(v_cfg_632_);
return v_cfg_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0___boxed(lean_object* v_cfg_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lake_LakeConfig_cache___proj___lam__0(v_cfg_633_);
lean_dec_ref(v_cfg_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1(lean_object* v_val_635_, lean_object* v_cfg_636_){
_start:
{
lean_inc_ref(v_val_635_);
return v_val_635_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1___boxed(lean_object* v_val_637_, lean_object* v_cfg_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lake_LakeConfig_cache___proj___lam__1(v_val_637_, v_cfg_638_);
lean_dec_ref(v_cfg_638_);
lean_dec_ref(v_val_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__2(lean_object* v_f_640_, lean_object* v_cfg_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_apply_1(v_f_640_, v_cfg_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3(lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__1));
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3___boxed(lean_object* v_x_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lake_LakeConfig_cache___proj___lam__3(v_x_645_);
lean_dec_ref(v_x_645_);
return v_res_646_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l_Lake_LakeConfig___fields___closed__2));
v___x_666_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_667_ = lean_array_push(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields(void){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_once(&l_Lake_LakeConfig___fields___closed__3, &l_Lake_LakeConfig___fields___closed__3_once, _init_l_Lake_LakeConfig___fields___closed__3);
return v___x_668_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigFields(void){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lake_LakeConfig___fields;
return v___x_669_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = l_Lake_LakeConfig___fields;
v___x_671_ = lean_array_get_size(v___x_670_);
return v___x_671_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_nat_dec_lt(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_box(1);
v___x_677_ = l_Lake_LakeConfig___fields;
v___x_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_675_);
return v___x_678_;
}
}
static size_t _init_l_Lake_LakeConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_679_; size_t v___x_680_; 
v___x_679_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_680_ = lean_usize_of_nat(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_681_ = lean_box(1);
v___x_682_ = lean_usize_once(&l_Lake_LakeConfig_instConfigInfo___closed__3, &l_Lake_LakeConfig_instConfigInfo___closed__3_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__3);
v___x_683_ = ((size_t)0ULL);
v___x_684_ = l_Lake_LakeConfig___fields;
v___f_685_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_686_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_686_, v___f_685_, v___x_684_, v___x_683_, v___x_682_, v___x_681_);
return v___x_687_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__4, &l_Lake_LakeConfig_instConfigInfo___closed__4_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__4);
v___x_690_ = l_Lake_LakeConfig___fields;
v___x_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
lean_ctor_set(v___x_691_, 2, v___x_688_);
return v___x_691_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__1, &l_Lake_LakeConfig_instConfigInfo___closed__1_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__1);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_693_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__5, &l_Lake_LakeConfig_instConfigInfo___closed__5_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__5);
return v___x_694_;
}
}
}
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LakeConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedCacheServiceKind_default = _init_l_Lake_instInhabitedCacheServiceKind_default();
l_Lake_instInhabitedCacheServiceKind = _init_l_Lake_instInhabitedCacheServiceKind();
l_Lake_CacheServiceConfig___fields = _init_l_Lake_CacheServiceConfig___fields();
lean_mark_persistent(l_Lake_CacheServiceConfig___fields);
l_Lake_CacheServiceConfig_instConfigFields = _init_l_Lake_CacheServiceConfig_instConfigFields();
lean_mark_persistent(l_Lake_CacheServiceConfig_instConfigFields);
l_Lake_CacheServiceConfig_instConfigInfo = _init_l_Lake_CacheServiceConfig_instConfigInfo();
lean_mark_persistent(l_Lake_CacheServiceConfig_instConfigInfo);
l_Lake_CacheConfig___fields = _init_l_Lake_CacheConfig___fields();
lean_mark_persistent(l_Lake_CacheConfig___fields);
l_Lake_CacheConfig_instConfigFields = _init_l_Lake_CacheConfig_instConfigFields();
lean_mark_persistent(l_Lake_CacheConfig_instConfigFields);
l_Lake_CacheConfig_instConfigInfo = _init_l_Lake_CacheConfig_instConfigInfo();
lean_mark_persistent(l_Lake_CacheConfig_instConfigInfo);
l_Lake_LakeConfig___fields = _init_l_Lake_LakeConfig___fields();
lean_mark_persistent(l_Lake_LakeConfig___fields);
l_Lake_LakeConfig_instConfigFields = _init_l_Lake_LakeConfig_instConfigFields();
lean_mark_persistent(l_Lake_LakeConfig_instConfigFields);
l_Lake_LakeConfig_instConfigInfo = _init_l_Lake_LakeConfig_instConfigInfo();
lean_mark_persistent(l_Lake_LakeConfig_instConfigInfo);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_LakeConfig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_LakeConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LakeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_LakeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_LakeConfig(builtin);
}
#ifdef __cplusplus
}
#endif
