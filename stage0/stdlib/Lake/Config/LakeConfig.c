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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx___boxed(lean_object*);
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
static uint8_t l_Lake_CacheServiceConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_CacheServiceConfig_instConfigInfo___closed__15;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__16;
static lean_once_cell_t l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheServiceConfig_instConfigInfo___closed__17;
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
static uint8_t l_Lake_CacheConfig_instConfigInfo___closed__3;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_CacheConfig_instConfigInfo___closed__4;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig_instConfigInfo___closed__5;
static lean_once_cell_t l_Lake_CacheConfig_instConfigInfo___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheConfig_instConfigInfo___closed__6;
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
static uint8_t l_Lake_LakeConfig_instConfigInfo___closed__3;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_LakeConfig_instConfigInfo___closed__4;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeConfig_instConfigInfo___closed__5;
static lean_once_cell_t l_Lake_LakeConfig_instConfigInfo___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LakeConfig_instConfigInfo___closed__6;
LEAN_EXPORT lean_object* l_Lake_LakeConfig_instConfigInfo;
LEAN_EXPORT const lean_object* l_Lake_LakeConfig_instEmptyCollection = (const lean_object*)&l_Lake_instInhabitedCacheConfig_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_CacheServiceKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_CacheServiceKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lake_CacheServiceKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg(lean_object* v_undef_23_){
_start:
{
lean_inc(v_undef_23_);
return v_undef_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg___boxed(lean_object* v_undef_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_CacheServiceKind_undef_elim___redArg(v_undef_24_);
lean_dec(v_undef_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_undef_29_){
_start:
{
lean_inc(v_undef_29_);
return v_undef_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_undef_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lake_CacheServiceKind_undef_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_undef_33_);
lean_dec(v_undef_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg(lean_object* v_reservoir_36_){
_start:
{
lean_inc(v_reservoir_36_);
return v_reservoir_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg___boxed(lean_object* v_reservoir_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_CacheServiceKind_reservoir_elim___redArg(v_reservoir_37_);
lean_dec(v_reservoir_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_reservoir_42_){
_start:
{
lean_inc(v_reservoir_42_);
return v_reservoir_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_reservoir_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lake_CacheServiceKind_reservoir_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_reservoir_46_);
lean_dec(v_reservoir_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg(lean_object* v_s3_49_){
_start:
{
lean_inc(v_s3_49_);
return v_s3_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg___boxed(lean_object* v_s3_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lake_CacheServiceKind_s3_elim___redArg(v_s3_50_);
lean_dec(v_s3_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_s3_55_){
_start:
{
lean_inc(v_s3_55_);
return v_s3_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_s3_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lake_CacheServiceKind_s3_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_s3_59_);
lean_dec(v_s3_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f(lean_object* v_s_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__0));
v___x_74_ = lean_string_dec_eq(v_s_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__1));
v___x_76_ = lean_string_dec_eq(v_s_72_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__2));
return v___x_78_;
}
}
else
{
lean_object* v___x_79_; 
v___x_79_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__3));
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f___boxed(lean_object* v_s_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lake_CacheServiceKind_ofString_x3f(v_s_80_);
lean_dec_ref(v_s_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0(lean_object* v_cfg_88_){
_start:
{
lean_object* v_name_89_; 
v_name_89_ = lean_ctor_get(v_cfg_88_, 0);
lean_inc_ref(v_name_89_);
return v_name_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0___boxed(lean_object* v_cfg_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lake_CacheServiceConfig_name___proj___lam__0(v_cfg_90_);
lean_dec_ref(v_cfg_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__1(lean_object* v_val_92_, lean_object* v_cfg_93_){
_start:
{
uint8_t v_kind_94_; lean_object* v_apiEndpoint_95_; lean_object* v_artifactEndpoint_96_; lean_object* v_revisionEndpoint_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_kind_94_ = lean_ctor_get_uint8(v_cfg_93_, sizeof(void*)*4);
v_apiEndpoint_95_ = lean_ctor_get(v_cfg_93_, 1);
v_artifactEndpoint_96_ = lean_ctor_get(v_cfg_93_, 2);
v_revisionEndpoint_97_ = lean_ctor_get(v_cfg_93_, 3);
v_isSharedCheck_104_ = !lean_is_exclusive(v_cfg_93_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_cfg_93_, 0);
lean_dec(v_unused_105_);
v___x_99_ = v_cfg_93_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_revisionEndpoint_97_);
lean_inc(v_artifactEndpoint_96_);
lean_inc(v_apiEndpoint_95_);
lean_dec(v_cfg_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v_val_92_);
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_val_92_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_apiEndpoint_95_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_artifactEndpoint_96_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_revisionEndpoint_97_);
lean_ctor_set_uint8(v_reuseFailAlloc_103_, sizeof(void*)*4, v_kind_94_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__2(lean_object* v_f_106_, lean_object* v_cfg_107_){
_start:
{
lean_object* v_name_108_; uint8_t v_kind_109_; lean_object* v_apiEndpoint_110_; lean_object* v_artifactEndpoint_111_; lean_object* v_revisionEndpoint_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
v_name_108_ = lean_ctor_get(v_cfg_107_, 0);
v_kind_109_ = lean_ctor_get_uint8(v_cfg_107_, sizeof(void*)*4);
v_apiEndpoint_110_ = lean_ctor_get(v_cfg_107_, 1);
v_artifactEndpoint_111_ = lean_ctor_get(v_cfg_107_, 2);
v_revisionEndpoint_112_ = lean_ctor_get(v_cfg_107_, 3);
v_isSharedCheck_120_ = !lean_is_exclusive(v_cfg_107_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v_cfg_107_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_revisionEndpoint_112_);
lean_inc(v_artifactEndpoint_111_);
lean_inc(v_apiEndpoint_110_);
lean_inc(v_name_108_);
lean_dec(v_cfg_107_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = lean_apply_1(v_f_106_, v_name_108_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_apiEndpoint_110_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_artifactEndpoint_111_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_revisionEndpoint_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_119_, sizeof(void*)*4, v_kind_109_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3(lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3___boxed(lean_object* v_x_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lake_CacheServiceConfig_name___proj___lam__3(v_x_123_);
lean_dec_ref(v_x_123_);
return v_res_124_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__0(lean_object* v_cfg_136_){
_start:
{
uint8_t v_kind_137_; 
v_kind_137_ = lean_ctor_get_uint8(v_cfg_136_, sizeof(void*)*4);
return v_kind_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__0___boxed(lean_object* v_cfg_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lake_CacheServiceConfig_kind___proj___lam__0(v_cfg_138_);
lean_dec_ref(v_cfg_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1(uint8_t v_val_141_, lean_object* v_cfg_142_){
_start:
{
lean_object* v_name_143_; lean_object* v_apiEndpoint_144_; lean_object* v_artifactEndpoint_145_; lean_object* v_revisionEndpoint_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_name_143_ = lean_ctor_get(v_cfg_142_, 0);
v_apiEndpoint_144_ = lean_ctor_get(v_cfg_142_, 1);
v_artifactEndpoint_145_ = lean_ctor_get(v_cfg_142_, 2);
v_revisionEndpoint_146_ = lean_ctor_get(v_cfg_142_, 3);
v_isSharedCheck_153_ = !lean_is_exclusive(v_cfg_142_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v_cfg_142_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_revisionEndpoint_146_);
lean_inc(v_artifactEndpoint_145_);
lean_inc(v_apiEndpoint_144_);
lean_inc(v_name_143_);
lean_dec(v_cfg_142_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_name_143_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_apiEndpoint_144_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_artifactEndpoint_145_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_revisionEndpoint_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*4, v_val_141_);
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed(lean_object* v_val_154_, lean_object* v_cfg_155_){
_start:
{
uint8_t v_val_49__boxed_156_; lean_object* v_res_157_; 
v_val_49__boxed_156_ = lean_unbox(v_val_154_);
v_res_157_ = l_Lake_CacheServiceConfig_kind___proj___lam__1(v_val_49__boxed_156_, v_cfg_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__2(lean_object* v_f_158_, lean_object* v_cfg_159_){
_start:
{
lean_object* v_name_160_; uint8_t v_kind_161_; lean_object* v_apiEndpoint_162_; lean_object* v_artifactEndpoint_163_; lean_object* v_revisionEndpoint_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_174_; 
v_name_160_ = lean_ctor_get(v_cfg_159_, 0);
v_kind_161_ = lean_ctor_get_uint8(v_cfg_159_, sizeof(void*)*4);
v_apiEndpoint_162_ = lean_ctor_get(v_cfg_159_, 1);
v_artifactEndpoint_163_ = lean_ctor_get(v_cfg_159_, 2);
v_revisionEndpoint_164_ = lean_ctor_get(v_cfg_159_, 3);
v_isSharedCheck_174_ = !lean_is_exclusive(v_cfg_159_);
if (v_isSharedCheck_174_ == 0)
{
v___x_166_ = v_cfg_159_;
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_revisionEndpoint_164_);
lean_inc(v_artifactEndpoint_163_);
lean_inc(v_apiEndpoint_162_);
lean_inc(v_name_160_);
lean_dec(v_cfg_159_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_168_ = lean_box(v_kind_161_);
v___x_169_ = lean_apply_1(v_f_158_, v___x_168_);
if (v_isShared_167_ == 0)
{
v___x_171_ = v___x_166_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_name_160_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_apiEndpoint_162_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_artifactEndpoint_163_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_revisionEndpoint_164_);
v___x_171_ = v_reuseFailAlloc_173_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
uint8_t v___x_172_; 
v___x_172_ = lean_unbox(v___x_169_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*4, v___x_172_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__3(lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed(lean_object* v_x_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Lake_CacheServiceConfig_kind___proj___lam__3(v_x_177_);
lean_dec_ref(v_x_177_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(lean_object* v_cfg_192_){
_start:
{
lean_object* v_apiEndpoint_193_; 
v_apiEndpoint_193_ = lean_ctor_get(v_cfg_192_, 1);
lean_inc_ref(v_apiEndpoint_193_);
return v_apiEndpoint_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed(lean_object* v_cfg_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(v_cfg_194_);
lean_dec_ref(v_cfg_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1(lean_object* v_val_196_, lean_object* v_cfg_197_){
_start:
{
lean_object* v_name_198_; uint8_t v_kind_199_; lean_object* v_artifactEndpoint_200_; lean_object* v_revisionEndpoint_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_name_198_ = lean_ctor_get(v_cfg_197_, 0);
v_kind_199_ = lean_ctor_get_uint8(v_cfg_197_, sizeof(void*)*4);
v_artifactEndpoint_200_ = lean_ctor_get(v_cfg_197_, 2);
v_revisionEndpoint_201_ = lean_ctor_get(v_cfg_197_, 3);
v_isSharedCheck_208_ = !lean_is_exclusive(v_cfg_197_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_cfg_197_, 1);
lean_dec(v_unused_209_);
v___x_203_ = v_cfg_197_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_revisionEndpoint_201_);
lean_inc(v_artifactEndpoint_200_);
lean_inc(v_name_198_);
lean_dec(v_cfg_197_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v_val_196_);
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_name_198_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_val_196_);
lean_ctor_set(v_reuseFailAlloc_207_, 2, v_artifactEndpoint_200_);
lean_ctor_set(v_reuseFailAlloc_207_, 3, v_revisionEndpoint_201_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, sizeof(void*)*4, v_kind_199_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2(lean_object* v_f_210_, lean_object* v_cfg_211_){
_start:
{
lean_object* v_name_212_; uint8_t v_kind_213_; lean_object* v_apiEndpoint_214_; lean_object* v_artifactEndpoint_215_; lean_object* v_revisionEndpoint_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
v_name_212_ = lean_ctor_get(v_cfg_211_, 0);
v_kind_213_ = lean_ctor_get_uint8(v_cfg_211_, sizeof(void*)*4);
v_apiEndpoint_214_ = lean_ctor_get(v_cfg_211_, 1);
v_artifactEndpoint_215_ = lean_ctor_get(v_cfg_211_, 2);
v_revisionEndpoint_216_ = lean_ctor_get(v_cfg_211_, 3);
v_isSharedCheck_224_ = !lean_is_exclusive(v_cfg_211_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v_cfg_211_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_revisionEndpoint_216_);
lean_inc(v_artifactEndpoint_215_);
lean_inc(v_apiEndpoint_214_);
lean_inc(v_name_212_);
lean_dec(v_cfg_211_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_apply_1(v_f_210_, v_apiEndpoint_214_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 1, v___x_220_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_name_212_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_artifactEndpoint_215_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v_revisionEndpoint_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_223_, sizeof(void*)*4, v_kind_213_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(lean_object* v_cfg_235_){
_start:
{
lean_object* v_artifactEndpoint_236_; 
v_artifactEndpoint_236_ = lean_ctor_get(v_cfg_235_, 2);
lean_inc_ref(v_artifactEndpoint_236_);
return v_artifactEndpoint_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed(lean_object* v_cfg_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(v_cfg_237_);
lean_dec_ref(v_cfg_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1(lean_object* v_val_239_, lean_object* v_cfg_240_){
_start:
{
lean_object* v_name_241_; uint8_t v_kind_242_; lean_object* v_apiEndpoint_243_; lean_object* v_revisionEndpoint_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_name_241_ = lean_ctor_get(v_cfg_240_, 0);
v_kind_242_ = lean_ctor_get_uint8(v_cfg_240_, sizeof(void*)*4);
v_apiEndpoint_243_ = lean_ctor_get(v_cfg_240_, 1);
v_revisionEndpoint_244_ = lean_ctor_get(v_cfg_240_, 3);
v_isSharedCheck_251_ = !lean_is_exclusive(v_cfg_240_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_cfg_240_, 2);
lean_dec(v_unused_252_);
v___x_246_ = v_cfg_240_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_revisionEndpoint_244_);
lean_inc(v_apiEndpoint_243_);
lean_inc(v_name_241_);
lean_dec(v_cfg_240_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 2, v_val_239_);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_name_241_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_apiEndpoint_243_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_val_239_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_revisionEndpoint_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_250_, sizeof(void*)*4, v_kind_242_);
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
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2(lean_object* v_f_253_, lean_object* v_cfg_254_){
_start:
{
lean_object* v_name_255_; uint8_t v_kind_256_; lean_object* v_apiEndpoint_257_; lean_object* v_artifactEndpoint_258_; lean_object* v_revisionEndpoint_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_name_255_ = lean_ctor_get(v_cfg_254_, 0);
v_kind_256_ = lean_ctor_get_uint8(v_cfg_254_, sizeof(void*)*4);
v_apiEndpoint_257_ = lean_ctor_get(v_cfg_254_, 1);
v_artifactEndpoint_258_ = lean_ctor_get(v_cfg_254_, 2);
v_revisionEndpoint_259_ = lean_ctor_get(v_cfg_254_, 3);
v_isSharedCheck_267_ = !lean_is_exclusive(v_cfg_254_);
if (v_isSharedCheck_267_ == 0)
{
v___x_261_ = v_cfg_254_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_revisionEndpoint_259_);
lean_inc(v_artifactEndpoint_258_);
lean_inc(v_apiEndpoint_257_);
lean_inc(v_name_255_);
lean_dec(v_cfg_254_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_apply_1(v_f_253_, v_artifactEndpoint_258_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 2, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_name_255_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_apiEndpoint_257_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_revisionEndpoint_259_);
lean_ctor_set_uint8(v_reuseFailAlloc_266_, sizeof(void*)*4, v_kind_256_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(lean_object* v_cfg_278_){
_start:
{
lean_object* v_revisionEndpoint_279_; 
v_revisionEndpoint_279_ = lean_ctor_get(v_cfg_278_, 3);
lean_inc_ref(v_revisionEndpoint_279_);
return v_revisionEndpoint_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed(lean_object* v_cfg_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(v_cfg_280_);
lean_dec_ref(v_cfg_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1(lean_object* v_val_282_, lean_object* v_cfg_283_){
_start:
{
lean_object* v_name_284_; uint8_t v_kind_285_; lean_object* v_apiEndpoint_286_; lean_object* v_artifactEndpoint_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_name_284_ = lean_ctor_get(v_cfg_283_, 0);
v_kind_285_ = lean_ctor_get_uint8(v_cfg_283_, sizeof(void*)*4);
v_apiEndpoint_286_ = lean_ctor_get(v_cfg_283_, 1);
v_artifactEndpoint_287_ = lean_ctor_get(v_cfg_283_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v_cfg_283_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_cfg_283_, 3);
lean_dec(v_unused_295_);
v___x_289_ = v_cfg_283_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_artifactEndpoint_287_);
lean_inc(v_apiEndpoint_286_);
lean_inc(v_name_284_);
lean_dec(v_cfg_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 3, v_val_282_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_name_284_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_apiEndpoint_286_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_artifactEndpoint_287_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_val_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_293_, sizeof(void*)*4, v_kind_285_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2(lean_object* v_f_296_, lean_object* v_cfg_297_){
_start:
{
lean_object* v_name_298_; uint8_t v_kind_299_; lean_object* v_apiEndpoint_300_; lean_object* v_artifactEndpoint_301_; lean_object* v_revisionEndpoint_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_310_; 
v_name_298_ = lean_ctor_get(v_cfg_297_, 0);
v_kind_299_ = lean_ctor_get_uint8(v_cfg_297_, sizeof(void*)*4);
v_apiEndpoint_300_ = lean_ctor_get(v_cfg_297_, 1);
v_artifactEndpoint_301_ = lean_ctor_get(v_cfg_297_, 2);
v_revisionEndpoint_302_ = lean_ctor_get(v_cfg_297_, 3);
v_isSharedCheck_310_ = !lean_is_exclusive(v_cfg_297_);
if (v_isSharedCheck_310_ == 0)
{
v___x_304_ = v_cfg_297_;
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_revisionEndpoint_302_);
lean_inc(v_artifactEndpoint_301_);
lean_inc(v_apiEndpoint_300_);
lean_inc(v_name_298_);
lean_dec(v_cfg_297_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_apply_1(v_f_296_, v_revisionEndpoint_302_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 3, v___x_306_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_name_298_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_apiEndpoint_300_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_artifactEndpoint_301_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v___x_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_309_, sizeof(void*)*4, v_kind_299_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__3));
v___x_331_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_332_ = lean_array_push(v___x_331_, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__7));
v___x_341_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__4, &l_Lake_CacheServiceConfig___fields___closed__4_once, _init_l_Lake_CacheServiceConfig___fields___closed__4);
v___x_342_ = lean_array_push(v___x_341_, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__11));
v___x_351_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__8, &l_Lake_CacheServiceConfig___fields___closed__8_once, _init_l_Lake_CacheServiceConfig___fields___closed__8);
v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__15));
v___x_361_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__12, &l_Lake_CacheServiceConfig___fields___closed__12_once, _init_l_Lake_CacheServiceConfig___fields___closed__12);
v___x_362_ = lean_array_push(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__19));
v___x_371_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__16, &l_Lake_CacheServiceConfig___fields___closed__16_once, _init_l_Lake_CacheServiceConfig___fields___closed__16);
v___x_372_ = lean_array_push(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__23));
v___x_381_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__20, &l_Lake_CacheServiceConfig___fields___closed__20_once, _init_l_Lake_CacheServiceConfig___fields___closed__20);
v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__24, &l_Lake_CacheServiceConfig___fields___closed__24_once, _init_l_Lake_CacheServiceConfig___fields___closed__24);
return v___x_383_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigFields(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lake_CacheServiceConfig___fields;
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_instConfigInfo___lam__0(lean_object* v_x1_385_, lean_object* v_x2_386_){
_start:
{
lean_object* v_name_387_; lean_object* v___x_388_; 
v_name_387_ = lean_ctor_get(v_x2_386_, 0);
lean_inc(v_name_387_);
v___x_388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_387_, v_x2_386_, v_x1_385_);
return v___x_388_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = l_Lake_CacheServiceConfig___fields;
v___x_390_ = lean_array_get_size(v___x_389_);
return v___x_390_;
}
}
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_nat_dec_lt(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_box(1);
v___x_415_ = l_Lake_CacheServiceConfig___fields;
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
return v___x_416_;
}
}
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_419_ = lean_nat_dec_le(v___x_418_, v___x_418_);
return v___x_419_;
}
}
static size_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_420_; size_t v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_421_ = lean_usize_of_nat(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_422_ = lean_box(1);
v___x_423_ = lean_usize_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__15, &l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15);
v___x_424_ = ((size_t)0ULL);
v___x_425_ = l_Lake_CacheServiceConfig___fields;
v___f_426_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_427_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_427_, v___f_426_, v___x_425_, v___x_424_, v___x_423_, v___x_422_);
return v___x_428_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__16, &l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16);
v___x_431_ = l_Lake_CacheServiceConfig___fields;
v___x_432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_429_);
return v___x_432_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__11, &l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
v___x_434_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__14, &l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14);
if (v___x_435_ == 0)
{
if (v___x_433_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_437_;
}
}
else
{
lean_object* v___x_438_; 
v___x_438_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0(lean_object* v_cfg_447_){
_start:
{
lean_object* v_defaultService_448_; 
v_defaultService_448_ = lean_ctor_get(v_cfg_447_, 0);
lean_inc_ref(v_defaultService_448_);
return v_defaultService_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0___boxed(lean_object* v_cfg_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lake_CacheConfig_defaultService___proj___lam__0(v_cfg_449_);
lean_dec_ref(v_cfg_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__1(lean_object* v_val_451_, lean_object* v_cfg_452_){
_start:
{
lean_object* v_defaultUploadService_453_; lean_object* v_services_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_defaultUploadService_453_ = lean_ctor_get(v_cfg_452_, 1);
v_services_454_ = lean_ctor_get(v_cfg_452_, 2);
v_isSharedCheck_461_ = !lean_is_exclusive(v_cfg_452_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_cfg_452_, 0);
lean_dec(v_unused_462_);
v___x_456_ = v_cfg_452_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_services_454_);
lean_inc(v_defaultUploadService_453_);
lean_dec(v_cfg_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_val_451_);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_val_451_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_defaultUploadService_453_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_services_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__2(lean_object* v_f_463_, lean_object* v_cfg_464_){
_start:
{
lean_object* v_defaultService_465_; lean_object* v_defaultUploadService_466_; lean_object* v_services_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v_defaultService_465_ = lean_ctor_get(v_cfg_464_, 0);
v_defaultUploadService_466_ = lean_ctor_get(v_cfg_464_, 1);
v_services_467_ = lean_ctor_get(v_cfg_464_, 2);
v_isSharedCheck_475_ = !lean_is_exclusive(v_cfg_464_);
if (v_isSharedCheck_475_ == 0)
{
v___x_469_ = v_cfg_464_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_services_467_);
lean_inc(v_defaultUploadService_466_);
lean_inc(v_defaultService_465_);
lean_dec(v_cfg_464_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_apply_1(v_f_463_, v_defaultService_465_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_defaultUploadService_466_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_services_467_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3(lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3___boxed(lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lake_CacheConfig_defaultService___proj___lam__3(v_x_478_);
lean_dec_ref(v_x_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0(lean_object* v_cfg_491_){
_start:
{
lean_object* v_defaultUploadService_492_; 
v_defaultUploadService_492_ = lean_ctor_get(v_cfg_491_, 1);
lean_inc_ref(v_defaultUploadService_492_);
return v_defaultUploadService_492_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed(lean_object* v_cfg_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lake_CacheConfig_defaultUploadService___proj___lam__0(v_cfg_493_);
lean_dec_ref(v_cfg_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__1(lean_object* v_val_495_, lean_object* v_cfg_496_){
_start:
{
lean_object* v_defaultService_497_; lean_object* v_services_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_defaultService_497_ = lean_ctor_get(v_cfg_496_, 0);
v_services_498_ = lean_ctor_get(v_cfg_496_, 2);
v_isSharedCheck_505_ = !lean_is_exclusive(v_cfg_496_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_cfg_496_, 1);
lean_dec(v_unused_506_);
v___x_500_ = v_cfg_496_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_services_498_);
lean_inc(v_defaultService_497_);
lean_dec(v_cfg_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v_val_495_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_defaultService_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_val_495_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_services_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__2(lean_object* v_f_507_, lean_object* v_cfg_508_){
_start:
{
lean_object* v_defaultService_509_; lean_object* v_defaultUploadService_510_; lean_object* v_services_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v_defaultService_509_ = lean_ctor_get(v_cfg_508_, 0);
v_defaultUploadService_510_ = lean_ctor_get(v_cfg_508_, 1);
v_services_511_ = lean_ctor_get(v_cfg_508_, 2);
v_isSharedCheck_519_ = !lean_is_exclusive(v_cfg_508_);
if (v_isSharedCheck_519_ == 0)
{
v___x_513_ = v_cfg_508_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_services_511_);
lean_inc(v_defaultUploadService_510_);
lean_inc(v_defaultService_509_);
lean_dec(v_cfg_508_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_apply_1(v_f_507_, v_defaultUploadService_510_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_defaultService_509_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_services_511_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0(lean_object* v_cfg_530_){
_start:
{
lean_object* v_services_531_; 
v_services_531_ = lean_ctor_get(v_cfg_530_, 2);
lean_inc_ref(v_services_531_);
return v_services_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0___boxed(lean_object* v_cfg_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lake_CacheConfig_services___proj___lam__0(v_cfg_532_);
lean_dec_ref(v_cfg_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__1(lean_object* v_val_534_, lean_object* v_cfg_535_){
_start:
{
lean_object* v_defaultService_536_; lean_object* v_defaultUploadService_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_defaultService_536_ = lean_ctor_get(v_cfg_535_, 0);
v_defaultUploadService_537_ = lean_ctor_get(v_cfg_535_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_cfg_535_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_cfg_535_, 2);
lean_dec(v_unused_545_);
v___x_539_ = v_cfg_535_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_defaultUploadService_537_);
lean_inc(v_defaultService_536_);
lean_dec(v_cfg_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 2, v_val_534_);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_defaultService_536_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_defaultUploadService_537_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_val_534_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__2(lean_object* v_f_546_, lean_object* v_cfg_547_){
_start:
{
lean_object* v_defaultService_548_; lean_object* v_defaultUploadService_549_; lean_object* v_services_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_defaultService_548_ = lean_ctor_get(v_cfg_547_, 0);
v_defaultUploadService_549_ = lean_ctor_get(v_cfg_547_, 1);
v_services_550_ = lean_ctor_get(v_cfg_547_, 2);
v_isSharedCheck_558_ = !lean_is_exclusive(v_cfg_547_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v_cfg_547_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_services_550_);
lean_inc(v_defaultUploadService_549_);
lean_inc(v_defaultService_548_);
lean_dec(v_cfg_547_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_apply_1(v_f_546_, v_services_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 2, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_defaultService_548_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_defaultUploadService_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3(lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__0));
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3___boxed(lean_object* v_x_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lake_CacheConfig_services___proj___lam__3(v_x_561_);
lean_dec_ref(v_x_561_);
return v_res_562_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__2));
v___x_582_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_583_ = lean_array_push(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__7(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__6));
v___x_592_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__3, &l_Lake_CacheConfig___fields___closed__3_once, _init_l_Lake_CacheConfig___fields___closed__3);
v___x_593_ = lean_array_push(v___x_592_, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__13(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__12));
v___x_606_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__7, &l_Lake_CacheConfig___fields___closed__7_once, _init_l_Lake_CacheConfig___fields___closed__7);
v___x_607_ = lean_array_push(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__13, &l_Lake_CacheConfig___fields___closed__13_once, _init_l_Lake_CacheConfig___fields___closed__13);
return v___x_608_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigFields(void){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lake_CacheConfig___fields;
return v___x_609_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = l_Lake_CacheConfig___fields;
v___x_611_ = lean_array_get_size(v___x_610_);
return v___x_611_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_lt(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_box(1);
v___x_617_ = l_Lake_CacheConfig___fields;
v___x_618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
lean_ctor_set(v___x_618_, 2, v___x_615_);
return v___x_618_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_620_ = lean_nat_dec_le(v___x_619_, v___x_619_);
return v___x_620_;
}
}
static size_t _init_l_Lake_CacheConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_621_; size_t v___x_622_; 
v___x_621_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_622_ = lean_usize_of_nat(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_623_; size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_623_ = lean_box(1);
v___x_624_ = lean_usize_once(&l_Lake_CacheConfig_instConfigInfo___closed__4, &l_Lake_CacheConfig_instConfigInfo___closed__4_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__4);
v___x_625_ = ((size_t)0ULL);
v___x_626_ = l_Lake_CacheConfig___fields;
v___f_627_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_628_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_628_, v___f_627_, v___x_626_, v___x_625_, v___x_624_, v___x_623_);
return v___x_629_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__5, &l_Lake_CacheConfig_instConfigInfo___closed__5_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__5);
v___x_632_ = l_Lake_CacheConfig___fields;
v___x_633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_630_);
return v___x_633_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__1, &l_Lake_CacheConfig_instConfigInfo___closed__1_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__1);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_635_;
}
else
{
uint8_t v___x_636_; 
v___x_636_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__3, &l_Lake_CacheConfig_instConfigInfo___closed__3_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__3);
if (v___x_636_ == 0)
{
if (v___x_634_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_637_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_638_;
}
}
else
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0(lean_object* v_cfg_643_){
_start:
{
lean_inc_ref(v_cfg_643_);
return v_cfg_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0___boxed(lean_object* v_cfg_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lake_LakeConfig_cache___proj___lam__0(v_cfg_644_);
lean_dec_ref(v_cfg_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1(lean_object* v_val_646_, lean_object* v_cfg_647_){
_start:
{
lean_inc_ref(v_val_646_);
return v_val_646_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1___boxed(lean_object* v_val_648_, lean_object* v_cfg_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lake_LakeConfig_cache___proj___lam__1(v_val_648_, v_cfg_649_);
lean_dec_ref(v_cfg_649_);
lean_dec_ref(v_val_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__2(lean_object* v_f_651_, lean_object* v_cfg_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = lean_apply_1(v_f_651_, v_cfg_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3(lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__1));
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3___boxed(lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lake_LakeConfig_cache___proj___lam__3(v_x_656_);
lean_dec_ref(v_x_656_);
return v_res_657_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = ((lean_object*)(l_Lake_LakeConfig___fields___closed__2));
v___x_677_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_678_ = lean_array_push(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields(void){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = lean_obj_once(&l_Lake_LakeConfig___fields___closed__3, &l_Lake_LakeConfig___fields___closed__3_once, _init_l_Lake_LakeConfig___fields___closed__3);
return v___x_679_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigFields(void){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lake_LakeConfig___fields;
return v___x_680_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = l_Lake_LakeConfig___fields;
v___x_682_ = lean_array_get_size(v___x_681_);
return v___x_682_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_nat_dec_lt(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_box(1);
v___x_688_ = l_Lake_LakeConfig___fields;
v___x_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
lean_ctor_set(v___x_689_, 2, v___x_686_);
return v___x_689_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_691_ = lean_nat_dec_le(v___x_690_, v___x_690_);
return v___x_691_;
}
}
static size_t _init_l_Lake_LakeConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_692_; size_t v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_693_ = lean_usize_of_nat(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___f_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_694_ = lean_box(1);
v___x_695_ = lean_usize_once(&l_Lake_LakeConfig_instConfigInfo___closed__4, &l_Lake_LakeConfig_instConfigInfo___closed__4_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__4);
v___x_696_ = ((size_t)0ULL);
v___x_697_ = l_Lake_LakeConfig___fields;
v___f_698_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_699_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_699_, v___f_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_700_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__5, &l_Lake_LakeConfig_instConfigInfo___closed__5_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__5);
v___x_703_ = l_Lake_LakeConfig___fields;
v___x_704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
lean_ctor_set(v___x_704_, 2, v___x_701_);
return v___x_704_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__1, &l_Lake_LakeConfig_instConfigInfo___closed__1_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__1);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_706_;
}
else
{
uint8_t v___x_707_; 
v___x_707_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__3, &l_Lake_LakeConfig_instConfigInfo___closed__3_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__3);
if (v___x_707_ == 0)
{
if (v___x_705_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_708_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_709_;
}
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_710_;
}
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
