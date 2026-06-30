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
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lake_CacheServiceKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lake_CacheServiceKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lake_CacheServiceKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lake_CacheServiceKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg(lean_object* v_undef_28_){
_start:
{
lean_inc(v_undef_28_);
return v_undef_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg___boxed(lean_object* v_undef_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lake_CacheServiceKind_undef_elim___redArg(v_undef_29_);
lean_dec(v_undef_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_undef_34_){
_start:
{
lean_inc(v_undef_34_);
return v_undef_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_undef_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lake_CacheServiceKind_undef_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_undef_38_);
lean_dec(v_undef_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg(lean_object* v_reservoir_41_){
_start:
{
lean_inc(v_reservoir_41_);
return v_reservoir_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg___boxed(lean_object* v_reservoir_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lake_CacheServiceKind_reservoir_elim___redArg(v_reservoir_42_);
lean_dec(v_reservoir_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_reservoir_47_){
_start:
{
lean_inc(v_reservoir_47_);
return v_reservoir_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_reservoir_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lake_CacheServiceKind_reservoir_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_reservoir_51_);
lean_dec(v_reservoir_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg(lean_object* v_s3_54_){
_start:
{
lean_inc(v_s3_54_);
return v_s3_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg___boxed(lean_object* v_s3_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_CacheServiceKind_s3_elim___redArg(v_s3_55_);
lean_dec(v_s3_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_s3_60_){
_start:
{
lean_inc(v_s3_60_);
return v_s3_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_s3_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lake_CacheServiceKind_s3_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_s3_64_);
lean_dec(v_s3_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f(lean_object* v_s_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__0));
v___x_79_ = lean_string_dec_eq(v_s_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__1));
v___x_81_ = lean_string_dec_eq(v_s_77_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__2));
return v___x_83_;
}
}
else
{
lean_object* v___x_84_; 
v___x_84_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__3));
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f___boxed(lean_object* v_s_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lake_CacheServiceKind_ofString_x3f(v_s_85_);
lean_dec_ref(v_s_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0(lean_object* v_cfg_93_){
_start:
{
lean_object* v_name_94_; 
v_name_94_ = lean_ctor_get(v_cfg_93_, 0);
lean_inc_ref(v_name_94_);
return v_name_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0___boxed(lean_object* v_cfg_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lake_CacheServiceConfig_name___proj___lam__0(v_cfg_95_);
lean_dec_ref(v_cfg_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__1(lean_object* v_val_97_, lean_object* v_cfg_98_){
_start:
{
uint8_t v_kind_99_; lean_object* v_apiEndpoint_100_; lean_object* v_artifactEndpoint_101_; lean_object* v_revisionEndpoint_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_kind_99_ = lean_ctor_get_uint8(v_cfg_98_, sizeof(void*)*4);
v_apiEndpoint_100_ = lean_ctor_get(v_cfg_98_, 1);
v_artifactEndpoint_101_ = lean_ctor_get(v_cfg_98_, 2);
v_revisionEndpoint_102_ = lean_ctor_get(v_cfg_98_, 3);
v_isSharedCheck_109_ = !lean_is_exclusive(v_cfg_98_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v_cfg_98_, 0);
lean_dec(v_unused_110_);
v___x_104_ = v_cfg_98_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_revisionEndpoint_102_);
lean_inc(v_artifactEndpoint_101_);
lean_inc(v_apiEndpoint_100_);
lean_dec(v_cfg_98_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_val_97_);
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_val_97_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_apiEndpoint_100_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v_artifactEndpoint_101_);
lean_ctor_set(v_reuseFailAlloc_108_, 3, v_revisionEndpoint_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_108_, sizeof(void*)*4, v_kind_99_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__2(lean_object* v_f_111_, lean_object* v_cfg_112_){
_start:
{
lean_object* v_name_113_; uint8_t v_kind_114_; lean_object* v_apiEndpoint_115_; lean_object* v_artifactEndpoint_116_; lean_object* v_revisionEndpoint_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_name_113_ = lean_ctor_get(v_cfg_112_, 0);
v_kind_114_ = lean_ctor_get_uint8(v_cfg_112_, sizeof(void*)*4);
v_apiEndpoint_115_ = lean_ctor_get(v_cfg_112_, 1);
v_artifactEndpoint_116_ = lean_ctor_get(v_cfg_112_, 2);
v_revisionEndpoint_117_ = lean_ctor_get(v_cfg_112_, 3);
v_isSharedCheck_125_ = !lean_is_exclusive(v_cfg_112_);
if (v_isSharedCheck_125_ == 0)
{
v___x_119_ = v_cfg_112_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_revisionEndpoint_117_);
lean_inc(v_artifactEndpoint_116_);
lean_inc(v_apiEndpoint_115_);
lean_inc(v_name_113_);
lean_dec(v_cfg_112_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_apply_1(v_f_111_, v_name_113_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_apiEndpoint_115_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v_artifactEndpoint_116_);
lean_ctor_set(v_reuseFailAlloc_124_, 3, v_revisionEndpoint_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_124_, sizeof(void*)*4, v_kind_114_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3(lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3___boxed(lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lake_CacheServiceConfig_name___proj___lam__3(v_x_128_);
lean_dec_ref(v_x_128_);
return v_res_129_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__0(lean_object* v_cfg_141_){
_start:
{
uint8_t v_kind_142_; 
v_kind_142_ = lean_ctor_get_uint8(v_cfg_141_, sizeof(void*)*4);
return v_kind_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__0___boxed(lean_object* v_cfg_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lake_CacheServiceConfig_kind___proj___lam__0(v_cfg_143_);
lean_dec_ref(v_cfg_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1(uint8_t v_val_146_, lean_object* v_cfg_147_){
_start:
{
lean_object* v_name_148_; lean_object* v_apiEndpoint_149_; lean_object* v_artifactEndpoint_150_; lean_object* v_revisionEndpoint_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_name_148_ = lean_ctor_get(v_cfg_147_, 0);
v_apiEndpoint_149_ = lean_ctor_get(v_cfg_147_, 1);
v_artifactEndpoint_150_ = lean_ctor_get(v_cfg_147_, 2);
v_revisionEndpoint_151_ = lean_ctor_get(v_cfg_147_, 3);
v_isSharedCheck_158_ = !lean_is_exclusive(v_cfg_147_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v_cfg_147_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_revisionEndpoint_151_);
lean_inc(v_artifactEndpoint_150_);
lean_inc(v_apiEndpoint_149_);
lean_inc(v_name_148_);
lean_dec(v_cfg_147_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_name_148_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_apiEndpoint_149_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_artifactEndpoint_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_revisionEndpoint_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*4, v_val_146_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed(lean_object* v_val_159_, lean_object* v_cfg_160_){
_start:
{
uint8_t v_val_49__boxed_161_; lean_object* v_res_162_; 
v_val_49__boxed_161_ = lean_unbox(v_val_159_);
v_res_162_ = l_Lake_CacheServiceConfig_kind___proj___lam__1(v_val_49__boxed_161_, v_cfg_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__2(lean_object* v_f_163_, lean_object* v_cfg_164_){
_start:
{
lean_object* v_name_165_; uint8_t v_kind_166_; lean_object* v_apiEndpoint_167_; lean_object* v_artifactEndpoint_168_; lean_object* v_revisionEndpoint_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_name_165_ = lean_ctor_get(v_cfg_164_, 0);
v_kind_166_ = lean_ctor_get_uint8(v_cfg_164_, sizeof(void*)*4);
v_apiEndpoint_167_ = lean_ctor_get(v_cfg_164_, 1);
v_artifactEndpoint_168_ = lean_ctor_get(v_cfg_164_, 2);
v_revisionEndpoint_169_ = lean_ctor_get(v_cfg_164_, 3);
v_isSharedCheck_179_ = !lean_is_exclusive(v_cfg_164_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_cfg_164_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_revisionEndpoint_169_);
lean_inc(v_artifactEndpoint_168_);
lean_inc(v_apiEndpoint_167_);
lean_inc(v_name_165_);
lean_dec(v_cfg_164_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_box(v_kind_166_);
v___x_174_ = lean_apply_1(v_f_163_, v___x_173_);
if (v_isShared_172_ == 0)
{
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_name_165_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_apiEndpoint_167_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_artifactEndpoint_168_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_revisionEndpoint_169_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
uint8_t v___x_177_; 
v___x_177_ = lean_unbox(v___x_174_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*4, v___x_177_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__3(lean_object* v_x_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed(lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Lake_CacheServiceConfig_kind___proj___lam__3(v_x_182_);
lean_dec_ref(v_x_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(lean_object* v_cfg_197_){
_start:
{
lean_object* v_apiEndpoint_198_; 
v_apiEndpoint_198_ = lean_ctor_get(v_cfg_197_, 1);
lean_inc_ref(v_apiEndpoint_198_);
return v_apiEndpoint_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed(lean_object* v_cfg_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(v_cfg_199_);
lean_dec_ref(v_cfg_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1(lean_object* v_val_201_, lean_object* v_cfg_202_){
_start:
{
lean_object* v_name_203_; uint8_t v_kind_204_; lean_object* v_artifactEndpoint_205_; lean_object* v_revisionEndpoint_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_name_203_ = lean_ctor_get(v_cfg_202_, 0);
v_kind_204_ = lean_ctor_get_uint8(v_cfg_202_, sizeof(void*)*4);
v_artifactEndpoint_205_ = lean_ctor_get(v_cfg_202_, 2);
v_revisionEndpoint_206_ = lean_ctor_get(v_cfg_202_, 3);
v_isSharedCheck_213_ = !lean_is_exclusive(v_cfg_202_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_cfg_202_, 1);
lean_dec(v_unused_214_);
v___x_208_ = v_cfg_202_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_revisionEndpoint_206_);
lean_inc(v_artifactEndpoint_205_);
lean_inc(v_name_203_);
lean_dec(v_cfg_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v_val_201_);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_name_203_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_val_201_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_artifactEndpoint_205_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_revisionEndpoint_206_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*4, v_kind_204_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2(lean_object* v_f_215_, lean_object* v_cfg_216_){
_start:
{
lean_object* v_name_217_; uint8_t v_kind_218_; lean_object* v_apiEndpoint_219_; lean_object* v_artifactEndpoint_220_; lean_object* v_revisionEndpoint_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_name_217_ = lean_ctor_get(v_cfg_216_, 0);
v_kind_218_ = lean_ctor_get_uint8(v_cfg_216_, sizeof(void*)*4);
v_apiEndpoint_219_ = lean_ctor_get(v_cfg_216_, 1);
v_artifactEndpoint_220_ = lean_ctor_get(v_cfg_216_, 2);
v_revisionEndpoint_221_ = lean_ctor_get(v_cfg_216_, 3);
v_isSharedCheck_229_ = !lean_is_exclusive(v_cfg_216_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v_cfg_216_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_revisionEndpoint_221_);
lean_inc(v_artifactEndpoint_220_);
lean_inc(v_apiEndpoint_219_);
lean_inc(v_name_217_);
lean_dec(v_cfg_216_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_apply_1(v_f_215_, v_apiEndpoint_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_name_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_artifactEndpoint_220_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_revisionEndpoint_221_);
lean_ctor_set_uint8(v_reuseFailAlloc_228_, sizeof(void*)*4, v_kind_218_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(lean_object* v_cfg_240_){
_start:
{
lean_object* v_artifactEndpoint_241_; 
v_artifactEndpoint_241_ = lean_ctor_get(v_cfg_240_, 2);
lean_inc_ref(v_artifactEndpoint_241_);
return v_artifactEndpoint_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed(lean_object* v_cfg_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(v_cfg_242_);
lean_dec_ref(v_cfg_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1(lean_object* v_val_244_, lean_object* v_cfg_245_){
_start:
{
lean_object* v_name_246_; uint8_t v_kind_247_; lean_object* v_apiEndpoint_248_; lean_object* v_revisionEndpoint_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_name_246_ = lean_ctor_get(v_cfg_245_, 0);
v_kind_247_ = lean_ctor_get_uint8(v_cfg_245_, sizeof(void*)*4);
v_apiEndpoint_248_ = lean_ctor_get(v_cfg_245_, 1);
v_revisionEndpoint_249_ = lean_ctor_get(v_cfg_245_, 3);
v_isSharedCheck_256_ = !lean_is_exclusive(v_cfg_245_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_cfg_245_, 2);
lean_dec(v_unused_257_);
v___x_251_ = v_cfg_245_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_revisionEndpoint_249_);
lean_inc(v_apiEndpoint_248_);
lean_inc(v_name_246_);
lean_dec(v_cfg_245_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 2, v_val_244_);
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_name_246_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_apiEndpoint_248_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_val_244_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_revisionEndpoint_249_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*4, v_kind_247_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2(lean_object* v_f_258_, lean_object* v_cfg_259_){
_start:
{
lean_object* v_name_260_; uint8_t v_kind_261_; lean_object* v_apiEndpoint_262_; lean_object* v_artifactEndpoint_263_; lean_object* v_revisionEndpoint_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_name_260_ = lean_ctor_get(v_cfg_259_, 0);
v_kind_261_ = lean_ctor_get_uint8(v_cfg_259_, sizeof(void*)*4);
v_apiEndpoint_262_ = lean_ctor_get(v_cfg_259_, 1);
v_artifactEndpoint_263_ = lean_ctor_get(v_cfg_259_, 2);
v_revisionEndpoint_264_ = lean_ctor_get(v_cfg_259_, 3);
v_isSharedCheck_272_ = !lean_is_exclusive(v_cfg_259_);
if (v_isSharedCheck_272_ == 0)
{
v___x_266_ = v_cfg_259_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_revisionEndpoint_264_);
lean_inc(v_artifactEndpoint_263_);
lean_inc(v_apiEndpoint_262_);
lean_inc(v_name_260_);
lean_dec(v_cfg_259_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_apply_1(v_f_258_, v_artifactEndpoint_263_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 2, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_name_260_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_apiEndpoint_262_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_revisionEndpoint_264_);
lean_ctor_set_uint8(v_reuseFailAlloc_271_, sizeof(void*)*4, v_kind_261_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(lean_object* v_cfg_283_){
_start:
{
lean_object* v_revisionEndpoint_284_; 
v_revisionEndpoint_284_ = lean_ctor_get(v_cfg_283_, 3);
lean_inc_ref(v_revisionEndpoint_284_);
return v_revisionEndpoint_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed(lean_object* v_cfg_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(v_cfg_285_);
lean_dec_ref(v_cfg_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1(lean_object* v_val_287_, lean_object* v_cfg_288_){
_start:
{
lean_object* v_name_289_; uint8_t v_kind_290_; lean_object* v_apiEndpoint_291_; lean_object* v_artifactEndpoint_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_name_289_ = lean_ctor_get(v_cfg_288_, 0);
v_kind_290_ = lean_ctor_get_uint8(v_cfg_288_, sizeof(void*)*4);
v_apiEndpoint_291_ = lean_ctor_get(v_cfg_288_, 1);
v_artifactEndpoint_292_ = lean_ctor_get(v_cfg_288_, 2);
v_isSharedCheck_299_ = !lean_is_exclusive(v_cfg_288_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_cfg_288_, 3);
lean_dec(v_unused_300_);
v___x_294_ = v_cfg_288_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_artifactEndpoint_292_);
lean_inc(v_apiEndpoint_291_);
lean_inc(v_name_289_);
lean_dec(v_cfg_288_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 3, v_val_287_);
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_name_289_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_apiEndpoint_291_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_artifactEndpoint_292_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_val_287_);
lean_ctor_set_uint8(v_reuseFailAlloc_298_, sizeof(void*)*4, v_kind_290_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2(lean_object* v_f_301_, lean_object* v_cfg_302_){
_start:
{
lean_object* v_name_303_; uint8_t v_kind_304_; lean_object* v_apiEndpoint_305_; lean_object* v_artifactEndpoint_306_; lean_object* v_revisionEndpoint_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_315_; 
v_name_303_ = lean_ctor_get(v_cfg_302_, 0);
v_kind_304_ = lean_ctor_get_uint8(v_cfg_302_, sizeof(void*)*4);
v_apiEndpoint_305_ = lean_ctor_get(v_cfg_302_, 1);
v_artifactEndpoint_306_ = lean_ctor_get(v_cfg_302_, 2);
v_revisionEndpoint_307_ = lean_ctor_get(v_cfg_302_, 3);
v_isSharedCheck_315_ = !lean_is_exclusive(v_cfg_302_);
if (v_isSharedCheck_315_ == 0)
{
v___x_309_ = v_cfg_302_;
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_revisionEndpoint_307_);
lean_inc(v_artifactEndpoint_306_);
lean_inc(v_apiEndpoint_305_);
lean_inc(v_name_303_);
lean_dec(v_cfg_302_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_apply_1(v_f_301_, v_revisionEndpoint_307_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v___x_311_);
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_name_303_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_apiEndpoint_305_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_artifactEndpoint_306_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v___x_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_314_, sizeof(void*)*4, v_kind_304_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__3));
v___x_336_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_337_ = lean_array_push(v___x_336_, v___x_335_);
return v___x_337_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__7));
v___x_346_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__4, &l_Lake_CacheServiceConfig___fields___closed__4_once, _init_l_Lake_CacheServiceConfig___fields___closed__4);
v___x_347_ = lean_array_push(v___x_346_, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__11));
v___x_356_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__8, &l_Lake_CacheServiceConfig___fields___closed__8_once, _init_l_Lake_CacheServiceConfig___fields___closed__8);
v___x_357_ = lean_array_push(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__15));
v___x_366_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__12, &l_Lake_CacheServiceConfig___fields___closed__12_once, _init_l_Lake_CacheServiceConfig___fields___closed__12);
v___x_367_ = lean_array_push(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__19));
v___x_376_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__16, &l_Lake_CacheServiceConfig___fields___closed__16_once, _init_l_Lake_CacheServiceConfig___fields___closed__16);
v___x_377_ = lean_array_push(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__23));
v___x_386_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__20, &l_Lake_CacheServiceConfig___fields___closed__20_once, _init_l_Lake_CacheServiceConfig___fields___closed__20);
v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__24, &l_Lake_CacheServiceConfig___fields___closed__24_once, _init_l_Lake_CacheServiceConfig___fields___closed__24);
return v___x_388_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigFields(void){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lake_CacheServiceConfig___fields;
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_instConfigInfo___lam__0(lean_object* v_x1_390_, lean_object* v_x2_391_){
_start:
{
lean_object* v_name_392_; lean_object* v___x_393_; 
v_name_392_ = lean_ctor_get(v_x2_391_, 0);
lean_inc(v_name_392_);
v___x_393_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_392_, v_x2_391_, v_x1_390_);
return v___x_393_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = l_Lake_CacheServiceConfig___fields;
v___x_395_ = lean_array_get_size(v___x_394_);
return v___x_395_;
}
}
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_nat_dec_lt(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_box(1);
v___x_420_ = l_Lake_CacheServiceConfig___fields;
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_418_);
return v___x_421_;
}
}
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_424_ = lean_nat_dec_le(v___x_423_, v___x_423_);
return v___x_424_;
}
}
static size_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_425_; size_t v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_426_ = lean_usize_of_nat(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_427_ = lean_box(1);
v___x_428_ = lean_usize_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__15, &l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15);
v___x_429_ = ((size_t)0ULL);
v___x_430_ = l_Lake_CacheServiceConfig___fields;
v___f_431_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_432_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_432_, v___f_431_, v___x_430_, v___x_429_, v___x_428_, v___x_427_);
return v___x_433_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__16, &l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16);
v___x_436_ = l_Lake_CacheServiceConfig___fields;
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_434_);
return v___x_437_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__11, &l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
v___x_439_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_439_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__14, &l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14);
if (v___x_440_ == 0)
{
if (v___x_438_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_441_;
}
else
{
lean_object* v___x_442_; 
v___x_442_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0(lean_object* v_cfg_452_){
_start:
{
lean_object* v_defaultService_453_; 
v_defaultService_453_ = lean_ctor_get(v_cfg_452_, 0);
lean_inc_ref(v_defaultService_453_);
return v_defaultService_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0___boxed(lean_object* v_cfg_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lake_CacheConfig_defaultService___proj___lam__0(v_cfg_454_);
lean_dec_ref(v_cfg_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__1(lean_object* v_val_456_, lean_object* v_cfg_457_){
_start:
{
lean_object* v_defaultUploadService_458_; lean_object* v_services_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_defaultUploadService_458_ = lean_ctor_get(v_cfg_457_, 1);
v_services_459_ = lean_ctor_get(v_cfg_457_, 2);
v_isSharedCheck_466_ = !lean_is_exclusive(v_cfg_457_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_cfg_457_, 0);
lean_dec(v_unused_467_);
v___x_461_ = v_cfg_457_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_services_459_);
lean_inc(v_defaultUploadService_458_);
lean_dec(v_cfg_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v_val_456_);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_val_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_defaultUploadService_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_services_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__2(lean_object* v_f_468_, lean_object* v_cfg_469_){
_start:
{
lean_object* v_defaultService_470_; lean_object* v_defaultUploadService_471_; lean_object* v_services_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_480_; 
v_defaultService_470_ = lean_ctor_get(v_cfg_469_, 0);
v_defaultUploadService_471_ = lean_ctor_get(v_cfg_469_, 1);
v_services_472_ = lean_ctor_get(v_cfg_469_, 2);
v_isSharedCheck_480_ = !lean_is_exclusive(v_cfg_469_);
if (v_isSharedCheck_480_ == 0)
{
v___x_474_ = v_cfg_469_;
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_services_472_);
lean_inc(v_defaultUploadService_471_);
lean_inc(v_defaultService_470_);
lean_dec(v_cfg_469_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_apply_1(v_f_468_, v_defaultService_470_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_defaultUploadService_471_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_services_472_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3(lean_object* v_x_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3___boxed(lean_object* v_x_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lake_CacheConfig_defaultService___proj___lam__3(v_x_483_);
lean_dec_ref(v_x_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0(lean_object* v_cfg_496_){
_start:
{
lean_object* v_defaultUploadService_497_; 
v_defaultUploadService_497_ = lean_ctor_get(v_cfg_496_, 1);
lean_inc_ref(v_defaultUploadService_497_);
return v_defaultUploadService_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed(lean_object* v_cfg_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lake_CacheConfig_defaultUploadService___proj___lam__0(v_cfg_498_);
lean_dec_ref(v_cfg_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__1(lean_object* v_val_500_, lean_object* v_cfg_501_){
_start:
{
lean_object* v_defaultService_502_; lean_object* v_services_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_defaultService_502_ = lean_ctor_get(v_cfg_501_, 0);
v_services_503_ = lean_ctor_get(v_cfg_501_, 2);
v_isSharedCheck_510_ = !lean_is_exclusive(v_cfg_501_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_cfg_501_, 1);
lean_dec(v_unused_511_);
v___x_505_ = v_cfg_501_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_services_503_);
lean_inc(v_defaultService_502_);
lean_dec(v_cfg_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v_val_500_);
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_defaultService_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_val_500_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_services_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__2(lean_object* v_f_512_, lean_object* v_cfg_513_){
_start:
{
lean_object* v_defaultService_514_; lean_object* v_defaultUploadService_515_; lean_object* v_services_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_defaultService_514_ = lean_ctor_get(v_cfg_513_, 0);
v_defaultUploadService_515_ = lean_ctor_get(v_cfg_513_, 1);
v_services_516_ = lean_ctor_get(v_cfg_513_, 2);
v_isSharedCheck_524_ = !lean_is_exclusive(v_cfg_513_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v_cfg_513_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_services_516_);
lean_inc(v_defaultUploadService_515_);
lean_inc(v_defaultService_514_);
lean_dec(v_cfg_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_apply_1(v_f_512_, v_defaultUploadService_515_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_defaultService_514_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_services_516_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0(lean_object* v_cfg_535_){
_start:
{
lean_object* v_services_536_; 
v_services_536_ = lean_ctor_get(v_cfg_535_, 2);
lean_inc_ref(v_services_536_);
return v_services_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0___boxed(lean_object* v_cfg_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lake_CacheConfig_services___proj___lam__0(v_cfg_537_);
lean_dec_ref(v_cfg_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__1(lean_object* v_val_539_, lean_object* v_cfg_540_){
_start:
{
lean_object* v_defaultService_541_; lean_object* v_defaultUploadService_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_defaultService_541_ = lean_ctor_get(v_cfg_540_, 0);
v_defaultUploadService_542_ = lean_ctor_get(v_cfg_540_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_cfg_540_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_cfg_540_, 2);
lean_dec(v_unused_550_);
v___x_544_ = v_cfg_540_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_defaultUploadService_542_);
lean_inc(v_defaultService_541_);
lean_dec(v_cfg_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 2, v_val_539_);
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_defaultService_541_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_defaultUploadService_542_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_val_539_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__2(lean_object* v_f_551_, lean_object* v_cfg_552_){
_start:
{
lean_object* v_defaultService_553_; lean_object* v_defaultUploadService_554_; lean_object* v_services_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_defaultService_553_ = lean_ctor_get(v_cfg_552_, 0);
v_defaultUploadService_554_ = lean_ctor_get(v_cfg_552_, 1);
v_services_555_ = lean_ctor_get(v_cfg_552_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v_cfg_552_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v_cfg_552_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_services_555_);
lean_inc(v_defaultUploadService_554_);
lean_inc(v_defaultService_553_);
lean_dec(v_cfg_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_apply_1(v_f_551_, v_services_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 2, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_defaultService_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_defaultUploadService_554_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3(lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__0));
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3___boxed(lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lake_CacheConfig_services___proj___lam__3(v_x_566_);
lean_dec_ref(v_x_566_);
return v_res_567_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__2));
v___x_587_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_588_ = lean_array_push(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__7(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__6));
v___x_597_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__3, &l_Lake_CacheConfig___fields___closed__3_once, _init_l_Lake_CacheConfig___fields___closed__3);
v___x_598_ = lean_array_push(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__13(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__12));
v___x_611_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__7, &l_Lake_CacheConfig___fields___closed__7_once, _init_l_Lake_CacheConfig___fields___closed__7);
v___x_612_ = lean_array_push(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields(void){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__13, &l_Lake_CacheConfig___fields___closed__13_once, _init_l_Lake_CacheConfig___fields___closed__13);
return v___x_613_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigFields(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lake_CacheConfig___fields;
return v___x_614_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = l_Lake_CacheConfig___fields;
v___x_616_ = lean_array_get_size(v___x_615_);
return v___x_616_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_nat_dec_lt(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_box(1);
v___x_622_ = l_Lake_CacheConfig___fields;
v___x_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_620_);
return v___x_623_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_625_ = lean_nat_dec_le(v___x_624_, v___x_624_);
return v___x_625_;
}
}
static size_t _init_l_Lake_CacheConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_626_; size_t v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_627_ = lean_usize_of_nat(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; lean_object* v___f_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_628_ = lean_box(1);
v___x_629_ = lean_usize_once(&l_Lake_CacheConfig_instConfigInfo___closed__4, &l_Lake_CacheConfig_instConfigInfo___closed__4_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__4);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = l_Lake_CacheConfig___fields;
v___f_632_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_633_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_633_, v___f_632_, v___x_631_, v___x_630_, v___x_629_, v___x_628_);
return v___x_634_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__5, &l_Lake_CacheConfig_instConfigInfo___closed__5_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__5);
v___x_637_ = l_Lake_CacheConfig___fields;
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
lean_ctor_set(v___x_638_, 2, v___x_635_);
return v___x_638_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__1, &l_Lake_CacheConfig_instConfigInfo___closed__1_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__1);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_640_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__3, &l_Lake_CacheConfig_instConfigInfo___closed__3_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__3);
if (v___x_641_ == 0)
{
if (v___x_639_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_643_;
}
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0(lean_object* v_cfg_648_){
_start:
{
lean_inc_ref(v_cfg_648_);
return v_cfg_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0___boxed(lean_object* v_cfg_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lake_LakeConfig_cache___proj___lam__0(v_cfg_649_);
lean_dec_ref(v_cfg_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1(lean_object* v_val_651_, lean_object* v_cfg_652_){
_start:
{
lean_inc_ref(v_val_651_);
return v_val_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1___boxed(lean_object* v_val_653_, lean_object* v_cfg_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lake_LakeConfig_cache___proj___lam__1(v_val_653_, v_cfg_654_);
lean_dec_ref(v_cfg_654_);
lean_dec_ref(v_val_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__2(lean_object* v_f_656_, lean_object* v_cfg_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_apply_1(v_f_656_, v_cfg_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3(lean_object* v_x_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__1));
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3___boxed(lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lake_LakeConfig_cache___proj___lam__3(v_x_661_);
lean_dec_ref(v_x_661_);
return v_res_662_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_Lake_LakeConfig___fields___closed__2));
v___x_682_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_683_ = lean_array_push(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields(void){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_once(&l_Lake_LakeConfig___fields___closed__3, &l_Lake_LakeConfig___fields___closed__3_once, _init_l_Lake_LakeConfig___fields___closed__3);
return v___x_684_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigFields(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lake_LakeConfig___fields;
return v___x_685_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = l_Lake_LakeConfig___fields;
v___x_687_ = lean_array_get_size(v___x_686_);
return v___x_687_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_nat_dec_lt(v___x_689_, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_box(1);
v___x_693_ = l_Lake_LakeConfig___fields;
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
lean_ctor_set(v___x_694_, 2, v___x_691_);
return v___x_694_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_696_ = lean_nat_dec_le(v___x_695_, v___x_695_);
return v___x_696_;
}
}
static size_t _init_l_Lake_LakeConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_697_; size_t v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_698_ = lean_usize_of_nat(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_699_; size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_699_ = lean_box(1);
v___x_700_ = lean_usize_once(&l_Lake_LakeConfig_instConfigInfo___closed__4, &l_Lake_LakeConfig_instConfigInfo___closed__4_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__4);
v___x_701_ = ((size_t)0ULL);
v___x_702_ = l_Lake_LakeConfig___fields;
v___f_703_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_704_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_704_, v___f_703_, v___x_702_, v___x_701_, v___x_700_, v___x_699_);
return v___x_705_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__5, &l_Lake_LakeConfig_instConfigInfo___closed__5_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__5);
v___x_708_ = l_Lake_LakeConfig___fields;
v___x_709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_707_);
lean_ctor_set(v___x_709_, 2, v___x_706_);
return v___x_709_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__1, &l_Lake_LakeConfig_instConfigInfo___closed__1_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__1);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__3, &l_Lake_LakeConfig_instConfigInfo___closed__3_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__3);
if (v___x_712_ == 0)
{
if (v___x_710_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_713_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_714_;
}
}
else
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_715_;
}
}
}
}
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LakeConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
