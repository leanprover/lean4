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
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_418_ = lean_nat_dec_le(v___x_417_, v___x_417_);
return v___x_418_;
}
}
static size_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_419_; size_t v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_420_ = lean_usize_of_nat(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_421_; size_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_421_ = lean_box(1);
v___x_422_ = lean_usize_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__15, &l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l_Lake_CacheServiceConfig___fields;
v___f_425_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_426_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_426_, v___f_425_, v___x_424_, v___x_423_, v___x_422_, v___x_421_);
return v___x_427_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__16, &l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16);
v___x_430_ = l_Lake_CacheServiceConfig___fields;
v___x_431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_428_);
return v___x_431_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__11, &l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__14, &l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14);
if (v___x_434_ == 0)
{
if (v___x_432_ == 0)
{
lean_object* v___x_435_; 
v___x_435_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_435_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_436_;
}
}
else
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0(lean_object* v_cfg_446_){
_start:
{
lean_object* v_defaultService_447_; 
v_defaultService_447_ = lean_ctor_get(v_cfg_446_, 0);
lean_inc_ref(v_defaultService_447_);
return v_defaultService_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0___boxed(lean_object* v_cfg_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lake_CacheConfig_defaultService___proj___lam__0(v_cfg_448_);
lean_dec_ref(v_cfg_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__1(lean_object* v_val_450_, lean_object* v_cfg_451_){
_start:
{
lean_object* v_defaultUploadService_452_; lean_object* v_services_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_defaultUploadService_452_ = lean_ctor_get(v_cfg_451_, 1);
v_services_453_ = lean_ctor_get(v_cfg_451_, 2);
v_isSharedCheck_460_ = !lean_is_exclusive(v_cfg_451_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_cfg_451_, 0);
lean_dec(v_unused_461_);
v___x_455_ = v_cfg_451_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_services_453_);
lean_inc(v_defaultUploadService_452_);
lean_dec(v_cfg_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_val_450_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_val_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_defaultUploadService_452_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_services_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__2(lean_object* v_f_462_, lean_object* v_cfg_463_){
_start:
{
lean_object* v_defaultService_464_; lean_object* v_defaultUploadService_465_; lean_object* v_services_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_defaultService_464_ = lean_ctor_get(v_cfg_463_, 0);
v_defaultUploadService_465_ = lean_ctor_get(v_cfg_463_, 1);
v_services_466_ = lean_ctor_get(v_cfg_463_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v_cfg_463_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v_cfg_463_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_services_466_);
lean_inc(v_defaultUploadService_465_);
lean_inc(v_defaultService_464_);
lean_dec(v_cfg_463_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_apply_1(v_f_462_, v_defaultService_464_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_defaultUploadService_465_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_services_466_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3(lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3___boxed(lean_object* v_x_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lake_CacheConfig_defaultService___proj___lam__3(v_x_477_);
lean_dec_ref(v_x_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0(lean_object* v_cfg_490_){
_start:
{
lean_object* v_defaultUploadService_491_; 
v_defaultUploadService_491_ = lean_ctor_get(v_cfg_490_, 1);
lean_inc_ref(v_defaultUploadService_491_);
return v_defaultUploadService_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed(lean_object* v_cfg_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lake_CacheConfig_defaultUploadService___proj___lam__0(v_cfg_492_);
lean_dec_ref(v_cfg_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__1(lean_object* v_val_494_, lean_object* v_cfg_495_){
_start:
{
lean_object* v_defaultService_496_; lean_object* v_services_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_defaultService_496_ = lean_ctor_get(v_cfg_495_, 0);
v_services_497_ = lean_ctor_get(v_cfg_495_, 2);
v_isSharedCheck_504_ = !lean_is_exclusive(v_cfg_495_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_cfg_495_, 1);
lean_dec(v_unused_505_);
v___x_499_ = v_cfg_495_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_services_497_);
lean_inc(v_defaultService_496_);
lean_dec(v_cfg_495_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v_val_494_);
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_defaultService_496_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_val_494_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_services_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__2(lean_object* v_f_506_, lean_object* v_cfg_507_){
_start:
{
lean_object* v_defaultService_508_; lean_object* v_defaultUploadService_509_; lean_object* v_services_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_defaultService_508_ = lean_ctor_get(v_cfg_507_, 0);
v_defaultUploadService_509_ = lean_ctor_get(v_cfg_507_, 1);
v_services_510_ = lean_ctor_get(v_cfg_507_, 2);
v_isSharedCheck_518_ = !lean_is_exclusive(v_cfg_507_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v_cfg_507_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_services_510_);
lean_inc(v_defaultUploadService_509_);
lean_inc(v_defaultService_508_);
lean_dec(v_cfg_507_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_apply_1(v_f_506_, v_defaultUploadService_509_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_defaultService_508_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_services_510_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0(lean_object* v_cfg_529_){
_start:
{
lean_object* v_services_530_; 
v_services_530_ = lean_ctor_get(v_cfg_529_, 2);
lean_inc_ref(v_services_530_);
return v_services_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0___boxed(lean_object* v_cfg_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lake_CacheConfig_services___proj___lam__0(v_cfg_531_);
lean_dec_ref(v_cfg_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__1(lean_object* v_val_533_, lean_object* v_cfg_534_){
_start:
{
lean_object* v_defaultService_535_; lean_object* v_defaultUploadService_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_defaultService_535_ = lean_ctor_get(v_cfg_534_, 0);
v_defaultUploadService_536_ = lean_ctor_get(v_cfg_534_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_cfg_534_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_cfg_534_, 2);
lean_dec(v_unused_544_);
v___x_538_ = v_cfg_534_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_defaultUploadService_536_);
lean_inc(v_defaultService_535_);
lean_dec(v_cfg_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 2, v_val_533_);
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_defaultService_535_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_defaultUploadService_536_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_val_533_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__2(lean_object* v_f_545_, lean_object* v_cfg_546_){
_start:
{
lean_object* v_defaultService_547_; lean_object* v_defaultUploadService_548_; lean_object* v_services_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_defaultService_547_ = lean_ctor_get(v_cfg_546_, 0);
v_defaultUploadService_548_ = lean_ctor_get(v_cfg_546_, 1);
v_services_549_ = lean_ctor_get(v_cfg_546_, 2);
v_isSharedCheck_557_ = !lean_is_exclusive(v_cfg_546_);
if (v_isSharedCheck_557_ == 0)
{
v___x_551_ = v_cfg_546_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_services_549_);
lean_inc(v_defaultUploadService_548_);
lean_inc(v_defaultService_547_);
lean_dec(v_cfg_546_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_apply_1(v_f_545_, v_services_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 2, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_defaultService_547_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_defaultUploadService_548_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v___x_553_);
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
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3(lean_object* v_x_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__0));
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3___boxed(lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lake_CacheConfig_services___proj___lam__3(v_x_560_);
lean_dec_ref(v_x_560_);
return v_res_561_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__2));
v___x_581_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_582_ = lean_array_push(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__7(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__6));
v___x_591_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__3, &l_Lake_CacheConfig___fields___closed__3_once, _init_l_Lake_CacheConfig___fields___closed__3);
v___x_592_ = lean_array_push(v___x_591_, v___x_590_);
return v___x_592_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__13(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__12));
v___x_605_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__7, &l_Lake_CacheConfig___fields___closed__7_once, _init_l_Lake_CacheConfig___fields___closed__7);
v___x_606_ = lean_array_push(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields(void){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__13, &l_Lake_CacheConfig___fields___closed__13_once, _init_l_Lake_CacheConfig___fields___closed__13);
return v___x_607_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigFields(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lake_CacheConfig___fields;
return v___x_608_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = l_Lake_CacheConfig___fields;
v___x_610_ = lean_array_get_size(v___x_609_);
return v___x_610_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_lt(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_box(1);
v___x_616_ = l_Lake_CacheConfig___fields;
v___x_617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_614_);
return v___x_617_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_619_ = lean_nat_dec_le(v___x_618_, v___x_618_);
return v___x_619_;
}
}
static size_t _init_l_Lake_CacheConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_620_; size_t v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_621_ = lean_usize_of_nat(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_622_ = lean_box(1);
v___x_623_ = lean_usize_once(&l_Lake_CacheConfig_instConfigInfo___closed__4, &l_Lake_CacheConfig_instConfigInfo___closed__4_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__4);
v___x_624_ = ((size_t)0ULL);
v___x_625_ = l_Lake_CacheConfig___fields;
v___f_626_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_627_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_627_, v___f_626_, v___x_625_, v___x_624_, v___x_623_, v___x_622_);
return v___x_628_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__5, &l_Lake_CacheConfig_instConfigInfo___closed__5_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__5);
v___x_631_ = l_Lake_CacheConfig___fields;
v___x_632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
lean_ctor_set(v___x_632_, 2, v___x_629_);
return v___x_632_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__1, &l_Lake_CacheConfig_instConfigInfo___closed__1_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__1);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_634_;
}
else
{
uint8_t v___x_635_; 
v___x_635_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__3, &l_Lake_CacheConfig_instConfigInfo___closed__3_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__3);
if (v___x_635_ == 0)
{
if (v___x_633_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_637_;
}
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0(lean_object* v_cfg_642_){
_start:
{
lean_inc_ref(v_cfg_642_);
return v_cfg_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0___boxed(lean_object* v_cfg_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lake_LakeConfig_cache___proj___lam__0(v_cfg_643_);
lean_dec_ref(v_cfg_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1(lean_object* v_val_645_, lean_object* v_cfg_646_){
_start:
{
lean_inc_ref(v_val_645_);
return v_val_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1___boxed(lean_object* v_val_647_, lean_object* v_cfg_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lake_LakeConfig_cache___proj___lam__1(v_val_647_, v_cfg_648_);
lean_dec_ref(v_cfg_648_);
lean_dec_ref(v_val_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__2(lean_object* v_f_650_, lean_object* v_cfg_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_apply_1(v_f_650_, v_cfg_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3(lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__1));
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3___boxed(lean_object* v_x_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lake_LakeConfig_cache___proj___lam__3(v_x_655_);
lean_dec_ref(v_x_655_);
return v_res_656_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = ((lean_object*)(l_Lake_LakeConfig___fields___closed__2));
v___x_676_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_677_ = lean_array_push(v___x_676_, v___x_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields(void){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_obj_once(&l_Lake_LakeConfig___fields___closed__3, &l_Lake_LakeConfig___fields___closed__3_once, _init_l_Lake_LakeConfig___fields___closed__3);
return v___x_678_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigFields(void){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lake_LakeConfig___fields;
return v___x_679_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l_Lake_LakeConfig___fields;
v___x_681_ = lean_array_get_size(v___x_680_);
return v___x_681_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_682_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_nat_dec_lt(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_box(1);
v___x_687_ = l_Lake_LakeConfig___fields;
v___x_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
lean_ctor_set(v___x_688_, 2, v___x_685_);
return v___x_688_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_690_ = lean_nat_dec_le(v___x_689_, v___x_689_);
return v___x_690_;
}
}
static size_t _init_l_Lake_LakeConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_691_; size_t v___x_692_; 
v___x_691_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_692_ = lean_usize_of_nat(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_693_; size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_693_ = lean_box(1);
v___x_694_ = lean_usize_once(&l_Lake_LakeConfig_instConfigInfo___closed__4, &l_Lake_LakeConfig_instConfigInfo___closed__4_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__4);
v___x_695_ = ((size_t)0ULL);
v___x_696_ = l_Lake_LakeConfig___fields;
v___f_697_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_698_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_698_, v___f_697_, v___x_696_, v___x_695_, v___x_694_, v___x_693_);
return v___x_699_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__5, &l_Lake_LakeConfig_instConfigInfo___closed__5_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__5);
v___x_702_ = l_Lake_LakeConfig___fields;
v___x_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_701_);
lean_ctor_set(v___x_703_, 2, v___x_700_);
return v___x_703_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__1, &l_Lake_LakeConfig_instConfigInfo___closed__1_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__1);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_705_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__3, &l_Lake_LakeConfig_instConfigInfo___closed__3_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__3);
if (v___x_706_ == 0)
{
if (v___x_704_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_707_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_708_;
}
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_709_;
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
