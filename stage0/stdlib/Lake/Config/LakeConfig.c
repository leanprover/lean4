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
lean_object* l_Lake_CacheServiceKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lake_CacheServiceKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lake_CacheServiceKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_CacheServiceKind_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lake_CacheServiceKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lake_CacheServiceKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lake_CacheServiceKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lake_CacheServiceKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg(lean_object* v_undef_24_){
_start:
{
lean_inc(v_undef_24_);
return v_undef_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___redArg___boxed(lean_object* v_undef_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_CacheServiceKind_undef_elim___redArg(v_undef_25_);
lean_dec(v_undef_25_);
return v_res_26_;
}
}
lean_object* l_Lake_CacheServiceKind_undef_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_undef_30_){
_start:
{
lean_inc(v_undef_30_);
return v_undef_30_;
}
}
LEAN_EXPORT void l_Lake_CacheServiceKind_undef_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_undef_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_CacheServiceKind_undef_elim(lean_box(0), v_t_28_, lean_box(0), v_undef_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_undef_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_undef_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lake_CacheServiceKind_undef_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_undef_35_);
lean_dec(v_undef_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg(lean_object* v_reservoir_38_){
_start:
{
lean_inc(v_reservoir_38_);
return v_reservoir_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___redArg___boxed(lean_object* v_reservoir_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_CacheServiceKind_reservoir_elim___redArg(v_reservoir_39_);
lean_dec(v_reservoir_39_);
return v_res_40_;
}
}
lean_object* l_Lake_CacheServiceKind_reservoir_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_reservoir_44_){
_start:
{
lean_inc(v_reservoir_44_);
return v_reservoir_44_;
}
}
LEAN_EXPORT void l_Lake_CacheServiceKind_reservoir_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_reservoir_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lake_CacheServiceKind_reservoir_elim(lean_box(0), v_t_42_, lean_box(0), v_reservoir_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_reservoir_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_reservoir_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lake_CacheServiceKind_reservoir_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_reservoir_49_);
lean_dec(v_reservoir_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg(lean_object* v_s3_52_){
_start:
{
lean_inc(v_s3_52_);
return v_s3_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___redArg___boxed(lean_object* v_s3_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_CacheServiceKind_s3_elim___redArg(v_s3_53_);
lean_dec(v_s3_53_);
return v_res_54_;
}
}
lean_object* l_Lake_CacheServiceKind_s3_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_s3_58_){
_start:
{
lean_inc(v_s3_58_);
return v_s3_58_;
}
}
LEAN_EXPORT void l_Lake_CacheServiceKind_s3_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_s3_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lake_CacheServiceKind_s3_elim(lean_box(0), v_t_56_, lean_box(0), v_s3_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_s3_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_s3_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lake_CacheServiceKind_s3_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_s3_63_);
lean_dec(v_s3_63_);
return v_res_65_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_Lake_instInhabitedCacheServiceKind(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f(lean_object* v_s_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__0));
v___x_78_ = lean_string_dec_eq(v_s_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__1));
v___x_80_ = lean_string_dec_eq(v_s_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__2));
return v___x_82_;
}
}
else
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Lake_CacheServiceKind_ofString_x3f___closed__3));
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceKind_ofString_x3f___boxed(lean_object* v_s_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lake_CacheServiceKind_ofString_x3f(v_s_84_);
lean_dec_ref(v_s_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0(lean_object* v_cfg_92_){
_start:
{
lean_object* v_name_93_; 
v_name_93_ = lean_ctor_get(v_cfg_92_, 0);
lean_inc_ref(v_name_93_);
return v_name_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__0___boxed(lean_object* v_cfg_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lake_CacheServiceConfig_name___proj___lam__0(v_cfg_94_);
lean_dec_ref(v_cfg_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__1(lean_object* v_val_96_, lean_object* v_cfg_97_){
_start:
{
uint8_t v_kind_98_; lean_object* v_apiEndpoint_99_; lean_object* v_artifactEndpoint_100_; lean_object* v_revisionEndpoint_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_kind_98_ = lean_ctor_get_uint8(v_cfg_97_, sizeof(void*)*4);
v_apiEndpoint_99_ = lean_ctor_get(v_cfg_97_, 1);
v_artifactEndpoint_100_ = lean_ctor_get(v_cfg_97_, 2);
v_revisionEndpoint_101_ = lean_ctor_get(v_cfg_97_, 3);
v_isSharedCheck_108_ = !lean_is_exclusive(v_cfg_97_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_cfg_97_, 0);
lean_dec(v_unused_109_);
v___x_103_ = v_cfg_97_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_revisionEndpoint_101_);
lean_inc(v_artifactEndpoint_100_);
lean_inc(v_apiEndpoint_99_);
lean_dec(v_cfg_97_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v_val_96_);
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_val_96_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_apiEndpoint_99_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v_artifactEndpoint_100_);
lean_ctor_set(v_reuseFailAlloc_107_, 3, v_revisionEndpoint_101_);
lean_ctor_set_uint8(v_reuseFailAlloc_107_, sizeof(void*)*4, v_kind_98_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__2(lean_object* v_f_110_, lean_object* v_cfg_111_){
_start:
{
lean_object* v_name_112_; uint8_t v_kind_113_; lean_object* v_apiEndpoint_114_; lean_object* v_artifactEndpoint_115_; lean_object* v_revisionEndpoint_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
v_name_112_ = lean_ctor_get(v_cfg_111_, 0);
v_kind_113_ = lean_ctor_get_uint8(v_cfg_111_, sizeof(void*)*4);
v_apiEndpoint_114_ = lean_ctor_get(v_cfg_111_, 1);
v_artifactEndpoint_115_ = lean_ctor_get(v_cfg_111_, 2);
v_revisionEndpoint_116_ = lean_ctor_get(v_cfg_111_, 3);
v_isSharedCheck_124_ = !lean_is_exclusive(v_cfg_111_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v_cfg_111_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_revisionEndpoint_116_);
lean_inc(v_artifactEndpoint_115_);
lean_inc(v_apiEndpoint_114_);
lean_inc(v_name_112_);
lean_dec(v_cfg_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_120_ = lean_apply_1(v_f_110_, v_name_112_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_apiEndpoint_114_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_artifactEndpoint_115_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v_revisionEndpoint_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_123_, sizeof(void*)*4, v_kind_113_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3(lean_object* v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_name___proj___lam__3___boxed(lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lake_CacheServiceConfig_name___proj___lam__3(v_x_127_);
lean_dec_ref(v_x_127_);
return v_res_128_;
}
}
uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__0(lean_object* v_cfg_140_){
_start:
{
uint8_t v_kind_141_; 
v_kind_141_ = lean_ctor_get_uint8(v_cfg_140_, sizeof(void*)*4);
return v_kind_141_;
}
}
LEAN_EXPORT void l_Lake_CacheServiceConfig_kind___proj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_140_ = stack[0].m_obj;
uint8_t v_res_142_;
v_res_142_ = l_Lake_CacheServiceConfig_kind___proj___lam__0(v_cfg_140_);
stack->m_num = v_res_142_;
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
lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1(uint8_t v_val_146_, lean_object* v_cfg_147_){
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
LEAN_EXPORT void l_Lake_CacheServiceConfig_kind___proj___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_146_ = stack[0].m_num;
lean_object* v_cfg_147_ = stack[1].m_obj;
lean_object* v_res_159_;
v_res_159_ = l_Lake_CacheServiceConfig_kind___proj___lam__1(v_val_146_, v_cfg_147_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__1___boxed(lean_object* v_val_160_, lean_object* v_cfg_161_){
_start:
{
uint8_t v_val_51__boxed_162_; lean_object* v_res_163_; 
v_val_51__boxed_162_ = lean_unbox(v_val_160_);
v_res_163_ = l_Lake_CacheServiceConfig_kind___proj___lam__1(v_val_51__boxed_162_, v_cfg_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__2(lean_object* v_f_164_, lean_object* v_cfg_165_){
_start:
{
lean_object* v_name_166_; uint8_t v_kind_167_; lean_object* v_apiEndpoint_168_; lean_object* v_artifactEndpoint_169_; lean_object* v_revisionEndpoint_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
v_name_166_ = lean_ctor_get(v_cfg_165_, 0);
v_kind_167_ = lean_ctor_get_uint8(v_cfg_165_, sizeof(void*)*4);
v_apiEndpoint_168_ = lean_ctor_get(v_cfg_165_, 1);
v_artifactEndpoint_169_ = lean_ctor_get(v_cfg_165_, 2);
v_revisionEndpoint_170_ = lean_ctor_get(v_cfg_165_, 3);
v_isSharedCheck_180_ = !lean_is_exclusive(v_cfg_165_);
if (v_isSharedCheck_180_ == 0)
{
v___x_172_ = v_cfg_165_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_revisionEndpoint_170_);
lean_inc(v_artifactEndpoint_169_);
lean_inc(v_apiEndpoint_168_);
lean_inc(v_name_166_);
lean_dec(v_cfg_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = lean_box(v_kind_167_);
v___x_175_ = lean_apply_1(v_f_164_, v___x_174_);
if (v_isShared_173_ == 0)
{
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_name_166_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_apiEndpoint_168_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_artifactEndpoint_169_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_revisionEndpoint_170_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
uint8_t v___x_178_; 
v___x_178_ = lean_unbox(v___x_175_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*4, v___x_178_);
return v___x_177_;
}
}
}
}
uint8_t l_Lake_CacheServiceConfig_kind___proj___lam__3(lean_object* v_x_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
LEAN_EXPORT void l_Lake_CacheServiceConfig_kind___proj___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_181_ = stack[0].m_obj;
uint8_t v_res_183_;
v_res_183_ = l_Lake_CacheServiceConfig_kind___proj___lam__3(v_x_181_);
stack->m_num = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_kind___proj___lam__3___boxed(lean_object* v_x_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lake_CacheServiceConfig_kind___proj___lam__3(v_x_184_);
lean_dec_ref(v_x_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(lean_object* v_cfg_199_){
_start:
{
lean_object* v_apiEndpoint_200_; 
v_apiEndpoint_200_ = lean_ctor_get(v_cfg_199_, 1);
lean_inc_ref(v_apiEndpoint_200_);
return v_apiEndpoint_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0___boxed(lean_object* v_cfg_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__0(v_cfg_201_);
lean_dec_ref(v_cfg_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__1(lean_object* v_val_203_, lean_object* v_cfg_204_){
_start:
{
lean_object* v_name_205_; uint8_t v_kind_206_; lean_object* v_artifactEndpoint_207_; lean_object* v_revisionEndpoint_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_name_205_ = lean_ctor_get(v_cfg_204_, 0);
v_kind_206_ = lean_ctor_get_uint8(v_cfg_204_, sizeof(void*)*4);
v_artifactEndpoint_207_ = lean_ctor_get(v_cfg_204_, 2);
v_revisionEndpoint_208_ = lean_ctor_get(v_cfg_204_, 3);
v_isSharedCheck_215_ = !lean_is_exclusive(v_cfg_204_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_cfg_204_, 1);
lean_dec(v_unused_216_);
v___x_210_ = v_cfg_204_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_revisionEndpoint_208_);
lean_inc(v_artifactEndpoint_207_);
lean_inc(v_name_205_);
lean_dec(v_cfg_204_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_val_203_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_name_205_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_val_203_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_artifactEndpoint_207_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_revisionEndpoint_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_214_, sizeof(void*)*4, v_kind_206_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_apiEndpoint___proj___lam__2(lean_object* v_f_217_, lean_object* v_cfg_218_){
_start:
{
lean_object* v_name_219_; uint8_t v_kind_220_; lean_object* v_apiEndpoint_221_; lean_object* v_artifactEndpoint_222_; lean_object* v_revisionEndpoint_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_name_219_ = lean_ctor_get(v_cfg_218_, 0);
v_kind_220_ = lean_ctor_get_uint8(v_cfg_218_, sizeof(void*)*4);
v_apiEndpoint_221_ = lean_ctor_get(v_cfg_218_, 1);
v_artifactEndpoint_222_ = lean_ctor_get(v_cfg_218_, 2);
v_revisionEndpoint_223_ = lean_ctor_get(v_cfg_218_, 3);
v_isSharedCheck_231_ = !lean_is_exclusive(v_cfg_218_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v_cfg_218_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_revisionEndpoint_223_);
lean_inc(v_artifactEndpoint_222_);
lean_inc(v_apiEndpoint_221_);
lean_inc(v_name_219_);
lean_dec(v_cfg_218_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_apply_1(v_f_217_, v_apiEndpoint_221_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_name_219_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_artifactEndpoint_222_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_revisionEndpoint_223_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*4, v_kind_220_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(lean_object* v_cfg_242_){
_start:
{
lean_object* v_artifactEndpoint_243_; 
v_artifactEndpoint_243_ = lean_ctor_get(v_cfg_242_, 2);
lean_inc_ref(v_artifactEndpoint_243_);
return v_artifactEndpoint_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0___boxed(lean_object* v_cfg_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__0(v_cfg_244_);
lean_dec_ref(v_cfg_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__1(lean_object* v_val_246_, lean_object* v_cfg_247_){
_start:
{
lean_object* v_name_248_; uint8_t v_kind_249_; lean_object* v_apiEndpoint_250_; lean_object* v_revisionEndpoint_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_name_248_ = lean_ctor_get(v_cfg_247_, 0);
v_kind_249_ = lean_ctor_get_uint8(v_cfg_247_, sizeof(void*)*4);
v_apiEndpoint_250_ = lean_ctor_get(v_cfg_247_, 1);
v_revisionEndpoint_251_ = lean_ctor_get(v_cfg_247_, 3);
v_isSharedCheck_258_ = !lean_is_exclusive(v_cfg_247_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_cfg_247_, 2);
lean_dec(v_unused_259_);
v___x_253_ = v_cfg_247_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_revisionEndpoint_251_);
lean_inc(v_apiEndpoint_250_);
lean_inc(v_name_248_);
lean_dec(v_cfg_247_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 2, v_val_246_);
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_name_248_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_apiEndpoint_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_val_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_revisionEndpoint_251_);
lean_ctor_set_uint8(v_reuseFailAlloc_257_, sizeof(void*)*4, v_kind_249_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_artifactEndpoint___proj___lam__2(lean_object* v_f_260_, lean_object* v_cfg_261_){
_start:
{
lean_object* v_name_262_; uint8_t v_kind_263_; lean_object* v_apiEndpoint_264_; lean_object* v_artifactEndpoint_265_; lean_object* v_revisionEndpoint_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_name_262_ = lean_ctor_get(v_cfg_261_, 0);
v_kind_263_ = lean_ctor_get_uint8(v_cfg_261_, sizeof(void*)*4);
v_apiEndpoint_264_ = lean_ctor_get(v_cfg_261_, 1);
v_artifactEndpoint_265_ = lean_ctor_get(v_cfg_261_, 2);
v_revisionEndpoint_266_ = lean_ctor_get(v_cfg_261_, 3);
v_isSharedCheck_274_ = !lean_is_exclusive(v_cfg_261_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v_cfg_261_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_revisionEndpoint_266_);
lean_inc(v_artifactEndpoint_265_);
lean_inc(v_apiEndpoint_264_);
lean_inc(v_name_262_);
lean_dec(v_cfg_261_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_apply_1(v_f_260_, v_artifactEndpoint_265_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 2, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_name_262_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_apiEndpoint_264_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_revisionEndpoint_266_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*4, v_kind_263_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(lean_object* v_cfg_285_){
_start:
{
lean_object* v_revisionEndpoint_286_; 
v_revisionEndpoint_286_ = lean_ctor_get(v_cfg_285_, 3);
lean_inc_ref(v_revisionEndpoint_286_);
return v_revisionEndpoint_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0___boxed(lean_object* v_cfg_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__0(v_cfg_287_);
lean_dec_ref(v_cfg_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__1(lean_object* v_val_289_, lean_object* v_cfg_290_){
_start:
{
lean_object* v_name_291_; uint8_t v_kind_292_; lean_object* v_apiEndpoint_293_; lean_object* v_artifactEndpoint_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_name_291_ = lean_ctor_get(v_cfg_290_, 0);
v_kind_292_ = lean_ctor_get_uint8(v_cfg_290_, sizeof(void*)*4);
v_apiEndpoint_293_ = lean_ctor_get(v_cfg_290_, 1);
v_artifactEndpoint_294_ = lean_ctor_get(v_cfg_290_, 2);
v_isSharedCheck_301_ = !lean_is_exclusive(v_cfg_290_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_cfg_290_, 3);
lean_dec(v_unused_302_);
v___x_296_ = v_cfg_290_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_artifactEndpoint_294_);
lean_inc(v_apiEndpoint_293_);
lean_inc(v_name_291_);
lean_dec(v_cfg_290_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 3, v_val_289_);
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_name_291_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_apiEndpoint_293_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_artifactEndpoint_294_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_val_289_);
lean_ctor_set_uint8(v_reuseFailAlloc_300_, sizeof(void*)*4, v_kind_292_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_revisionEndpoint___proj___lam__2(lean_object* v_f_303_, lean_object* v_cfg_304_){
_start:
{
lean_object* v_name_305_; uint8_t v_kind_306_; lean_object* v_apiEndpoint_307_; lean_object* v_artifactEndpoint_308_; lean_object* v_revisionEndpoint_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
v_name_305_ = lean_ctor_get(v_cfg_304_, 0);
v_kind_306_ = lean_ctor_get_uint8(v_cfg_304_, sizeof(void*)*4);
v_apiEndpoint_307_ = lean_ctor_get(v_cfg_304_, 1);
v_artifactEndpoint_308_ = lean_ctor_get(v_cfg_304_, 2);
v_revisionEndpoint_309_ = lean_ctor_get(v_cfg_304_, 3);
v_isSharedCheck_317_ = !lean_is_exclusive(v_cfg_304_);
if (v_isSharedCheck_317_ == 0)
{
v___x_311_ = v_cfg_304_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_revisionEndpoint_309_);
lean_inc(v_artifactEndpoint_308_);
lean_inc(v_apiEndpoint_307_);
lean_inc(v_name_305_);
lean_dec(v_cfg_304_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_apply_1(v_f_303_, v_revisionEndpoint_309_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 3, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_name_305_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_apiEndpoint_307_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_artifactEndpoint_308_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v___x_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*4, v_kind_306_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__4(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__3));
v___x_338_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_339_ = lean_array_push(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__8(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__7));
v___x_348_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__4, &l_Lake_CacheServiceConfig___fields___closed__4_once, _init_l_Lake_CacheServiceConfig___fields___closed__4);
v___x_349_ = lean_array_push(v___x_348_, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__11));
v___x_358_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__8, &l_Lake_CacheServiceConfig___fields___closed__8_once, _init_l_Lake_CacheServiceConfig___fields___closed__8);
v___x_359_ = lean_array_push(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__16(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__15));
v___x_368_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__12, &l_Lake_CacheServiceConfig___fields___closed__12_once, _init_l_Lake_CacheServiceConfig___fields___closed__12);
v___x_369_ = lean_array_push(v___x_368_, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__20(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__19));
v___x_378_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__16, &l_Lake_CacheServiceConfig___fields___closed__16_once, _init_l_Lake_CacheServiceConfig___fields___closed__16);
v___x_379_ = lean_array_push(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__23));
v___x_388_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__20, &l_Lake_CacheServiceConfig___fields___closed__20_once, _init_l_Lake_CacheServiceConfig___fields___closed__20);
v___x_389_ = lean_array_push(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig___fields(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_Lake_CacheServiceConfig___fields___closed__24, &l_Lake_CacheServiceConfig___fields___closed__24_once, _init_l_Lake_CacheServiceConfig___fields___closed__24);
return v___x_390_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigFields(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lake_CacheServiceConfig___fields;
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceConfig_instConfigInfo___lam__0(lean_object* v_x1_392_, lean_object* v_x2_393_){
_start:
{
lean_object* v_name_394_; lean_object* v___x_395_; 
v_name_394_ = lean_ctor_get(v_x2_393_, 0);
lean_inc(v_name_394_);
v___x_395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_394_, v_x2_393_, v_x1_392_);
return v___x_395_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = l_Lake_CacheServiceConfig___fields;
v___x_397_ = lean_array_get_size(v___x_396_);
return v___x_397_;
}
}
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_417_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_nat_dec_lt(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_box(1);
v___x_422_ = l_Lake_CacheServiceConfig___fields;
v___x_423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
return v___x_423_;
}
}
static uint8_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_426_ = lean_nat_dec_le(v___x_425_, v___x_425_);
return v___x_426_;
}
}
static size_t _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_427_; size_t v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__0, &l_Lake_CacheServiceConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__0);
v___x_428_ = lean_usize_of_nat(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_429_ = lean_box(1);
v___x_430_ = lean_usize_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__15, &l_Lake_CacheServiceConfig_instConfigInfo___closed__15_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__15);
v___x_431_ = ((size_t)0ULL);
v___x_432_ = l_Lake_CacheServiceConfig___fields;
v___f_433_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_434_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_434_, v___f_433_, v___x_432_, v___x_431_, v___x_430_, v___x_429_);
return v___x_435_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__16, &l_Lake_CacheServiceConfig_instConfigInfo___closed__16_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__16);
v___x_438_ = l_Lake_CacheServiceConfig___fields;
v___x_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_437_);
lean_ctor_set(v___x_439_, 2, v___x_436_);
return v___x_439_;
}
}
static lean_object* _init_l_Lake_CacheServiceConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__11, &l_Lake_CacheServiceConfig_instConfigInfo___closed__11_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__11);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_441_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = lean_uint8_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__14, &l_Lake_CacheServiceConfig_instConfigInfo___closed__14_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__14);
if (v___x_442_ == 0)
{
if (v___x_440_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__12, &l_Lake_CacheServiceConfig_instConfigInfo___closed__12_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__12);
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_444_;
}
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Lake_CacheServiceConfig_instConfigInfo___closed__17, &l_Lake_CacheServiceConfig_instConfigInfo___closed__17_once, _init_l_Lake_CacheServiceConfig_instConfigInfo___closed__17);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0(lean_object* v_cfg_454_){
_start:
{
lean_object* v_defaultService_455_; 
v_defaultService_455_ = lean_ctor_get(v_cfg_454_, 0);
lean_inc_ref(v_defaultService_455_);
return v_defaultService_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__0___boxed(lean_object* v_cfg_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lake_CacheConfig_defaultService___proj___lam__0(v_cfg_456_);
lean_dec_ref(v_cfg_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__1(lean_object* v_val_458_, lean_object* v_cfg_459_){
_start:
{
lean_object* v_defaultUploadService_460_; lean_object* v_services_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_defaultUploadService_460_ = lean_ctor_get(v_cfg_459_, 1);
v_services_461_ = lean_ctor_get(v_cfg_459_, 2);
v_isSharedCheck_468_ = !lean_is_exclusive(v_cfg_459_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v_cfg_459_, 0);
lean_dec(v_unused_469_);
v___x_463_ = v_cfg_459_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_services_461_);
lean_inc(v_defaultUploadService_460_);
lean_dec(v_cfg_459_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v_val_458_);
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_val_458_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_defaultUploadService_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_services_461_);
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
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__2(lean_object* v_f_470_, lean_object* v_cfg_471_){
_start:
{
lean_object* v_defaultService_472_; lean_object* v_defaultUploadService_473_; lean_object* v_services_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
v_defaultService_472_ = lean_ctor_get(v_cfg_471_, 0);
v_defaultUploadService_473_ = lean_ctor_get(v_cfg_471_, 1);
v_services_474_ = lean_ctor_get(v_cfg_471_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v_cfg_471_);
if (v_isSharedCheck_482_ == 0)
{
v___x_476_ = v_cfg_471_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_services_474_);
lean_inc(v_defaultUploadService_473_);
lean_inc(v_defaultService_472_);
lean_dec(v_cfg_471_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_apply_1(v_f_470_, v_defaultService_472_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_defaultUploadService_473_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_services_474_);
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
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3(lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l_Lake_instInhabitedCacheServiceConfig_default___closed__0));
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultService___proj___lam__3___boxed(lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lake_CacheConfig_defaultService___proj___lam__3(v_x_485_);
lean_dec_ref(v_x_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0(lean_object* v_cfg_498_){
_start:
{
lean_object* v_defaultUploadService_499_; 
v_defaultUploadService_499_ = lean_ctor_get(v_cfg_498_, 1);
lean_inc_ref(v_defaultUploadService_499_);
return v_defaultUploadService_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__0___boxed(lean_object* v_cfg_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lake_CacheConfig_defaultUploadService___proj___lam__0(v_cfg_500_);
lean_dec_ref(v_cfg_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__1(lean_object* v_val_502_, lean_object* v_cfg_503_){
_start:
{
lean_object* v_defaultService_504_; lean_object* v_services_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_defaultService_504_ = lean_ctor_get(v_cfg_503_, 0);
v_services_505_ = lean_ctor_get(v_cfg_503_, 2);
v_isSharedCheck_512_ = !lean_is_exclusive(v_cfg_503_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v_cfg_503_, 1);
lean_dec(v_unused_513_);
v___x_507_ = v_cfg_503_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_services_505_);
lean_inc(v_defaultService_504_);
lean_dec(v_cfg_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v_val_502_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_defaultService_504_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_val_502_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_services_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_defaultUploadService___proj___lam__2(lean_object* v_f_514_, lean_object* v_cfg_515_){
_start:
{
lean_object* v_defaultService_516_; lean_object* v_defaultUploadService_517_; lean_object* v_services_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_526_; 
v_defaultService_516_ = lean_ctor_get(v_cfg_515_, 0);
v_defaultUploadService_517_ = lean_ctor_get(v_cfg_515_, 1);
v_services_518_ = lean_ctor_get(v_cfg_515_, 2);
v_isSharedCheck_526_ = !lean_is_exclusive(v_cfg_515_);
if (v_isSharedCheck_526_ == 0)
{
v___x_520_ = v_cfg_515_;
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_services_518_);
lean_inc(v_defaultUploadService_517_);
lean_inc(v_defaultService_516_);
lean_dec(v_cfg_515_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_apply_1(v_f_514_, v_defaultUploadService_517_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_defaultService_516_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_services_518_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0(lean_object* v_cfg_537_){
_start:
{
lean_object* v_services_538_; 
v_services_538_ = lean_ctor_get(v_cfg_537_, 2);
lean_inc_ref(v_services_538_);
return v_services_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__0___boxed(lean_object* v_cfg_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lake_CacheConfig_services___proj___lam__0(v_cfg_539_);
lean_dec_ref(v_cfg_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__1(lean_object* v_val_541_, lean_object* v_cfg_542_){
_start:
{
lean_object* v_defaultService_543_; lean_object* v_defaultUploadService_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_defaultService_543_ = lean_ctor_get(v_cfg_542_, 0);
v_defaultUploadService_544_ = lean_ctor_get(v_cfg_542_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_cfg_542_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_cfg_542_, 2);
lean_dec(v_unused_552_);
v___x_546_ = v_cfg_542_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_defaultUploadService_544_);
lean_inc(v_defaultService_543_);
lean_dec(v_cfg_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 2, v_val_541_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_defaultService_543_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_defaultUploadService_544_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_val_541_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__2(lean_object* v_f_553_, lean_object* v_cfg_554_){
_start:
{
lean_object* v_defaultService_555_; lean_object* v_defaultUploadService_556_; lean_object* v_services_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_defaultService_555_ = lean_ctor_get(v_cfg_554_, 0);
v_defaultUploadService_556_ = lean_ctor_get(v_cfg_554_, 1);
v_services_557_ = lean_ctor_get(v_cfg_554_, 2);
v_isSharedCheck_565_ = !lean_is_exclusive(v_cfg_554_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v_cfg_554_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_services_557_);
lean_inc(v_defaultUploadService_556_);
lean_inc(v_defaultService_555_);
lean_dec(v_cfg_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_apply_1(v_f_553_, v_services_557_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 2, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_defaultService_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_defaultUploadService_556_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3(lean_object* v_x_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__0));
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheConfig_services___proj___lam__3___boxed(lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lake_CacheConfig_services___proj___lam__3(v_x_568_);
lean_dec_ref(v_x_568_);
return v_res_569_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__2));
v___x_589_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_590_ = lean_array_push(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__7(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__6));
v___x_599_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__3, &l_Lake_CacheConfig___fields___closed__3_once, _init_l_Lake_CacheConfig___fields___closed__3);
v___x_600_ = lean_array_push(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields___closed__13(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((lean_object*)(l_Lake_CacheConfig___fields___closed__12));
v___x_613_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__7, &l_Lake_CacheConfig___fields___closed__7_once, _init_l_Lake_CacheConfig___fields___closed__7);
v___x_614_ = lean_array_push(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_Lake_CacheConfig___fields(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lake_CacheConfig___fields___closed__13, &l_Lake_CacheConfig___fields___closed__13_once, _init_l_Lake_CacheConfig___fields___closed__13);
return v___x_615_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigFields(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lake_CacheConfig___fields;
return v___x_616_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = l_Lake_CacheConfig___fields;
v___x_618_ = lean_array_get_size(v___x_617_);
return v___x_618_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_619_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_lt(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_box(1);
v___x_624_ = l_Lake_CacheConfig___fields;
v___x_625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
lean_ctor_set(v___x_625_, 2, v___x_622_);
return v___x_625_;
}
}
static uint8_t _init_l_Lake_CacheConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_627_ = lean_nat_dec_le(v___x_626_, v___x_626_);
return v___x_627_;
}
}
static size_t _init_l_Lake_CacheConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_628_; size_t v___x_629_; 
v___x_628_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__0, &l_Lake_CacheConfig_instConfigInfo___closed__0_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__0);
v___x_629_ = lean_usize_of_nat(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_630_ = lean_box(1);
v___x_631_ = lean_usize_once(&l_Lake_CacheConfig_instConfigInfo___closed__4, &l_Lake_CacheConfig_instConfigInfo___closed__4_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__4);
v___x_632_ = ((size_t)0ULL);
v___x_633_ = l_Lake_CacheConfig___fields;
v___f_634_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_635_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_635_, v___f_634_, v___x_633_, v___x_632_, v___x_631_, v___x_630_);
return v___x_636_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__5, &l_Lake_CacheConfig_instConfigInfo___closed__5_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__5);
v___x_639_ = l_Lake_CacheConfig___fields;
v___x_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___x_638_);
lean_ctor_set(v___x_640_, 2, v___x_637_);
return v___x_640_;
}
}
static lean_object* _init_l_Lake_CacheConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__1, &l_Lake_CacheConfig_instConfigInfo___closed__1_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__1);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_642_;
}
else
{
uint8_t v___x_643_; 
v___x_643_ = lean_uint8_once(&l_Lake_CacheConfig_instConfigInfo___closed__3, &l_Lake_CacheConfig_instConfigInfo___closed__3_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__3);
if (v___x_643_ == 0)
{
if (v___x_641_ == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__2, &l_Lake_CacheConfig_instConfigInfo___closed__2_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__2);
return v___x_644_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_645_;
}
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l_Lake_CacheConfig_instConfigInfo___closed__6, &l_Lake_CacheConfig_instConfigInfo___closed__6_once, _init_l_Lake_CacheConfig_instConfigInfo___closed__6);
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0(lean_object* v_cfg_650_){
_start:
{
lean_inc_ref(v_cfg_650_);
return v_cfg_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__0___boxed(lean_object* v_cfg_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lake_LakeConfig_cache___proj___lam__0(v_cfg_651_);
lean_dec_ref(v_cfg_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1(lean_object* v_val_653_, lean_object* v_cfg_654_){
_start:
{
lean_inc_ref(v_val_653_);
return v_val_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__1___boxed(lean_object* v_val_655_, lean_object* v_cfg_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lake_LakeConfig_cache___proj___lam__1(v_val_655_, v_cfg_656_);
lean_dec_ref(v_cfg_656_);
lean_dec_ref(v_val_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__2(lean_object* v_f_658_, lean_object* v_cfg_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_apply_1(v_f_658_, v_cfg_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3(lean_object* v_x_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = ((lean_object*)(l_Lake_instInhabitedCacheConfig_default___closed__1));
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeConfig_cache___proj___lam__3___boxed(lean_object* v_x_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lake_LakeConfig_cache___proj___lam__3(v_x_663_);
lean_dec_ref(v_x_663_);
return v_res_664_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = ((lean_object*)(l_Lake_LakeConfig___fields___closed__2));
v___x_684_ = ((lean_object*)(l_Lake_CacheServiceConfig___fields___closed__0));
v___x_685_ = lean_array_push(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static lean_object* _init_l_Lake_LakeConfig___fields(void){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Lake_LakeConfig___fields___closed__3, &l_Lake_LakeConfig___fields___closed__3_once, _init_l_Lake_LakeConfig___fields___closed__3);
return v___x_686_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigFields(void){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lake_LakeConfig___fields;
return v___x_687_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l_Lake_LakeConfig___fields;
v___x_689_ = lean_array_get_size(v___x_688_);
return v___x_689_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_nat_dec_lt(v___x_691_, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__2(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_box(1);
v___x_695_ = l_Lake_LakeConfig___fields;
v___x_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
lean_ctor_set(v___x_696_, 2, v___x_693_);
return v___x_696_;
}
}
static uint8_t _init_l_Lake_LakeConfig_instConfigInfo___closed__3(void){
_start:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_698_ = lean_nat_dec_le(v___x_697_, v___x_697_);
return v___x_698_;
}
}
static size_t _init_l_Lake_LakeConfig_instConfigInfo___closed__4(void){
_start:
{
lean_object* v___x_699_; size_t v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__0, &l_Lake_LakeConfig_instConfigInfo___closed__0_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__0);
v___x_700_ = lean_usize_of_nat(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__5(void){
_start:
{
lean_object* v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; lean_object* v___f_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_701_ = lean_box(1);
v___x_702_ = lean_usize_once(&l_Lake_LakeConfig_instConfigInfo___closed__4, &l_Lake_LakeConfig_instConfigInfo___closed__4_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__4);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = l_Lake_LakeConfig___fields;
v___f_705_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__13));
v___x_706_ = ((lean_object*)(l_Lake_CacheServiceConfig_instConfigInfo___closed__10));
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_706_, v___f_705_, v___x_704_, v___x_703_, v___x_702_, v___x_701_);
return v___x_707_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo___closed__6(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__5, &l_Lake_LakeConfig_instConfigInfo___closed__5_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__5);
v___x_710_ = l_Lake_LakeConfig___fields;
v___x_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_708_);
return v___x_711_;
}
}
static lean_object* _init_l_Lake_LakeConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__1, &l_Lake_LakeConfig_instConfigInfo___closed__1_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__1);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_713_;
}
else
{
uint8_t v___x_714_; 
v___x_714_ = lean_uint8_once(&l_Lake_LakeConfig_instConfigInfo___closed__3, &l_Lake_LakeConfig_instConfigInfo___closed__3_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__3);
if (v___x_714_ == 0)
{
if (v___x_712_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__2, &l_Lake_LakeConfig_instConfigInfo___closed__2_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__2);
return v___x_715_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_716_;
}
}
else
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_Lake_LakeConfig_instConfigInfo___closed__6, &l_Lake_LakeConfig_instConfigInfo___closed__6_once, _init_l_Lake_LakeConfig_instConfigInfo___closed__6);
return v___x_717_;
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
