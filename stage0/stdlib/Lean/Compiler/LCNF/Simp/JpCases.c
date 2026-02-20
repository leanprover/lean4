// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.JpCases
// Imports: public import Lean.Compiler.LCNF.DependsOn public import Lean.Compiler.LCNF.Internalize public import Lean.Compiler.LCNF.Simp.DiscrM
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0;
static lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1(uint8_t);
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.LCNF.Simp.JpCases"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Compiler.LCNF.Simp.JpCases.0.Lean.Compiler.LCNF.Simp.extractJpCases.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3_value;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instSingletonFVarIdFVarIdSet;
uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2_value;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2;
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4_value;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5;
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "jpCases"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 92, 220, 8, 204, 108, 198, 7)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "candidates"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 104, 221, 94, 203, 189, 176, 167)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "JpCases"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 200, 62, 252, 228, 198, 151, 109)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(5, 181, 89, 208, 84, 141, 174, 108)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(80, 114, 224, 6, 181, 131, 133, 238)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 91, 150, 74, 170, 27, 158, 82)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 85, 119, 190, 56, 191, 107, 84)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 95, 208, 21, 155, 197, 36, 224)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 99, 113, 108, 82, 177, 202, 32)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(158, 149, 154, 42, 73, 148, 172, 49)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 98, 9, 182, 57, 248, 25, 88)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 117, 18, 175, 69, 86, 64, 169)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 8, 88, 168, 116, 51, 112, 53)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 128, 156, 153, 203, 13, 202, 211)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)(((size_t)(862626027) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(79, 69, 117, 196, 237, 244, 183, 219)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 169, 91, 210, 237, 254, 196, 180)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 70, 154, 134, 24, 16, 151, 30)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 209, 167, 183, 214, 28, 157, 252)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_instBEqFVarId_beq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_8;
goto _start;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0___boxed), 2, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findIdx_x3f_loop___redArg(x_12, x_11, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = lean_box(0);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = lean_box(0);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_5);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getConfig___redArg(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(x_1, x_12, x_5, x_7);
lean_dec(x_12);
lean_dec_ref(x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(x_1, x_15, x_5, x_7);
lean_dec(x_15);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(x_1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default;
return x_1;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_6);
x_7 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
x_1 = x_9;
x_2 = x_5;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
x_9 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(x_8, x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_2 = x_10;
goto block_7;
block_7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_1 = x_9;
goto _start;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_11, 4);
lean_inc_ref(x_13);
lean_dec_ref(x_11);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_14 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_dec_ref(x_14);
x_1 = x_12;
goto _start;
}
else
{
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_14;
}
}
case 2:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_30; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_17);
x_30 = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(x_17, x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_st_ref_take(x_2);
x_34 = lean_ctor_get(x_17, 0);
x_35 = l_Lean_NameSet_empty;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_35);
lean_ctor_set(x_1, 0, x_32);
lean_inc(x_34);
x_36 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_34, x_1, x_33);
x_37 = lean_st_ref_set(x_2, x_36);
x_19 = x_2;
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = lean_box(0);
goto block_29;
}
else
{
lean_dec(x_31);
lean_free_object(x_1);
x_19 = x_2;
x_20 = x_3;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = lean_box(0);
goto block_29;
}
}
else
{
uint8_t x_38; 
lean_free_object(x_1);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
block_29:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_26);
lean_dec_ref(x_17);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_20);
x_27 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(x_26, x_19, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_dec_ref(x_27);
x_1 = x_18;
x_2 = x_19;
x_3 = x_20;
x_4 = x_21;
x_5 = x_22;
x_6 = x_23;
x_7 = x_24;
goto _start;
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
return x_27;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_54; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
lean_inc_ref(x_41);
x_54 = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(x_41, x_4);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_st_ref_take(x_2);
x_58 = lean_ctor_get(x_41, 0);
x_59 = l_Lean_NameSet_empty;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_58);
x_61 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_58, x_60, x_57);
x_62 = lean_st_ref_set(x_2, x_61);
x_43 = x_2;
x_44 = x_3;
x_45 = x_4;
x_46 = x_5;
x_47 = x_6;
x_48 = x_7;
x_49 = lean_box(0);
goto block_53;
}
else
{
lean_dec(x_55);
x_43 = x_2;
x_44 = x_3;
x_45 = x_4;
x_46 = x_5;
x_47 = x_6;
x_48 = x_7;
x_49 = lean_box(0);
goto block_53;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
block_53:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_41, 4);
lean_inc_ref(x_50);
lean_dec_ref(x_41);
lean_inc(x_48);
lean_inc_ref(x_47);
lean_inc(x_46);
lean_inc_ref(x_45);
lean_inc_ref(x_44);
x_51 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(x_50, x_43, x_44, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_51);
x_1 = x_42;
x_2 = x_43;
x_3 = x_44;
x_4 = x_45;
x_5 = x_46;
x_6 = x_47;
x_7 = x_48;
goto _start;
}
else
{
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_42);
return x_51;
}
}
}
}
case 3:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_1);
x_68 = lean_st_ref_get(x_2);
x_69 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(x_68, x_66);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 1)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_box(0);
x_76 = lean_array_get(x_75, x_67, x_73);
lean_dec_ref(x_67);
if (lean_obj_tag(x_76) == 1)
{
lean_object* x_77; lean_object* x_78; 
lean_free_object(x_69);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(x_77, x_3, x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_st_ref_take(x_2);
x_83 = l_Lean_NameSet_insert(x_74, x_81);
lean_ctor_set(x_71, 1, x_83);
x_84 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_66, x_71, x_82);
x_85 = lean_st_ref_set(x_2, x_84);
x_86 = lean_box(0);
lean_ctor_set(x_78, 0, x_86);
return x_78;
}
else
{
lean_object* x_87; 
lean_dec(x_80);
lean_free_object(x_71);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
x_87 = lean_box(0);
lean_ctor_set(x_78, 0, x_87);
return x_78;
}
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
lean_dec(x_78);
if (lean_obj_tag(x_88) == 1)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_st_ref_take(x_2);
x_91 = l_Lean_NameSet_insert(x_74, x_89);
lean_ctor_set(x_71, 1, x_91);
x_92 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_66, x_71, x_90);
x_93 = lean_st_ref_set(x_2, x_92);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_88);
lean_free_object(x_71);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_free_object(x_71);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
x_98 = !lean_is_exclusive(x_78);
if (x_98 == 0)
{
return x_78;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_78, 0);
lean_inc(x_99);
lean_dec(x_78);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_76);
lean_free_object(x_71);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
x_101 = lean_box(0);
lean_ctor_set_tag(x_69, 0);
lean_ctor_set(x_69, 0, x_101);
return x_69;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_71, 0);
x_103 = lean_ctor_get(x_71, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_71);
x_104 = lean_box(0);
x_105 = lean_array_get(x_104, x_67, x_102);
lean_dec_ref(x_67);
if (lean_obj_tag(x_105) == 1)
{
lean_object* x_106; lean_object* x_107; 
lean_free_object(x_69);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(x_106, x_3, x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_st_ref_take(x_2);
x_112 = l_Lean_NameSet_insert(x_103, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_102);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_66, x_113, x_111);
x_115 = lean_st_ref_set(x_2, x_114);
x_116 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_109;
}
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_66);
x_118 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_109;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_66);
x_120 = lean_ctor_get(x_107, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_121 = x_107;
} else {
 lean_dec_ref(x_107);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
x_123 = lean_box(0);
lean_ctor_set_tag(x_69, 0);
lean_ctor_set(x_69, 0, x_123);
return x_69;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_69, 0);
lean_inc(x_124);
lean_dec(x_69);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_box(0);
x_129 = lean_array_get(x_128, x_67, x_125);
lean_dec_ref(x_67);
if (lean_obj_tag(x_129) == 1)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(x_130, x_3, x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = lean_st_ref_take(x_2);
x_136 = l_Lean_NameSet_insert(x_126, x_134);
if (lean_is_scalar(x_127)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_127;
}
lean_ctor_set(x_137, 0, x_125);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_66, x_137, x_135);
x_139 = lean_st_ref_set(x_2, x_138);
x_140 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_141 = lean_alloc_ctor(0, 1, 0);
} else {
 x_141 = x_133;
}
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_66);
x_142 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_143 = lean_alloc_ctor(0, 1, 0);
} else {
 x_143 = x_133;
}
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_66);
x_144 = lean_ctor_get(x_131, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_145 = x_131;
} else {
 lean_dec_ref(x_131);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_69);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_3);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
case 4:
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_1);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_152 = lean_ctor_get(x_1, 0);
x_153 = lean_ctor_get(x_152, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 3);
lean_inc_ref(x_154);
lean_dec_ref(x_152);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_array_get_size(x_154);
x_157 = lean_box(0);
x_158 = lean_nat_dec_lt(x_155, x_156);
if (x_158 == 0)
{
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_157);
return x_1;
}
else
{
uint8_t x_159; 
x_159 = lean_nat_dec_le(x_156, x_156);
if (x_159 == 0)
{
if (x_158 == 0)
{
lean_dec_ref(x_154);
lean_dec(x_153);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_157);
return x_1;
}
else
{
size_t x_160; size_t x_161; lean_object* x_162; 
lean_free_object(x_1);
x_160 = 0;
x_161 = lean_usize_of_nat(x_156);
x_162 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(x_153, x_154, x_160, x_161, x_157, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_154);
return x_162;
}
}
else
{
size_t x_163; size_t x_164; lean_object* x_165; 
lean_free_object(x_1);
x_163 = 0;
x_164 = lean_usize_of_nat(x_156);
x_165 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(x_153, x_154, x_163, x_164, x_157, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_154);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
lean_dec(x_1);
x_167 = lean_ctor_get(x_166, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 3);
lean_inc_ref(x_168);
lean_dec_ref(x_166);
x_169 = lean_unsigned_to_nat(0u);
x_170 = lean_array_get_size(x_168);
x_171 = lean_box(0);
x_172 = lean_nat_dec_lt(x_169, x_170);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_171);
return x_173;
}
else
{
uint8_t x_174; 
x_174 = lean_nat_dec_le(x_170, x_170);
if (x_174 == 0)
{
if (x_172 == 0)
{
lean_object* x_175; 
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_171);
return x_175;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; 
x_176 = 0;
x_177 = lean_usize_of_nat(x_170);
x_178 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(x_167, x_168, x_176, x_177, x_171, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_168);
return x_178;
}
}
else
{
size_t x_179; size_t x_180; lean_object* x_181; 
x_179 = 0;
x_180 = lean_usize_of_nat(x_170);
x_181 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(x_167, x_168, x_179, x_180, x_171, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_168);
return x_181;
}
}
}
}
default: 
{
uint8_t x_182; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_182 = !lean_is_exclusive(x_1);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_1, 0);
lean_dec(x_183);
x_184 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_1);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_20);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
lean_inc(x_1);
x_24 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_21, x_22, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_26 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(x_23, x_6, x_25, x_8, x_9, x_10, x_11);
x_13 = x_26;
goto block_18;
}
else
{
uint8_t x_27; 
lean_dec_ref(x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_20);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_31 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(x_30, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = x_31;
goto block_18;
}
}
else
{
lean_object* x_32; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_5);
return x_32;
}
block_18:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(1);
x_8 = lean_st_mk_ref(x_7);
x_9 = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2;
x_10 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(x_1, x_8, x_9, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_st_ref_get(x_8);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = lean_st_ref_get(x_8);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0;
x_3 = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_panic_fn(x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(100u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_array_push(x_2, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
case 4:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_2);
x_10 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3;
x_11 = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0;
x_3 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(x_6, x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_array_uget(x_3, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(x_10, x_11, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Array_append___redArg(x_2, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Array_append___redArg(x_2, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec_ref(x_2);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_20; uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_6, x_1);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_7);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_35 = 0;
x_36 = lean_array_fget_borrowed(x_2, x_6);
x_37 = lean_nat_dec_eq(x_3, x_6);
if (x_37 == 0)
{
lean_object* x_38; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_36);
x_38 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_35, x_36, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_array_push(x_7, x_39);
x_14 = x_40;
x_15 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
if (x_4 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_5);
x_45 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(x_5, x_7, x_44, x_8, x_9, x_10, x_11, x_12);
x_20 = x_45;
goto block_32;
}
else
{
lean_object* x_46; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_36);
x_46 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_35, x_36, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_array_push(x_7, x_47);
x_49 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_5);
x_50 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(x_5, x_48, x_49, x_8, x_9, x_10, x_11, x_12);
x_20 = x_50;
goto block_32;
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_6 = x_17;
x_7 = x_14;
goto _start;
}
block_32:
{
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; 
lean_free_object(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_14 = x_24;
x_15 = lean_box(0);
goto block_19;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_14 = x_28;
x_15 = lean_box(0);
goto block_19;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_array_uget(x_3, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam_default(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_13 = 0;
x_14 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0;
x_15 = lean_array_get_borrowed(x_14, x_2, x_3);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1;
x_51 = l_Lean_instSingletonFVarIdFVarIdSet;
lean_inc(x_16);
x_52 = lean_apply_1(x_51, x_16);
x_53 = l_Lean_Compiler_LCNF_Code_dependsOn(x_13, x_5, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_array_get_size(x_1);
x_55 = lean_nat_dec_lt(x_17, x_54);
if (x_55 == 0)
{
lean_dec(x_52);
x_19 = x_53;
goto block_50;
}
else
{
if (x_55 == 0)
{
lean_dec(x_52);
x_19 = x_53;
goto block_50;
}
else
{
size_t x_56; size_t x_57; uint8_t x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_54);
x_58 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(x_52, x_1, x_56, x_57);
lean_dec(x_52);
x_19 = x_58;
goto block_50;
}
}
}
else
{
lean_dec(x_52);
x_19 = x_53;
goto block_50;
}
block_50:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_get_size(x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_21 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(x_20, x_2, x_3, x_19, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_array_size(x_1);
x_24 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_25 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(x_23, x_24, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_27 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_13, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Compiler_LCNF_attachCodeDecls(x_13, x_26, x_28);
lean_dec(x_26);
x_30 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3));
x_31 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_13, x_22, x_29, x_30, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_6);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 1, x_19);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*1 + 1, x_19);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_27, 0);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_25, 0);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
lean_dec(x_21);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_4);
x_18 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1;
x_13 = lean_st_mk_ref(x_12);
lean_inc(x_13);
x_14 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_st_ref_get(x_13);
lean_dec(x_13);
lean_dec(x_16);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_st_ref_get(x_13);
lean_dec(x_13);
lean_dec(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
}
else
{
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
x_13 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc_ref(x_1);
x_6 = l_Array_toSubarray___redArg(x_1, x_5, x_2);
x_7 = l_Subarray_copy___redArg(x_6);
x_8 = l_Array_append___redArg(x_7, x_3);
x_15 = lean_array_get_size(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_18 = lean_nat_dec_le(x_17, x_5);
if (x_18 == 0)
{
x_9 = x_17;
x_10 = x_15;
goto block_14;
}
else
{
lean_dec(x_17);
x_9 = x_5;
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Array_toSubarray___redArg(x_1, x_9, x_10);
x_12 = l_Subarray_copy___redArg(x_11);
x_13 = l_Array_append___redArg(x_8, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_31; uint8_t x_32; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
lean_inc(x_21);
lean_inc_ref(x_1);
x_22 = l_Array_toSubarray___redArg(x_1, x_19, x_21);
x_23 = l_Subarray_copy___redArg(x_22);
x_24 = l_Array_append___redArg(x_23, x_3);
x_31 = lean_array_get_size(x_1);
x_32 = lean_nat_dec_le(x_21, x_19);
if (x_32 == 0)
{
x_25 = x_21;
x_26 = x_31;
goto block_30;
}
else
{
lean_dec(x_21);
x_25 = x_19;
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Array_toSubarray___redArg(x_1, x_25, x_26);
x_28 = l_Subarray_copy___redArg(x_27);
x_29 = l_Array_append___redArg(x_24, x_28);
lean_dec_ref(x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_1, x_2, x_3, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(x_1, x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_array_size(x_1);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(x_5, x_6, x_1);
x_8 = lean_array_size(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(x_8, x_6, x_3);
x_10 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_7, x_2, x_9, x_4);
lean_dec_ref(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_ref_get(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 1)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(x_3, x_1);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
lean_free_object(x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_array_get(x_21, x_2, x_19);
if (lean_obj_tag(x_22) == 1)
{
uint8_t x_23; 
lean_free_object(x_15);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_24, x_5, x_7, x_9);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_29);
x_31 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_14, x_30);
lean_dec(x_30);
lean_dec(x_14);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
if (x_34 == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_35; uint8_t x_36; uint8_t x_37; 
lean_free_object(x_26);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_35 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get_uint8(x_32, sizeof(void*)*1 + 1);
lean_dec(x_32);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_59 = lean_ctor_get(x_38, 3);
lean_inc(x_59);
lean_dec_ref(x_38);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_39);
x_62 = lean_nat_dec_le(x_59, x_60);
if (x_62 == 0)
{
lean_ctor_set(x_29, 1, x_61);
lean_ctor_set(x_29, 0, x_59);
x_40 = x_29;
goto block_58;
}
else
{
lean_dec(x_59);
lean_ctor_set(x_29, 1, x_61);
lean_ctor_set(x_29, 0, x_60);
x_40 = x_29;
goto block_58;
}
block_58:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec_ref(x_35);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
x_45 = l_Array_toSubarray___redArg(x_39, x_43, x_44);
x_46 = l_Subarray_copy___redArg(x_45);
x_47 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_46, x_36);
lean_dec_ref(x_46);
lean_ctor_set_tag(x_40, 3);
lean_ctor_set(x_40, 1, x_47);
lean_ctor_set(x_40, 0, x_41);
if (lean_is_scalar(x_33)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_33;
}
lean_ctor_set(x_48, 0, x_40);
if (lean_is_scalar(x_27)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_27;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_40);
x_52 = l_Array_toSubarray___redArg(x_39, x_50, x_51);
x_53 = l_Subarray_copy___redArg(x_52);
x_54 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_53, x_36);
lean_dec_ref(x_53);
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_33)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_33;
}
lean_ctor_set(x_56, 0, x_55);
if (lean_is_scalar(x_27)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_27;
}
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_63 = lean_ctor_get(x_29, 0);
x_64 = lean_ctor_get(x_29, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_29);
x_77 = lean_ctor_get(x_63, 3);
lean_inc(x_77);
lean_dec_ref(x_63);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_array_get_size(x_64);
x_80 = lean_nat_dec_le(x_77, x_78);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_79);
x_65 = x_81;
goto block_76;
}
else
{
lean_object* x_82; 
lean_dec(x_77);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_79);
x_65 = x_82;
goto block_76;
}
block_76:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_35, 0);
lean_inc(x_66);
lean_dec_ref(x_35);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = l_Array_toSubarray___redArg(x_64, x_67, x_68);
x_71 = l_Subarray_copy___redArg(x_70);
x_72 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_71, x_36);
lean_dec_ref(x_71);
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(3, 2, 0);
} else {
 x_73 = x_69;
 lean_ctor_set_tag(x_73, 3);
}
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_33)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_33;
}
lean_ctor_set(x_74, 0, x_73);
if (lean_is_scalar(x_27)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_27;
}
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get_uint8(x_32, sizeof(void*)*1 + 1);
lean_dec(x_32);
x_85 = !lean_is_exclusive(x_29);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_29, 0);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_eq(x_86, x_87);
if (x_88 == 1)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_29);
lean_dec(x_86);
lean_free_object(x_26);
lean_free_object(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec_ref(x_83);
x_90 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_91 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_90, x_84);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_91);
lean_ctor_set(x_17, 0, x_89);
if (lean_is_scalar(x_33)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_33;
}
lean_ctor_set(x_92, 0, x_17);
if (lean_is_scalar(x_27)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_27;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_27);
x_94 = 0;
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_sub(x_86, x_95);
lean_dec(x_86);
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 0, x_96);
lean_ctor_set_tag(x_26, 0);
x_97 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
x_98 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_94, x_26, x_97, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_83, 0);
lean_inc(x_101);
lean_dec_ref(x_83);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_ctor_set(x_22, 0, x_102);
x_103 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_104 = lean_array_push(x_103, x_22);
x_105 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_104, x_84);
lean_dec_ref(x_104);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_105);
lean_ctor_set(x_17, 0, x_101);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_17);
if (lean_is_scalar(x_33)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_33;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_98, 0, x_107);
return x_98;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_98, 0);
lean_inc(x_108);
lean_dec(x_98);
x_109 = lean_ctor_get(x_83, 0);
lean_inc(x_109);
lean_dec_ref(x_83);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_ctor_set(x_22, 0, x_110);
x_111 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_112 = lean_array_push(x_111, x_22);
x_113 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_112, x_84);
lean_dec_ref(x_112);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_113);
lean_ctor_set(x_17, 0, x_109);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_17);
if (lean_is_scalar(x_33)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_33;
}
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_83);
lean_dec(x_33);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec_ref(x_2);
x_117 = !lean_is_exclusive(x_98);
if (x_117 == 0)
{
return x_98;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
lean_dec(x_98);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_29, 0);
lean_inc(x_120);
lean_dec(x_29);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_eq(x_120, x_121);
if (x_122 == 1)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_120);
lean_free_object(x_26);
lean_free_object(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_123 = lean_ctor_get(x_83, 0);
lean_inc(x_123);
lean_dec_ref(x_83);
x_124 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_125 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_124, x_84);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_125);
lean_ctor_set(x_17, 0, x_123);
if (lean_is_scalar(x_33)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_33;
}
lean_ctor_set(x_126, 0, x_17);
if (lean_is_scalar(x_27)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_27;
}
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_27);
x_128 = 0;
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_sub(x_120, x_129);
lean_dec(x_120);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_131);
x_132 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
x_133 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_128, x_26, x_132, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_83, 0);
lean_inc(x_136);
lean_dec_ref(x_83);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_ctor_set(x_22, 0, x_137);
x_138 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_139 = lean_array_push(x_138, x_22);
x_140 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_139, x_84);
lean_dec_ref(x_139);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_140);
lean_ctor_set(x_17, 0, x_136);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_17);
if (lean_is_scalar(x_33)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_33;
}
lean_ctor_set(x_142, 0, x_141);
if (lean_is_scalar(x_135)) {
 x_143 = lean_alloc_ctor(0, 1, 0);
} else {
 x_143 = x_135;
}
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_83);
lean_dec(x_33);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec_ref(x_2);
x_144 = lean_ctor_get(x_133, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_145 = x_133;
} else {
 lean_dec_ref(x_133);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
return x_146;
}
}
}
}
}
else
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_free_object(x_26);
lean_dec(x_29);
lean_free_object(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_147 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_147);
x_148 = lean_ctor_get_uint8(x_32, sizeof(void*)*1 + 1);
lean_dec(x_32);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_151 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_150, x_148);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_151);
lean_ctor_set(x_17, 0, x_149);
if (lean_is_scalar(x_33)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_33;
}
lean_ctor_set(x_152, 0, x_17);
if (lean_is_scalar(x_27)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_27;
}
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_31);
lean_free_object(x_26);
lean_dec(x_29);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_154 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_155 = lean_alloc_ctor(0, 1, 0);
} else {
 x_155 = x_27;
}
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_26, 0);
lean_inc(x_156);
lean_dec(x_26);
x_157 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_156);
x_158 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_14, x_157);
lean_dec(x_157);
lean_dec(x_14);
if (lean_obj_tag(x_158) == 1)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get_uint8(x_159, sizeof(void*)*1);
if (x_161 == 0)
{
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_162 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_162);
x_163 = lean_ctor_get_uint8(x_159, sizeof(void*)*1 + 1);
lean_dec(x_159);
x_164 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_156, 1);
lean_inc_ref(x_165);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_166 = x_156;
} else {
 lean_dec_ref(x_156);
 x_166 = lean_box(0);
}
x_179 = lean_ctor_get(x_164, 3);
lean_inc(x_179);
lean_dec_ref(x_164);
x_180 = lean_unsigned_to_nat(0u);
x_181 = lean_array_get_size(x_165);
x_182 = lean_nat_dec_le(x_179, x_180);
if (x_182 == 0)
{
lean_object* x_183; 
if (lean_is_scalar(x_166)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_166;
}
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_181);
x_167 = x_183;
goto block_178;
}
else
{
lean_object* x_184; 
lean_dec(x_179);
if (lean_is_scalar(x_166)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_166;
}
lean_ctor_set(x_184, 0, x_180);
lean_ctor_set(x_184, 1, x_181);
x_167 = x_184;
goto block_178;
}
block_178:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_168 = lean_ctor_get(x_162, 0);
lean_inc(x_168);
lean_dec_ref(x_162);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = l_Array_toSubarray___redArg(x_165, x_169, x_170);
x_173 = l_Subarray_copy___redArg(x_172);
x_174 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_173, x_163);
lean_dec_ref(x_173);
if (lean_is_scalar(x_171)) {
 x_175 = lean_alloc_ctor(3, 2, 0);
} else {
 x_175 = x_171;
 lean_ctor_set_tag(x_175, 3);
}
lean_ctor_set(x_175, 0, x_168);
lean_ctor_set(x_175, 1, x_174);
if (lean_is_scalar(x_160)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_160;
}
lean_ctor_set(x_176, 0, x_175);
if (lean_is_scalar(x_27)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_27;
}
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
else
{
lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_185 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_185);
x_186 = lean_ctor_get_uint8(x_159, sizeof(void*)*1 + 1);
lean_dec(x_159);
x_187 = lean_ctor_get(x_156, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_188 = x_156;
} else {
 lean_dec_ref(x_156);
 x_188 = lean_box(0);
}
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_nat_dec_eq(x_187, x_189);
if (x_190 == 1)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_188);
lean_dec(x_187);
lean_free_object(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_191 = lean_ctor_get(x_185, 0);
lean_inc(x_191);
lean_dec_ref(x_185);
x_192 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_193 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_192, x_186);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_193);
lean_ctor_set(x_17, 0, x_191);
if (lean_is_scalar(x_160)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_160;
}
lean_ctor_set(x_194, 0, x_17);
if (lean_is_scalar(x_27)) {
 x_195 = lean_alloc_ctor(0, 1, 0);
} else {
 x_195 = x_27;
}
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
else
{
uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_27);
x_196 = 0;
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_sub(x_187, x_197);
lean_dec(x_187);
if (lean_is_scalar(x_188)) {
 x_199 = lean_alloc_ctor(0, 1, 0);
} else {
 x_199 = x_188;
 lean_ctor_set_tag(x_199, 0);
}
lean_ctor_set(x_199, 0, x_198);
x_200 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
x_202 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_196, x_200, x_201, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_185, 0);
lean_inc(x_205);
lean_dec_ref(x_185);
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
lean_ctor_set(x_22, 0, x_206);
x_207 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_208 = lean_array_push(x_207, x_22);
x_209 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_208, x_186);
lean_dec_ref(x_208);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_209);
lean_ctor_set(x_17, 0, x_205);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_17);
if (lean_is_scalar(x_160)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_160;
}
lean_ctor_set(x_211, 0, x_210);
if (lean_is_scalar(x_204)) {
 x_212 = lean_alloc_ctor(0, 1, 0);
} else {
 x_212 = x_204;
}
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec_ref(x_185);
lean_dec(x_160);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec_ref(x_2);
x_213 = lean_ctor_get(x_202, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_214 = x_202;
} else {
 lean_dec_ref(x_202);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
return x_215;
}
}
}
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_156);
lean_free_object(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_216 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_216);
x_217 = lean_ctor_get_uint8(x_159, sizeof(void*)*1 + 1);
lean_dec(x_159);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec_ref(x_216);
x_219 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_220 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_219, x_217);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_220);
lean_ctor_set(x_17, 0, x_218);
if (lean_is_scalar(x_160)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_160;
}
lean_ctor_set(x_221, 0, x_17);
if (lean_is_scalar(x_27)) {
 x_222 = lean_alloc_ctor(0, 1, 0);
} else {
 x_222 = x_27;
}
lean_ctor_set(x_222, 0, x_221);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_158);
lean_dec(x_156);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_223 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_224 = lean_alloc_ctor(0, 1, 0);
} else {
 x_224 = x_27;
}
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_26);
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_225 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_226 = lean_alloc_ctor(0, 1, 0);
} else {
 x_226 = x_27;
}
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
else
{
uint8_t x_227; 
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_227 = !lean_is_exclusive(x_25);
if (x_227 == 0)
{
return x_25;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_25, 0);
lean_inc(x_228);
lean_dec(x_25);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_22, 0);
lean_inc(x_230);
lean_dec(x_22);
x_231 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_230, x_5, x_7, x_9);
lean_dec(x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_obj_tag(x_232) == 1)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_234);
x_237 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_14, x_236);
lean_dec(x_236);
lean_dec(x_14);
if (lean_obj_tag(x_237) == 1)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get_uint8(x_238, sizeof(void*)*1);
if (x_240 == 0)
{
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_dec(x_235);
lean_free_object(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_241 = lean_ctor_get(x_238, 0);
lean_inc_ref(x_241);
x_242 = lean_ctor_get_uint8(x_238, sizeof(void*)*1 + 1);
lean_dec(x_238);
x_243 = lean_ctor_get(x_234, 0);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_234, 1);
lean_inc_ref(x_244);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_245 = x_234;
} else {
 lean_dec_ref(x_234);
 x_245 = lean_box(0);
}
x_258 = lean_ctor_get(x_243, 3);
lean_inc(x_258);
lean_dec_ref(x_243);
x_259 = lean_unsigned_to_nat(0u);
x_260 = lean_array_get_size(x_244);
x_261 = lean_nat_dec_le(x_258, x_259);
if (x_261 == 0)
{
lean_object* x_262; 
if (lean_is_scalar(x_245)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_245;
}
lean_ctor_set(x_262, 0, x_258);
lean_ctor_set(x_262, 1, x_260);
x_246 = x_262;
goto block_257;
}
else
{
lean_object* x_263; 
lean_dec(x_258);
if (lean_is_scalar(x_245)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_245;
}
lean_ctor_set(x_263, 0, x_259);
lean_ctor_set(x_263, 1, x_260);
x_246 = x_263;
goto block_257;
}
block_257:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_247 = lean_ctor_get(x_241, 0);
lean_inc(x_247);
lean_dec_ref(x_241);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_250 = x_246;
} else {
 lean_dec_ref(x_246);
 x_250 = lean_box(0);
}
x_251 = l_Array_toSubarray___redArg(x_244, x_248, x_249);
x_252 = l_Subarray_copy___redArg(x_251);
x_253 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_252, x_242);
lean_dec_ref(x_252);
if (lean_is_scalar(x_250)) {
 x_254 = lean_alloc_ctor(3, 2, 0);
} else {
 x_254 = x_250;
 lean_ctor_set_tag(x_254, 3);
}
lean_ctor_set(x_254, 0, x_247);
lean_ctor_set(x_254, 1, x_253);
if (lean_is_scalar(x_239)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_239;
}
lean_ctor_set(x_255, 0, x_254);
if (lean_is_scalar(x_233)) {
 x_256 = lean_alloc_ctor(0, 1, 0);
} else {
 x_256 = x_233;
}
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
}
else
{
lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_264 = lean_ctor_get(x_238, 0);
lean_inc_ref(x_264);
x_265 = lean_ctor_get_uint8(x_238, sizeof(void*)*1 + 1);
lean_dec(x_238);
x_266 = lean_ctor_get(x_234, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_267 = x_234;
} else {
 lean_dec_ref(x_234);
 x_267 = lean_box(0);
}
x_268 = lean_unsigned_to_nat(0u);
x_269 = lean_nat_dec_eq(x_266, x_268);
if (x_269 == 1)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_235);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_270 = lean_ctor_get(x_264, 0);
lean_inc(x_270);
lean_dec_ref(x_264);
x_271 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_272 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_271, x_265);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_272);
lean_ctor_set(x_17, 0, x_270);
if (lean_is_scalar(x_239)) {
 x_273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_273 = x_239;
}
lean_ctor_set(x_273, 0, x_17);
if (lean_is_scalar(x_233)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_233;
}
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
else
{
uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_233);
x_275 = 0;
x_276 = lean_unsigned_to_nat(1u);
x_277 = lean_nat_sub(x_266, x_276);
lean_dec(x_266);
if (lean_is_scalar(x_267)) {
 x_278 = lean_alloc_ctor(0, 1, 0);
} else {
 x_278 = x_267;
 lean_ctor_set_tag(x_278, 0);
}
lean_ctor_set(x_278, 0, x_277);
if (lean_is_scalar(x_235)) {
 x_279 = lean_alloc_ctor(0, 1, 0);
} else {
 x_279 = x_235;
 lean_ctor_set_tag(x_279, 0);
}
lean_ctor_set(x_279, 0, x_278);
x_280 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
x_281 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_275, x_279, x_280, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_264, 0);
lean_inc(x_284);
lean_dec_ref(x_264);
x_285 = lean_ctor_get(x_282, 0);
lean_inc(x_285);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_287 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_288 = lean_array_push(x_287, x_286);
x_289 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_288, x_265);
lean_dec_ref(x_288);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_289);
lean_ctor_set(x_17, 0, x_284);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_282);
lean_ctor_set(x_290, 1, x_17);
if (lean_is_scalar(x_239)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_239;
}
lean_ctor_set(x_291, 0, x_290);
if (lean_is_scalar(x_283)) {
 x_292 = lean_alloc_ctor(0, 1, 0);
} else {
 x_292 = x_283;
}
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec_ref(x_264);
lean_dec(x_239);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec_ref(x_2);
x_293 = lean_ctor_get(x_281, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_294 = x_281;
} else {
 lean_dec_ref(x_281);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 1, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_293);
return x_295;
}
}
}
}
else
{
lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_296 = lean_ctor_get(x_238, 0);
lean_inc_ref(x_296);
x_297 = lean_ctor_get_uint8(x_238, sizeof(void*)*1 + 1);
lean_dec(x_238);
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
lean_dec_ref(x_296);
x_299 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_300 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_19, x_299, x_297);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_300);
lean_ctor_set(x_17, 0, x_298);
if (lean_is_scalar(x_239)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_239;
}
lean_ctor_set(x_301, 0, x_17);
if (lean_is_scalar(x_233)) {
 x_302 = lean_alloc_ctor(0, 1, 0);
} else {
 x_302 = x_233;
}
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_234);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_303 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_304 = lean_alloc_ctor(0, 1, 0);
} else {
 x_304 = x_233;
}
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_232);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_305 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_306 = lean_alloc_ctor(0, 1, 0);
} else {
 x_306 = x_233;
}
lean_ctor_set(x_306, 0, x_305);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_307 = lean_ctor_get(x_231, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_308 = x_231;
} else {
 lean_dec_ref(x_231);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 1, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_307);
return x_309;
}
}
}
else
{
lean_object* x_310; 
lean_dec(x_22);
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_310 = lean_box(0);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_310);
return x_15;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_17, 0);
lean_inc(x_311);
lean_dec(x_17);
x_312 = lean_box(0);
x_313 = lean_array_get(x_312, x_2, x_311);
if (lean_obj_tag(x_313) == 1)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_free_object(x_15);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 x_315 = x_313;
} else {
 lean_dec_ref(x_313);
 x_315 = lean_box(0);
}
x_316 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_314, x_5, x_7, x_9);
lean_dec(x_314);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_318 = x_316;
} else {
 lean_dec_ref(x_316);
 x_318 = lean_box(0);
}
if (lean_obj_tag(x_317) == 1)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 x_320 = x_317;
} else {
 lean_dec_ref(x_317);
 x_320 = lean_box(0);
}
x_321 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_319);
x_322 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_14, x_321);
lean_dec(x_321);
lean_dec(x_14);
if (lean_obj_tag(x_322) == 1)
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 x_324 = x_322;
} else {
 lean_dec_ref(x_322);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get_uint8(x_323, sizeof(void*)*1);
if (x_325 == 0)
{
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_326 = lean_ctor_get(x_323, 0);
lean_inc_ref(x_326);
x_327 = lean_ctor_get_uint8(x_323, sizeof(void*)*1 + 1);
lean_dec(x_323);
x_328 = lean_ctor_get(x_319, 0);
lean_inc_ref(x_328);
x_329 = lean_ctor_get(x_319, 1);
lean_inc_ref(x_329);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_330 = x_319;
} else {
 lean_dec_ref(x_319);
 x_330 = lean_box(0);
}
x_343 = lean_ctor_get(x_328, 3);
lean_inc(x_343);
lean_dec_ref(x_328);
x_344 = lean_unsigned_to_nat(0u);
x_345 = lean_array_get_size(x_329);
x_346 = lean_nat_dec_le(x_343, x_344);
if (x_346 == 0)
{
lean_object* x_347; 
if (lean_is_scalar(x_330)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_330;
}
lean_ctor_set(x_347, 0, x_343);
lean_ctor_set(x_347, 1, x_345);
x_331 = x_347;
goto block_342;
}
else
{
lean_object* x_348; 
lean_dec(x_343);
if (lean_is_scalar(x_330)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_330;
}
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
x_331 = x_348;
goto block_342;
}
block_342:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_332 = lean_ctor_get(x_326, 0);
lean_inc(x_332);
lean_dec_ref(x_326);
x_333 = lean_ctor_get(x_331, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_335 = x_331;
} else {
 lean_dec_ref(x_331);
 x_335 = lean_box(0);
}
x_336 = l_Array_toSubarray___redArg(x_329, x_333, x_334);
x_337 = l_Subarray_copy___redArg(x_336);
x_338 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_311, x_337, x_327);
lean_dec_ref(x_337);
if (lean_is_scalar(x_335)) {
 x_339 = lean_alloc_ctor(3, 2, 0);
} else {
 x_339 = x_335;
 lean_ctor_set_tag(x_339, 3);
}
lean_ctor_set(x_339, 0, x_332);
lean_ctor_set(x_339, 1, x_338);
if (lean_is_scalar(x_324)) {
 x_340 = lean_alloc_ctor(1, 1, 0);
} else {
 x_340 = x_324;
}
lean_ctor_set(x_340, 0, x_339);
if (lean_is_scalar(x_318)) {
 x_341 = lean_alloc_ctor(0, 1, 0);
} else {
 x_341 = x_318;
}
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
else
{
lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_349 = lean_ctor_get(x_323, 0);
lean_inc_ref(x_349);
x_350 = lean_ctor_get_uint8(x_323, sizeof(void*)*1 + 1);
lean_dec(x_323);
x_351 = lean_ctor_get(x_319, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 x_352 = x_319;
} else {
 lean_dec_ref(x_319);
 x_352 = lean_box(0);
}
x_353 = lean_unsigned_to_nat(0u);
x_354 = lean_nat_dec_eq(x_351, x_353);
if (x_354 == 1)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_320);
lean_dec(x_315);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_355 = lean_ctor_get(x_349, 0);
lean_inc(x_355);
lean_dec_ref(x_349);
x_356 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_357 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_311, x_356, x_350);
x_358 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_357);
if (lean_is_scalar(x_324)) {
 x_359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_359 = x_324;
}
lean_ctor_set(x_359, 0, x_358);
if (lean_is_scalar(x_318)) {
 x_360 = lean_alloc_ctor(0, 1, 0);
} else {
 x_360 = x_318;
}
lean_ctor_set(x_360, 0, x_359);
return x_360;
}
else
{
uint8_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_318);
x_361 = 0;
x_362 = lean_unsigned_to_nat(1u);
x_363 = lean_nat_sub(x_351, x_362);
lean_dec(x_351);
if (lean_is_scalar(x_352)) {
 x_364 = lean_alloc_ctor(0, 1, 0);
} else {
 x_364 = x_352;
 lean_ctor_set_tag(x_364, 0);
}
lean_ctor_set(x_364, 0, x_363);
if (lean_is_scalar(x_320)) {
 x_365 = lean_alloc_ctor(0, 1, 0);
} else {
 x_365 = x_320;
 lean_ctor_set_tag(x_365, 0);
}
lean_ctor_set(x_365, 0, x_364);
x_366 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
x_367 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_361, x_365, x_366, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_369 = x_367;
} else {
 lean_dec_ref(x_367);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_349, 0);
lean_inc(x_370);
lean_dec_ref(x_349);
x_371 = lean_ctor_get(x_368, 0);
lean_inc(x_371);
if (lean_is_scalar(x_315)) {
 x_372 = lean_alloc_ctor(1, 1, 0);
} else {
 x_372 = x_315;
}
lean_ctor_set(x_372, 0, x_371);
x_373 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_374 = lean_array_push(x_373, x_372);
x_375 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_311, x_374, x_350);
lean_dec_ref(x_374);
x_376 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_376, 0, x_370);
lean_ctor_set(x_376, 1, x_375);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_368);
lean_ctor_set(x_377, 1, x_376);
if (lean_is_scalar(x_324)) {
 x_378 = lean_alloc_ctor(1, 1, 0);
} else {
 x_378 = x_324;
}
lean_ctor_set(x_378, 0, x_377);
if (lean_is_scalar(x_369)) {
 x_379 = lean_alloc_ctor(0, 1, 0);
} else {
 x_379 = x_369;
}
lean_ctor_set(x_379, 0, x_378);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec_ref(x_349);
lean_dec(x_324);
lean_dec(x_315);
lean_dec(x_311);
lean_dec_ref(x_2);
x_380 = lean_ctor_get(x_367, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_381 = x_367;
} else {
 lean_dec_ref(x_367);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 1, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_380);
return x_382;
}
}
}
}
else
{
lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_315);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_383 = lean_ctor_get(x_323, 0);
lean_inc_ref(x_383);
x_384 = lean_ctor_get_uint8(x_323, sizeof(void*)*1 + 1);
lean_dec(x_323);
x_385 = lean_ctor_get(x_383, 0);
lean_inc(x_385);
lean_dec_ref(x_383);
x_386 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_387 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_311, x_386, x_384);
x_388 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_387);
if (lean_is_scalar(x_324)) {
 x_389 = lean_alloc_ctor(1, 1, 0);
} else {
 x_389 = x_324;
}
lean_ctor_set(x_389, 0, x_388);
if (lean_is_scalar(x_318)) {
 x_390 = lean_alloc_ctor(0, 1, 0);
} else {
 x_390 = x_318;
}
lean_ctor_set(x_390, 0, x_389);
return x_390;
}
}
else
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_391 = lean_box(0);
if (lean_is_scalar(x_318)) {
 x_392 = lean_alloc_ctor(0, 1, 0);
} else {
 x_392 = x_318;
}
lean_ctor_set(x_392, 0, x_391);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_393 = lean_box(0);
if (lean_is_scalar(x_318)) {
 x_394 = lean_alloc_ctor(0, 1, 0);
} else {
 x_394 = x_318;
}
lean_ctor_set(x_394, 0, x_393);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_395 = lean_ctor_get(x_316, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_396 = x_316;
} else {
 lean_dec_ref(x_316);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_395);
return x_397;
}
}
else
{
lean_object* x_398; 
lean_dec(x_313);
lean_dec(x_311);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_398 = lean_box(0);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_398);
return x_15;
}
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = lean_ctor_get(x_15, 0);
lean_inc(x_399);
lean_dec(x_15);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_401 = x_399;
} else {
 lean_dec_ref(x_399);
 x_401 = lean_box(0);
}
x_402 = lean_box(0);
x_403 = lean_array_get(x_402, x_2, x_400);
if (lean_obj_tag(x_403) == 1)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_405 = x_403;
} else {
 lean_dec_ref(x_403);
 x_405 = lean_box(0);
}
x_406 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_404, x_5, x_7, x_9);
lean_dec(x_404);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_408 = x_406;
} else {
 lean_dec_ref(x_406);
 x_408 = lean_box(0);
}
if (lean_obj_tag(x_407) == 1)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_410 = x_407;
} else {
 lean_dec_ref(x_407);
 x_410 = lean_box(0);
}
x_411 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_409);
x_412 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_14, x_411);
lean_dec(x_411);
lean_dec(x_14);
if (lean_obj_tag(x_412) == 1)
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_414 = x_412;
} else {
 lean_dec_ref(x_412);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get_uint8(x_413, sizeof(void*)*1);
if (x_415 == 0)
{
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
lean_dec(x_410);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_416 = lean_ctor_get(x_413, 0);
lean_inc_ref(x_416);
x_417 = lean_ctor_get_uint8(x_413, sizeof(void*)*1 + 1);
lean_dec(x_413);
x_418 = lean_ctor_get(x_409, 0);
lean_inc_ref(x_418);
x_419 = lean_ctor_get(x_409, 1);
lean_inc_ref(x_419);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_420 = x_409;
} else {
 lean_dec_ref(x_409);
 x_420 = lean_box(0);
}
x_433 = lean_ctor_get(x_418, 3);
lean_inc(x_433);
lean_dec_ref(x_418);
x_434 = lean_unsigned_to_nat(0u);
x_435 = lean_array_get_size(x_419);
x_436 = lean_nat_dec_le(x_433, x_434);
if (x_436 == 0)
{
lean_object* x_437; 
if (lean_is_scalar(x_420)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_420;
}
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_435);
x_421 = x_437;
goto block_432;
}
else
{
lean_object* x_438; 
lean_dec(x_433);
if (lean_is_scalar(x_420)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_420;
}
lean_ctor_set(x_438, 0, x_434);
lean_ctor_set(x_438, 1, x_435);
x_421 = x_438;
goto block_432;
}
block_432:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_422 = lean_ctor_get(x_416, 0);
lean_inc(x_422);
lean_dec_ref(x_416);
x_423 = lean_ctor_get(x_421, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_421, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_425 = x_421;
} else {
 lean_dec_ref(x_421);
 x_425 = lean_box(0);
}
x_426 = l_Array_toSubarray___redArg(x_419, x_423, x_424);
x_427 = l_Subarray_copy___redArg(x_426);
x_428 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_400, x_427, x_417);
lean_dec_ref(x_427);
if (lean_is_scalar(x_425)) {
 x_429 = lean_alloc_ctor(3, 2, 0);
} else {
 x_429 = x_425;
 lean_ctor_set_tag(x_429, 3);
}
lean_ctor_set(x_429, 0, x_422);
lean_ctor_set(x_429, 1, x_428);
if (lean_is_scalar(x_414)) {
 x_430 = lean_alloc_ctor(1, 1, 0);
} else {
 x_430 = x_414;
}
lean_ctor_set(x_430, 0, x_429);
if (lean_is_scalar(x_408)) {
 x_431 = lean_alloc_ctor(0, 1, 0);
} else {
 x_431 = x_408;
}
lean_ctor_set(x_431, 0, x_430);
return x_431;
}
}
else
{
lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; 
x_439 = lean_ctor_get(x_413, 0);
lean_inc_ref(x_439);
x_440 = lean_ctor_get_uint8(x_413, sizeof(void*)*1 + 1);
lean_dec(x_413);
x_441 = lean_ctor_get(x_409, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_442 = x_409;
} else {
 lean_dec_ref(x_409);
 x_442 = lean_box(0);
}
x_443 = lean_unsigned_to_nat(0u);
x_444 = lean_nat_dec_eq(x_441, x_443);
if (x_444 == 1)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_410);
lean_dec(x_405);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_445 = lean_ctor_get(x_439, 0);
lean_inc(x_445);
lean_dec_ref(x_439);
x_446 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_447 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_400, x_446, x_440);
if (lean_is_scalar(x_401)) {
 x_448 = lean_alloc_ctor(3, 2, 0);
} else {
 x_448 = x_401;
 lean_ctor_set_tag(x_448, 3);
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_447);
if (lean_is_scalar(x_414)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_414;
}
lean_ctor_set(x_449, 0, x_448);
if (lean_is_scalar(x_408)) {
 x_450 = lean_alloc_ctor(0, 1, 0);
} else {
 x_450 = x_408;
}
lean_ctor_set(x_450, 0, x_449);
return x_450;
}
else
{
uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_408);
x_451 = 0;
x_452 = lean_unsigned_to_nat(1u);
x_453 = lean_nat_sub(x_441, x_452);
lean_dec(x_441);
if (lean_is_scalar(x_442)) {
 x_454 = lean_alloc_ctor(0, 1, 0);
} else {
 x_454 = x_442;
 lean_ctor_set_tag(x_454, 0);
}
lean_ctor_set(x_454, 0, x_453);
if (lean_is_scalar(x_410)) {
 x_455 = lean_alloc_ctor(0, 1, 0);
} else {
 x_455 = x_410;
 lean_ctor_set_tag(x_455, 0);
}
lean_ctor_set(x_455, 0, x_454);
x_456 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
x_457 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_451, x_455, x_456, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 x_459 = x_457;
} else {
 lean_dec_ref(x_457);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_439, 0);
lean_inc(x_460);
lean_dec_ref(x_439);
x_461 = lean_ctor_get(x_458, 0);
lean_inc(x_461);
if (lean_is_scalar(x_405)) {
 x_462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_462 = x_405;
}
lean_ctor_set(x_462, 0, x_461);
x_463 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_464 = lean_array_push(x_463, x_462);
x_465 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_400, x_464, x_440);
lean_dec_ref(x_464);
if (lean_is_scalar(x_401)) {
 x_466 = lean_alloc_ctor(3, 2, 0);
} else {
 x_466 = x_401;
 lean_ctor_set_tag(x_466, 3);
}
lean_ctor_set(x_466, 0, x_460);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_458);
lean_ctor_set(x_467, 1, x_466);
if (lean_is_scalar(x_414)) {
 x_468 = lean_alloc_ctor(1, 1, 0);
} else {
 x_468 = x_414;
}
lean_ctor_set(x_468, 0, x_467);
if (lean_is_scalar(x_459)) {
 x_469 = lean_alloc_ctor(0, 1, 0);
} else {
 x_469 = x_459;
}
lean_ctor_set(x_469, 0, x_468);
return x_469;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec_ref(x_439);
lean_dec(x_414);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_400);
lean_dec_ref(x_2);
x_470 = lean_ctor_get(x_457, 0);
lean_inc(x_470);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 x_471 = x_457;
} else {
 lean_dec_ref(x_457);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 1, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_470);
return x_472;
}
}
}
}
else
{
lean_object* x_473; uint8_t x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_405);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_473 = lean_ctor_get(x_413, 0);
lean_inc_ref(x_473);
x_474 = lean_ctor_get_uint8(x_413, sizeof(void*)*1 + 1);
lean_dec(x_413);
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
lean_dec_ref(x_473);
x_476 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_477 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_400, x_476, x_474);
if (lean_is_scalar(x_401)) {
 x_478 = lean_alloc_ctor(3, 2, 0);
} else {
 x_478 = x_401;
 lean_ctor_set_tag(x_478, 3);
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_477);
if (lean_is_scalar(x_414)) {
 x_479 = lean_alloc_ctor(1, 1, 0);
} else {
 x_479 = x_414;
}
lean_ctor_set(x_479, 0, x_478);
if (lean_is_scalar(x_408)) {
 x_480 = lean_alloc_ctor(0, 1, 0);
} else {
 x_480 = x_408;
}
lean_ctor_set(x_480, 0, x_479);
return x_480;
}
}
else
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_412);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_481 = lean_box(0);
if (lean_is_scalar(x_408)) {
 x_482 = lean_alloc_ctor(0, 1, 0);
} else {
 x_482 = x_408;
}
lean_ctor_set(x_482, 0, x_481);
return x_482;
}
}
else
{
lean_object* x_483; lean_object* x_484; 
lean_dec(x_407);
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_483 = lean_box(0);
if (lean_is_scalar(x_408)) {
 x_484 = lean_alloc_ctor(0, 1, 0);
} else {
 x_484 = x_408;
}
lean_ctor_set(x_484, 0, x_483);
return x_484;
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_405);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_485 = lean_ctor_get(x_406, 0);
lean_inc(x_485);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_486 = x_406;
} else {
 lean_dec_ref(x_406);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 1, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_485);
return x_487;
}
}
else
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_488 = lean_box(0);
x_489 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_489, 0, x_488);
return x_489;
}
}
}
else
{
lean_object* x_490; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_490 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_490);
return x_12;
}
}
else
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_12, 0);
lean_inc(x_491);
lean_dec(x_12);
x_492 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(x_3, x_1);
if (lean_obj_tag(x_492) == 1)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 x_494 = x_492;
} else {
 lean_dec_ref(x_492);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_493, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_496 = x_493;
} else {
 lean_dec_ref(x_493);
 x_496 = lean_box(0);
}
x_497 = lean_box(0);
x_498 = lean_array_get(x_497, x_2, x_495);
if (lean_obj_tag(x_498) == 1)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_494);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 x_500 = x_498;
} else {
 lean_dec_ref(x_498);
 x_500 = lean_box(0);
}
x_501 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_499, x_5, x_7, x_9);
lean_dec(x_499);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 x_503 = x_501;
} else {
 lean_dec_ref(x_501);
 x_503 = lean_box(0);
}
if (lean_obj_tag(x_502) == 1)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_504 = lean_ctor_get(x_502, 0);
lean_inc(x_504);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 x_505 = x_502;
} else {
 lean_dec_ref(x_502);
 x_505 = lean_box(0);
}
x_506 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_504);
x_507 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_491, x_506);
lean_dec(x_506);
lean_dec(x_491);
if (lean_obj_tag(x_507) == 1)
{
lean_object* x_508; lean_object* x_509; uint8_t x_510; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 x_509 = x_507;
} else {
 lean_dec_ref(x_507);
 x_509 = lean_box(0);
}
x_510 = lean_ctor_get_uint8(x_508, sizeof(void*)*1);
if (x_510 == 0)
{
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_511; uint8_t x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; 
lean_dec(x_505);
lean_dec(x_500);
lean_dec(x_496);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_511 = lean_ctor_get(x_508, 0);
lean_inc_ref(x_511);
x_512 = lean_ctor_get_uint8(x_508, sizeof(void*)*1 + 1);
lean_dec(x_508);
x_513 = lean_ctor_get(x_504, 0);
lean_inc_ref(x_513);
x_514 = lean_ctor_get(x_504, 1);
lean_inc_ref(x_514);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_515 = x_504;
} else {
 lean_dec_ref(x_504);
 x_515 = lean_box(0);
}
x_528 = lean_ctor_get(x_513, 3);
lean_inc(x_528);
lean_dec_ref(x_513);
x_529 = lean_unsigned_to_nat(0u);
x_530 = lean_array_get_size(x_514);
x_531 = lean_nat_dec_le(x_528, x_529);
if (x_531 == 0)
{
lean_object* x_532; 
if (lean_is_scalar(x_515)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_515;
}
lean_ctor_set(x_532, 0, x_528);
lean_ctor_set(x_532, 1, x_530);
x_516 = x_532;
goto block_527;
}
else
{
lean_object* x_533; 
lean_dec(x_528);
if (lean_is_scalar(x_515)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_515;
}
lean_ctor_set(x_533, 0, x_529);
lean_ctor_set(x_533, 1, x_530);
x_516 = x_533;
goto block_527;
}
block_527:
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_517 = lean_ctor_get(x_511, 0);
lean_inc(x_517);
lean_dec_ref(x_511);
x_518 = lean_ctor_get(x_516, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_516, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_520 = x_516;
} else {
 lean_dec_ref(x_516);
 x_520 = lean_box(0);
}
x_521 = l_Array_toSubarray___redArg(x_514, x_518, x_519);
x_522 = l_Subarray_copy___redArg(x_521);
x_523 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_495, x_522, x_512);
lean_dec_ref(x_522);
if (lean_is_scalar(x_520)) {
 x_524 = lean_alloc_ctor(3, 2, 0);
} else {
 x_524 = x_520;
 lean_ctor_set_tag(x_524, 3);
}
lean_ctor_set(x_524, 0, x_517);
lean_ctor_set(x_524, 1, x_523);
if (lean_is_scalar(x_509)) {
 x_525 = lean_alloc_ctor(1, 1, 0);
} else {
 x_525 = x_509;
}
lean_ctor_set(x_525, 0, x_524);
if (lean_is_scalar(x_503)) {
 x_526 = lean_alloc_ctor(0, 1, 0);
} else {
 x_526 = x_503;
}
lean_ctor_set(x_526, 0, x_525);
return x_526;
}
}
else
{
lean_object* x_534; uint8_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; 
x_534 = lean_ctor_get(x_508, 0);
lean_inc_ref(x_534);
x_535 = lean_ctor_get_uint8(x_508, sizeof(void*)*1 + 1);
lean_dec(x_508);
x_536 = lean_ctor_get(x_504, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 x_537 = x_504;
} else {
 lean_dec_ref(x_504);
 x_537 = lean_box(0);
}
x_538 = lean_unsigned_to_nat(0u);
x_539 = lean_nat_dec_eq(x_536, x_538);
if (x_539 == 1)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_505);
lean_dec(x_500);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_540 = lean_ctor_get(x_534, 0);
lean_inc(x_540);
lean_dec_ref(x_534);
x_541 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_542 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_495, x_541, x_535);
if (lean_is_scalar(x_496)) {
 x_543 = lean_alloc_ctor(3, 2, 0);
} else {
 x_543 = x_496;
 lean_ctor_set_tag(x_543, 3);
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_542);
if (lean_is_scalar(x_509)) {
 x_544 = lean_alloc_ctor(1, 1, 0);
} else {
 x_544 = x_509;
}
lean_ctor_set(x_544, 0, x_543);
if (lean_is_scalar(x_503)) {
 x_545 = lean_alloc_ctor(0, 1, 0);
} else {
 x_545 = x_503;
}
lean_ctor_set(x_545, 0, x_544);
return x_545;
}
else
{
uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_503);
x_546 = 0;
x_547 = lean_unsigned_to_nat(1u);
x_548 = lean_nat_sub(x_536, x_547);
lean_dec(x_536);
if (lean_is_scalar(x_537)) {
 x_549 = lean_alloc_ctor(0, 1, 0);
} else {
 x_549 = x_537;
 lean_ctor_set_tag(x_549, 0);
}
lean_ctor_set(x_549, 0, x_548);
if (lean_is_scalar(x_505)) {
 x_550 = lean_alloc_ctor(0, 1, 0);
} else {
 x_550 = x_505;
 lean_ctor_set_tag(x_550, 0);
}
lean_ctor_set(x_550, 0, x_549);
x_551 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
x_552 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_546, x_550, x_551, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 x_554 = x_552;
} else {
 lean_dec_ref(x_552);
 x_554 = lean_box(0);
}
x_555 = lean_ctor_get(x_534, 0);
lean_inc(x_555);
lean_dec_ref(x_534);
x_556 = lean_ctor_get(x_553, 0);
lean_inc(x_556);
if (lean_is_scalar(x_500)) {
 x_557 = lean_alloc_ctor(1, 1, 0);
} else {
 x_557 = x_500;
}
lean_ctor_set(x_557, 0, x_556);
x_558 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3;
x_559 = lean_array_push(x_558, x_557);
x_560 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_495, x_559, x_535);
lean_dec_ref(x_559);
if (lean_is_scalar(x_496)) {
 x_561 = lean_alloc_ctor(3, 2, 0);
} else {
 x_561 = x_496;
 lean_ctor_set_tag(x_561, 3);
}
lean_ctor_set(x_561, 0, x_555);
lean_ctor_set(x_561, 1, x_560);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_553);
lean_ctor_set(x_562, 1, x_561);
if (lean_is_scalar(x_509)) {
 x_563 = lean_alloc_ctor(1, 1, 0);
} else {
 x_563 = x_509;
}
lean_ctor_set(x_563, 0, x_562);
if (lean_is_scalar(x_554)) {
 x_564 = lean_alloc_ctor(0, 1, 0);
} else {
 x_564 = x_554;
}
lean_ctor_set(x_564, 0, x_563);
return x_564;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec_ref(x_534);
lean_dec(x_509);
lean_dec(x_500);
lean_dec(x_496);
lean_dec(x_495);
lean_dec_ref(x_2);
x_565 = lean_ctor_get(x_552, 0);
lean_inc(x_565);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 x_566 = x_552;
} else {
 lean_dec_ref(x_552);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(1, 1, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_565);
return x_567;
}
}
}
}
else
{
lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_500);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_568 = lean_ctor_get(x_508, 0);
lean_inc_ref(x_568);
x_569 = lean_ctor_get_uint8(x_508, sizeof(void*)*1 + 1);
lean_dec(x_508);
x_570 = lean_ctor_get(x_568, 0);
lean_inc(x_570);
lean_dec_ref(x_568);
x_571 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
x_572 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(x_2, x_495, x_571, x_569);
if (lean_is_scalar(x_496)) {
 x_573 = lean_alloc_ctor(3, 2, 0);
} else {
 x_573 = x_496;
 lean_ctor_set_tag(x_573, 3);
}
lean_ctor_set(x_573, 0, x_570);
lean_ctor_set(x_573, 1, x_572);
if (lean_is_scalar(x_509)) {
 x_574 = lean_alloc_ctor(1, 1, 0);
} else {
 x_574 = x_509;
}
lean_ctor_set(x_574, 0, x_573);
if (lean_is_scalar(x_503)) {
 x_575 = lean_alloc_ctor(0, 1, 0);
} else {
 x_575 = x_503;
}
lean_ctor_set(x_575, 0, x_574);
return x_575;
}
}
else
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_507);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_500);
lean_dec(x_496);
lean_dec(x_495);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_576 = lean_box(0);
if (lean_is_scalar(x_503)) {
 x_577 = lean_alloc_ctor(0, 1, 0);
} else {
 x_577 = x_503;
}
lean_ctor_set(x_577, 0, x_576);
return x_577;
}
}
else
{
lean_object* x_578; lean_object* x_579; 
lean_dec(x_502);
lean_dec(x_500);
lean_dec(x_496);
lean_dec(x_495);
lean_dec(x_491);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_578 = lean_box(0);
if (lean_is_scalar(x_503)) {
 x_579 = lean_alloc_ctor(0, 1, 0);
} else {
 x_579 = x_503;
}
lean_ctor_set(x_579, 0, x_578);
return x_579;
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_500);
lean_dec(x_496);
lean_dec(x_495);
lean_dec(x_491);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_580 = lean_ctor_get(x_501, 0);
lean_inc(x_580);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 x_581 = x_501;
} else {
 lean_dec_ref(x_501);
 x_581 = lean_box(0);
}
if (lean_is_scalar(x_581)) {
 x_582 = lean_alloc_ctor(1, 1, 0);
} else {
 x_582 = x_581;
}
lean_ctor_set(x_582, 0, x_580);
return x_582;
}
}
else
{
lean_object* x_583; lean_object* x_584; 
lean_dec(x_498);
lean_dec(x_496);
lean_dec(x_495);
lean_dec(x_491);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_583 = lean_box(0);
if (lean_is_scalar(x_494)) {
 x_584 = lean_alloc_ctor(0, 1, 0);
} else {
 x_584 = x_494;
 lean_ctor_set_tag(x_584, 0);
}
lean_ctor_set(x_584, 0, x_583);
return x_584;
}
}
else
{
lean_object* x_585; lean_object* x_586; 
lean_dec(x_492);
lean_dec(x_491);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_585 = lean_box(0);
x_586 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_586, 0, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_587 = lean_box(0);
x_588 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_588, 0, x_587);
return x_588;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 3);
x_6 = lean_ctor_get(x_3, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(x_1, x_2, x_5);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_7);
x_8 = l_Lean_NameSet_contains(x_1, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
x_2 = x_10;
x_3 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 4);
lean_inc(x_13);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
x_14 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(x_1, x_2, x_3, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_6 = x_16;
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_NameSet_contains(x_1, x_11);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_14);
lean_inc_ref(x_2);
x_19 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_11, x_2, x_17);
x_3 = x_19;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_11);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec_ref(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_6 = x_22;
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_3 = x_23;
x_4 = x_13;
goto _start;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0;
x_2 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_8, x_7);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_28 = x_9;
} else {
 lean_dec_ref(x_9);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
x_32 = 0;
x_33 = lean_array_uget(x_6, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_36);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc_ref(x_35);
lean_inc(x_34);
lean_inc(x_1);
x_37 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_34, x_35, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_39 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_36, x_10, x_11, x_38, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
x_43 = l_Lean_NameSet_contains(x_42, x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_35);
lean_dec(x_34);
x_44 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_33, x_40);
x_45 = lean_array_push(x_27, x_44);
if (lean_is_scalar(x_31)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_31;
}
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
if (lean_is_scalar(x_28)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_28;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_18 = x_47;
x_19 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_40);
lean_inc_ref(x_35);
lean_inc_ref(x_3);
x_49 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(x_3, x_4, x_41, x_35, x_40, x_48, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 1);
x_53 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_40, x_14);
lean_dec(x_40);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_53);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_inc_ref(x_51);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_51);
x_56 = lean_array_push(x_29, x_55);
x_57 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_34, x_50, x_30);
lean_inc(x_41);
lean_inc_ref(x_4);
x_58 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(x_4, x_41, x_35, x_52);
x_59 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_33, x_59);
x_61 = lean_array_push(x_27, x_60);
if (lean_is_scalar(x_31)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_31;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
if (lean_is_scalar(x_28)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_28;
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_18 = x_63;
x_19 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_64; 
lean_dec(x_50);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_53);
if (x_64 == 0)
{
return x_53;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_40);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_49);
if (x_67 == 0)
{
return x_49;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_49, 0);
lean_inc(x_68);
lean_dec(x_49);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec_ref(x_35);
lean_dec_ref(x_33);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_39);
if (x_70 == 0)
{
return x_39;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_39, 0);
lean_inc(x_71);
lean_dec(x_39);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_37);
if (x_73 == 0)
{
return x_37;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_37, 0);
lean_inc(x_74);
lean_dec(x_37);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_76);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_77 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_76, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_100; lean_object* x_101; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
x_100 = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(x_5);
x_150 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
x_151 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(x_100, x_150, x_85);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_101 = x_152;
goto block_149;
block_83:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_33, x_78);
x_80 = lean_array_push(x_27, x_79);
if (lean_is_scalar(x_31)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_31;
}
lean_ctor_set(x_81, 0, x_29);
lean_ctor_set(x_81, 1, x_30);
if (lean_is_scalar(x_28)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_28;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_18 = x_82;
x_19 = lean_box(0);
goto block_23;
}
block_99:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_88, 0);
lean_inc(x_92);
lean_dec_ref(x_88);
lean_inc(x_84);
lean_inc_ref(x_4);
x_93 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(x_4, x_84, x_86, x_87);
x_94 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_33, x_94);
x_96 = lean_array_push(x_27, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_18 = x_98;
x_19 = lean_box(0);
goto block_23;
}
block_149:
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_dec(x_100);
goto block_83;
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_unbox(x_104);
if (x_105 == 0)
{
lean_free_object(x_102);
lean_dec(x_104);
lean_dec(x_100);
goto block_83;
}
else
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
lean_dec(x_31);
lean_dec(x_28);
x_106 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1;
x_107 = lean_unbox(x_104);
lean_dec(x_104);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_78);
lean_inc_ref(x_3);
x_108 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(x_3, x_4, x_84, x_106, x_78, x_107, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc_ref(x_110);
x_111 = lean_ctor_get_uint8(x_109, sizeof(void*)*1 + 1);
x_112 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_78, x_14);
lean_dec(x_78);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
lean_dec_ref(x_112);
lean_inc(x_85);
x_113 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(x_100, x_109, x_30, x_85);
lean_dec(x_100);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
lean_inc_ref(x_110);
lean_ctor_set_tag(x_102, 2);
lean_ctor_set(x_102, 0, x_110);
x_115 = lean_array_push(x_29, x_102);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_86 = x_106;
x_87 = x_111;
x_88 = x_110;
x_89 = x_115;
x_90 = x_116;
x_91 = lean_box(0);
goto block_99;
}
else
{
uint8_t x_117; 
lean_dec_ref(x_110);
lean_free_object(x_102);
lean_dec_ref(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_113);
if (x_117 == 0)
{
return x_113;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
lean_dec(x_113);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec_ref(x_110);
lean_dec(x_109);
lean_free_object(x_102);
lean_dec(x_100);
lean_dec_ref(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_112);
if (x_120 == 0)
{
return x_112;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_112, 0);
lean_inc(x_121);
lean_dec(x_112);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_102);
lean_dec(x_100);
lean_dec(x_78);
lean_dec_ref(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_108);
if (x_123 == 0)
{
return x_108;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_108, 0);
lean_inc(x_124);
lean_dec(x_108);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_102, 0);
lean_inc(x_126);
lean_dec(x_102);
x_127 = lean_unbox(x_126);
if (x_127 == 0)
{
lean_dec(x_126);
lean_dec(x_100);
goto block_83;
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; 
lean_dec(x_31);
lean_dec(x_28);
x_128 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1;
x_129 = lean_unbox(x_126);
lean_dec(x_126);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_78);
lean_inc_ref(x_3);
x_130 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(x_3, x_4, x_84, x_128, x_78, x_129, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_132);
x_133 = lean_ctor_get_uint8(x_131, sizeof(void*)*1 + 1);
x_134 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_78, x_14);
lean_dec(x_78);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
lean_dec_ref(x_134);
lean_inc(x_85);
x_135 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(x_100, x_131, x_30, x_85);
lean_dec(x_100);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
lean_inc_ref(x_132);
x_137 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_137, 0, x_132);
x_138 = lean_array_push(x_29, x_137);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
x_86 = x_128;
x_87 = x_133;
x_88 = x_132;
x_89 = x_138;
x_90 = x_139;
x_91 = lean_box(0);
goto block_99;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_132);
lean_dec_ref(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_141 = x_135;
} else {
 lean_dec_ref(x_135);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec(x_100);
lean_dec_ref(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_134, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_144 = x_134;
} else {
 lean_dec_ref(x_134);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_100);
lean_dec(x_78);
lean_dec_ref(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_130, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_147 = x_130;
} else {
 lean_dec_ref(x_130);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
}
}
}
}
else
{
uint8_t x_153; 
lean_dec_ref(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_77);
if (x_153 == 0)
{
return x_77;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_77, 0);
lean_inc(x_154);
lean_dec(x_77);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
}
}
block_23:
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
x_8 = x_21;
x_9 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 4);
x_15 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(x_3, x_11);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_19 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 3);
lean_inc_ref(x_25);
x_26 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1;
x_27 = lean_array_size(x_25);
x_28 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_12);
lean_inc(x_21);
lean_inc(x_24);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(x_24, x_17, x_21, x_12, x_20, x_25, x_27, x_28, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_25);
lean_dec(x_20);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_st_ref_take(x_4);
lean_inc(x_11);
x_37 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_11, x_35, x_36);
x_38 = lean_st_ref_set(x_4, x_37);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_23);
lean_ctor_set(x_40, 2, x_24);
lean_ctor_set(x_40, 3, x_32);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_Compiler_LCNF_attachCodeDecls(x_39, x_21, x_41);
lean_dec(x_21);
x_43 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_39, x_1, x_13, x_12, x_42, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_47);
lean_ctor_set(x_31, 0, x_44);
x_48 = l_Lean_Compiler_LCNF_attachCodeDecls(x_39, x_34, x_31);
lean_dec(x_34);
lean_ctor_set(x_15, 0, x_48);
lean_ctor_set(x_45, 0, x_15);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_49);
lean_ctor_set(x_31, 0, x_44);
x_50 = l_Lean_Compiler_LCNF_attachCodeDecls(x_39, x_34, x_31);
lean_dec(x_34);
lean_ctor_set(x_15, 0, x_50);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_15);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_44);
lean_free_object(x_31);
lean_dec(x_34);
lean_free_object(x_15);
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_31);
lean_dec(x_34);
lean_free_object(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
return x_43;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_31, 0);
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_31);
x_60 = lean_st_ref_take(x_4);
lean_inc(x_11);
x_61 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_11, x_59, x_60);
x_62 = lean_st_ref_set(x_4, x_61);
x_63 = 0;
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_22);
lean_ctor_set(x_64, 1, x_23);
lean_ctor_set(x_64, 2, x_24);
lean_ctor_set(x_64, 3, x_32);
x_65 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_Compiler_LCNF_attachCodeDecls(x_63, x_21, x_65);
lean_dec(x_21);
x_67 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_63, x_1, x_13, x_12, x_66, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Compiler_LCNF_attachCodeDecls(x_63, x_58, x_72);
lean_dec(x_58);
lean_ctor_set(x_15, 0, x_73);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_15);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_68);
lean_dec(x_58);
lean_free_object(x_15);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_58);
lean_free_object(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_79 = x_67;
} else {
 lean_dec_ref(x_67);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_29);
if (x_81 == 0)
{
return x_29;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_29, 0);
lean_inc(x_82);
lean_dec(x_29);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_free_object(x_15);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_15, 0);
lean_inc(x_86);
lean_dec(x_15);
x_87 = lean_ctor_get(x_86, 1);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; 
x_88 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(x_14);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_89, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 3);
lean_inc_ref(x_94);
x_95 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1;
x_96 = lean_array_size(x_94);
x_97 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_12);
lean_inc(x_90);
lean_inc(x_93);
x_98 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(x_93, x_86, x_90, x_12, x_89, x_94, x_96, x_97, x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_94);
lean_dec(x_89);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
x_105 = lean_st_ref_take(x_4);
lean_inc(x_11);
x_106 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_11, x_103, x_105);
x_107 = lean_st_ref_set(x_4, x_106);
x_108 = 0;
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_91);
lean_ctor_set(x_109, 1, x_92);
lean_ctor_set(x_109, 2, x_93);
lean_ctor_set(x_109, 3, x_101);
x_110 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = l_Lean_Compiler_LCNF_attachCodeDecls(x_108, x_90, x_110);
lean_dec(x_90);
x_112 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_108, x_1, x_13, x_12, x_111, x_7);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_117 = lean_alloc_ctor(2, 2, 0);
} else {
 x_117 = x_104;
 lean_ctor_set_tag(x_117, 2);
}
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Compiler_LCNF_attachCodeDecls(x_108, x_102, x_117);
lean_dec(x_102);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 1, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_113);
lean_dec(x_104);
lean_dec(x_102);
x_121 = lean_ctor_get(x_114, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_122 = x_114;
} else {
 lean_dec_ref(x_114);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_125 = x_112;
} else {
 lean_dec_ref(x_112);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_127 = lean_ctor_get(x_98, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_128 = x_98;
} else {
 lean_dec_ref(x_98);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_86);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; size_t x_24; size_t x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
x_24 = lean_ptr_addr(x_11);
x_25 = lean_ptr_addr(x_13);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
x_15 = x_26;
goto block_23;
}
else
{
size_t x_27; uint8_t x_28; 
x_27 = lean_ptr_addr(x_10);
x_28 = lean_usize_dec_eq(x_27, x_27);
x_15 = x_28;
goto block_23;
}
block_23:
{
if (x_15 == 0)
{
uint8_t x_16; 
lean_inc_ref(x_10);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_13);
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_13);
if (lean_is_scalar(x_14)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_14;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_13);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_14;
}
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
}
else
{
lean_dec_ref(x_1);
return x_12;
}
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_29, 2);
x_32 = lean_ctor_get(x_29, 3);
x_33 = lean_ctor_get(x_29, 4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_33);
x_34 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = 0;
lean_inc_ref(x_31);
lean_inc_ref(x_32);
lean_inc_ref(x_29);
x_37 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_36, x_29, x_32, x_31, x_35, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc_ref(x_30);
x_39 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; size_t x_51; size_t x_52; uint8_t x_53; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_51 = lean_ptr_addr(x_30);
x_52 = lean_ptr_addr(x_40);
x_53 = lean_usize_dec_eq(x_51, x_52);
if (x_53 == 0)
{
x_42 = x_53;
goto block_50;
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
x_54 = lean_ptr_addr(x_29);
x_55 = lean_ptr_addr(x_38);
x_56 = lean_usize_dec_eq(x_54, x_55);
x_42 = x_56;
goto block_50;
}
block_50:
{
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_1, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_1, 0);
lean_dec(x_45);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_38);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_1);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_40);
if (lean_is_scalar(x_41)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_41;
}
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_38);
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_1);
return x_49;
}
}
}
else
{
lean_dec(x_38);
lean_dec_ref(x_1);
return x_39;
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_57 = !lean_is_exclusive(x_37);
if (x_57 == 0)
{
return x_37;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_37, 0);
lean_inc(x_58);
lean_dec(x_37);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_34;
}
}
case 2:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_61);
lean_inc_ref(x_60);
x_62 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(x_60, x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_65; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_62);
lean_dec(x_64);
x_66 = lean_ctor_get(x_60, 2);
x_67 = lean_ctor_get(x_60, 3);
x_68 = lean_ctor_get(x_60, 4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_68);
x_69 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = 0;
lean_inc_ref(x_66);
lean_inc_ref(x_67);
lean_inc_ref(x_60);
x_72 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_71, x_60, x_67, x_66, x_70, x_6);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
lean_inc_ref(x_61);
x_74 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; size_t x_86; size_t x_87; uint8_t x_88; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_86 = lean_ptr_addr(x_61);
x_87 = lean_ptr_addr(x_75);
x_88 = lean_usize_dec_eq(x_86, x_87);
if (x_88 == 0)
{
x_77 = x_88;
goto block_85;
}
else
{
size_t x_89; size_t x_90; uint8_t x_91; 
x_89 = lean_ptr_addr(x_60);
x_90 = lean_ptr_addr(x_73);
x_91 = lean_usize_dec_eq(x_89, x_90);
x_77 = x_91;
goto block_85;
}
block_85:
{
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_1, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_1, 0);
lean_dec(x_80);
lean_ctor_set(x_1, 1, x_75);
lean_ctor_set(x_1, 0, x_73);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_1);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_1);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_75);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_75);
lean_dec(x_73);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_1);
return x_84;
}
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_1);
return x_74;
}
}
else
{
uint8_t x_92; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_92 = !lean_is_exclusive(x_72);
if (x_92 == 0)
{
return x_72;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_72, 0);
lean_inc(x_93);
lean_dec(x_72);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_69;
}
}
}
else
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_62, 0);
lean_inc(x_95);
lean_dec(x_62);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_95);
x_98 = lean_ctor_get(x_60, 2);
x_99 = lean_ctor_get(x_60, 3);
x_100 = lean_ctor_get(x_60, 4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_100);
x_101 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = 0;
lean_inc_ref(x_98);
lean_inc_ref(x_99);
lean_inc_ref(x_60);
x_104 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_103, x_60, x_99, x_98, x_102, x_6);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
lean_inc_ref(x_61);
x_106 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; size_t x_115; size_t x_116; uint8_t x_117; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_115 = lean_ptr_addr(x_61);
x_116 = lean_ptr_addr(x_107);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
x_109 = x_117;
goto block_114;
}
else
{
size_t x_118; size_t x_119; uint8_t x_120; 
x_118 = lean_ptr_addr(x_60);
x_119 = lean_ptr_addr(x_105);
x_120 = lean_usize_dec_eq(x_118, x_119);
x_109 = x_120;
goto block_114;
}
block_114:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_110 = x_1;
} else {
 lean_dec_ref(x_1);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(2, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_107);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; 
lean_dec(x_107);
lean_dec(x_105);
if (lean_is_scalar(x_108)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_108;
}
lean_ctor_set(x_113, 0, x_1);
return x_113;
}
}
}
else
{
lean_dec(x_105);
lean_dec_ref(x_1);
return x_106;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_121 = lean_ctor_get(x_104, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_122 = x_104;
} else {
 lean_dec_ref(x_104);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
else
{
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_101;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec_ref(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_124 = !lean_is_exclusive(x_62);
if (x_124 == 0)
{
return x_62;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_62, 0);
lean_inc(x_125);
lean_dec(x_62);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
case 3:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_1, 0);
x_128 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_128);
x_129 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(x_127, x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
if (lean_obj_tag(x_131) == 1)
{
lean_object* x_132; 
lean_dec_ref(x_1);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
lean_ctor_set(x_129, 0, x_132);
return x_129;
}
else
{
lean_dec(x_131);
lean_ctor_set(x_129, 0, x_1);
return x_129;
}
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
lean_dec(x_129);
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_1);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_1);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec_ref(x_1);
x_137 = !lean_is_exclusive(x_129);
if (x_137 == 0)
{
return x_129;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_129, 0);
lean_inc(x_138);
lean_dec(x_129);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
case 4:
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_140);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
x_144 = lean_ctor_get(x_140, 2);
x_145 = lean_ctor_get(x_140, 3);
x_146 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_145);
lean_inc(x_144);
x_147 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(x_144, x_146, x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; size_t x_150; size_t x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ptr_addr(x_145);
lean_dec_ref(x_145);
x_151 = lean_ptr_addr(x_149);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_1);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_1, 0);
lean_dec(x_154);
lean_ctor_set(x_140, 3, x_149);
lean_ctor_set(x_147, 0, x_1);
return x_147;
}
else
{
lean_object* x_155; 
lean_dec(x_1);
lean_ctor_set(x_140, 3, x_149);
x_155 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_155, 0, x_140);
lean_ctor_set(x_147, 0, x_155);
return x_147;
}
}
else
{
lean_dec(x_149);
lean_free_object(x_140);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_ctor_set(x_147, 0, x_1);
return x_147;
}
}
else
{
lean_object* x_156; size_t x_157; size_t x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_147, 0);
lean_inc(x_156);
lean_dec(x_147);
x_157 = lean_ptr_addr(x_145);
lean_dec_ref(x_145);
x_158 = lean_ptr_addr(x_156);
x_159 = lean_usize_dec_eq(x_157, x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_160 = x_1;
} else {
 lean_dec_ref(x_1);
 x_160 = lean_box(0);
}
lean_ctor_set(x_140, 3, x_156);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(4, 1, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_140);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
else
{
lean_object* x_163; 
lean_dec(x_156);
lean_free_object(x_140);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_1);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_free_object(x_140);
lean_dec_ref(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_1);
x_164 = !lean_is_exclusive(x_147);
if (x_164 == 0)
{
return x_147;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_147, 0);
lean_inc(x_165);
lean_dec(x_147);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_140, 0);
x_168 = lean_ctor_get(x_140, 1);
x_169 = lean_ctor_get(x_140, 2);
x_170 = lean_ctor_get(x_140, 3);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_140);
x_171 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_170);
lean_inc(x_169);
x_172 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(x_169, x_171, x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; size_t x_175; size_t x_176; uint8_t x_177; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = lean_ptr_addr(x_170);
lean_dec_ref(x_170);
x_176 = lean_ptr_addr(x_173);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_178 = x_1;
} else {
 lean_dec_ref(x_1);
 x_178 = lean_box(0);
}
x_179 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_179, 0, x_167);
lean_ctor_set(x_179, 1, x_168);
lean_ctor_set(x_179, 2, x_169);
lean_ctor_set(x_179, 3, x_173);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(4, 1, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
if (lean_is_scalar(x_174)) {
 x_181 = lean_alloc_ctor(0, 1, 0);
} else {
 x_181 = x_174;
}
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
else
{
lean_object* x_182; 
lean_dec(x_173);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec(x_167);
if (lean_is_scalar(x_174)) {
 x_182 = lean_alloc_ctor(0, 1, 0);
} else {
 x_182 = x_174;
}
lean_ctor_set(x_182, 0, x_1);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec_ref(x_170);
lean_dec(x_169);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_172, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_184 = x_172;
} else {
 lean_dec_ref(x_172);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
return x_185;
}
}
}
default: 
{
lean_object* x_186; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_1);
return x_186;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget_borrowed(x_3, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
x_31 = lean_ctor_get(x_15, 2);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_30);
lean_inc(x_29);
lean_inc(x_1);
x_32 = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_29, x_30, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_31);
x_34 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_31, x_4, x_5, x_33, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc_ref(x_15);
x_36 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_15, x_35);
x_16 = x_36;
x_17 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_43);
x_44 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc_ref(x_15);
x_46 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_15, x_45);
x_16 = x_46;
x_17 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
block_28:
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_15);
x_19 = lean_ptr_addr(x_16);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_array_fset(x_3, x_2, x_16);
lean_dec(x_2);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 5);
x_10 = lean_st_ref_get(x_6);
x_11 = lean_st_ref_get(x_4);
x_12 = l_Lean_Compiler_LCNF_getPurity___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2;
x_20 = lean_st_ref_take(x_6);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; double x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_unbox(x_14);
lean_dec(x_14);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17, x_25);
lean_dec_ref(x_17);
lean_inc_ref(x_8);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_8);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_27);
x_28 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3;
x_29 = 0;
x_30 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4));
x_31 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_float(x_31, sizeof(void*)*2, x_28);
lean_ctor_set_float(x_31, sizeof(void*)*2 + 8, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 16, x_29);
x_32 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5;
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_11);
lean_ctor_set(x_33, 2, x_32);
lean_inc(x_9);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_PersistentArray_push___redArg(x_24, x_34);
lean_ctor_set(x_22, 0, x_35);
x_36 = lean_st_ref_set(x_6, x_20);
x_37 = lean_box(0);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
else
{
uint64_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_unbox(x_14);
lean_dec(x_14);
x_41 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17, x_40);
lean_dec_ref(x_17);
lean_inc_ref(x_8);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_8);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_42);
x_43 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3;
x_44 = 0;
x_45 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4));
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_9);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_PersistentArray_push___redArg(x_39, x_49);
x_51 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint64(x_51, sizeof(void*)*1, x_38);
lean_ctor_set(x_20, 4, x_51);
x_52 = lean_st_ref_set(x_6, x_20);
x_53 = lean_box(0);
lean_ctor_set(x_12, 0, x_53);
return x_12;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; double x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_54 = lean_ctor_get(x_20, 4);
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
x_57 = lean_ctor_get(x_20, 2);
x_58 = lean_ctor_get(x_20, 3);
x_59 = lean_ctor_get(x_20, 5);
x_60 = lean_ctor_get(x_20, 6);
x_61 = lean_ctor_get(x_20, 7);
x_62 = lean_ctor_get(x_20, 8);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_54);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_63 = lean_ctor_get_uint64(x_54, sizeof(void*)*1);
x_64 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
 x_65 = lean_box(0);
}
x_66 = lean_unbox(x_14);
lean_dec(x_14);
x_67 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17, x_66);
lean_dec_ref(x_17);
lean_inc_ref(x_8);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_15);
lean_ctor_set(x_68, 1, x_19);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_8);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_68);
x_69 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3;
x_70 = 0;
x_71 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4));
x_72 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_float(x_72, sizeof(void*)*2, x_69);
lean_ctor_set_float(x_72, sizeof(void*)*2 + 8, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 16, x_70);
x_73 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5;
x_74 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_11);
lean_ctor_set(x_74, 2, x_73);
lean_inc(x_9);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_9);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_PersistentArray_push___redArg(x_64, x_75);
if (lean_is_scalar(x_65)) {
 x_77 = lean_alloc_ctor(0, 1, 8);
} else {
 x_77 = x_65;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set_uint64(x_77, sizeof(void*)*1, x_63);
x_78 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_78, 0, x_55);
lean_ctor_set(x_78, 1, x_56);
lean_ctor_set(x_78, 2, x_57);
lean_ctor_set(x_78, 3, x_58);
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 5, x_59);
lean_ctor_set(x_78, 6, x_60);
lean_ctor_set(x_78, 7, x_61);
lean_ctor_set(x_78, 8, x_62);
x_79 = lean_st_ref_set(x_6, x_78);
x_80 = lean_box(0);
lean_ctor_set(x_12, 0, x_80);
return x_12;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; double x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_81 = lean_ctor_get(x_11, 0);
lean_inc(x_81);
lean_dec(x_11);
x_82 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2;
x_83 = lean_st_ref_take(x_6);
x_84 = lean_ctor_get(x_83, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_83, 3);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_83, 5);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_83, 6);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_83, 7);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_83, 8);
lean_inc_ref(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 lean_ctor_release(x_83, 6);
 lean_ctor_release(x_83, 7);
 lean_ctor_release(x_83, 8);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get_uint64(x_84, sizeof(void*)*1);
x_95 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
 x_96 = lean_box(0);
}
x_97 = lean_unbox(x_14);
lean_dec(x_14);
x_98 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_81, x_97);
lean_dec_ref(x_81);
lean_inc_ref(x_8);
x_99 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_99, 0, x_15);
lean_ctor_set(x_99, 1, x_82);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_8);
x_100 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_2);
x_101 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3;
x_102 = 0;
x_103 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4));
x_104 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_float(x_104, sizeof(void*)*2, x_101);
lean_ctor_set_float(x_104, sizeof(void*)*2 + 8, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*2 + 16, x_102);
x_105 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5;
x_106 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_105);
lean_inc(x_9);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_9);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_PersistentArray_push___redArg(x_95, x_107);
if (lean_is_scalar(x_96)) {
 x_109 = lean_alloc_ctor(0, 1, 8);
} else {
 x_109 = x_96;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set_uint64(x_109, sizeof(void*)*1, x_94);
if (lean_is_scalar(x_93)) {
 x_110 = lean_alloc_ctor(0, 9, 0);
} else {
 x_110 = x_93;
}
lean_ctor_set(x_110, 0, x_85);
lean_ctor_set(x_110, 1, x_86);
lean_ctor_set(x_110, 2, x_87);
lean_ctor_set(x_110, 3, x_88);
lean_ctor_set(x_110, 4, x_109);
lean_ctor_set(x_110, 5, x_89);
lean_ctor_set(x_110, 6, x_90);
lean_ctor_set(x_110, 7, x_91);
lean_ctor_set(x_110, 8, x_92);
x_111 = lean_st_ref_set(x_6, x_110);
x_112 = lean_box(0);
lean_ctor_set(x_12, 0, x_112);
return x_12;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; double x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_113 = lean_ctor_get(x_12, 0);
lean_inc(x_113);
lean_dec(x_12);
x_114 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_114);
lean_dec(x_10);
x_115 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_115);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_116 = x_11;
} else {
 lean_dec_ref(x_11);
 x_116 = lean_box(0);
}
x_117 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2;
x_118 = lean_st_ref_take(x_6);
x_119 = lean_ctor_get(x_118, 4);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 2);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_118, 5);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_118, 6);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_118, 7);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_118, 8);
lean_inc_ref(x_127);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 lean_ctor_release(x_118, 6);
 lean_ctor_release(x_118, 7);
 lean_ctor_release(x_118, 8);
 x_128 = x_118;
} else {
 lean_dec_ref(x_118);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get_uint64(x_119, sizeof(void*)*1);
x_130 = lean_ctor_get(x_119, 0);
lean_inc_ref(x_130);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_131 = x_119;
} else {
 lean_dec_ref(x_119);
 x_131 = lean_box(0);
}
x_132 = lean_unbox(x_113);
lean_dec(x_113);
x_133 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_115, x_132);
lean_dec_ref(x_115);
lean_inc_ref(x_8);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_114);
lean_ctor_set(x_134, 1, x_117);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_8);
if (lean_is_scalar(x_116)) {
 x_135 = lean_alloc_ctor(3, 2, 0);
} else {
 x_135 = x_116;
 lean_ctor_set_tag(x_135, 3);
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_2);
x_136 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3;
x_137 = 0;
x_138 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4));
x_139 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_float(x_139, sizeof(void*)*2, x_136);
lean_ctor_set_float(x_139, sizeof(void*)*2 + 8, x_136);
lean_ctor_set_uint8(x_139, sizeof(void*)*2 + 16, x_137);
x_140 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5;
x_141 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_135);
lean_ctor_set(x_141, 2, x_140);
lean_inc(x_9);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_9);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_PersistentArray_push___redArg(x_130, x_142);
if (lean_is_scalar(x_131)) {
 x_144 = lean_alloc_ctor(0, 1, 8);
} else {
 x_144 = x_131;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set_uint64(x_144, sizeof(void*)*1, x_129);
if (lean_is_scalar(x_128)) {
 x_145 = lean_alloc_ctor(0, 9, 0);
} else {
 x_145 = x_128;
}
lean_ctor_set(x_145, 0, x_120);
lean_ctor_set(x_145, 1, x_121);
lean_ctor_set(x_145, 2, x_122);
lean_ctor_set(x_145, 3, x_123);
lean_ctor_set(x_145, 4, x_144);
lean_ctor_set(x_145, 5, x_124);
lean_ctor_set(x_145, 6, x_125);
lean_ctor_set(x_145, 7, x_126);
lean_ctor_set(x_145, 8, x_127);
x_146 = lean_st_ref_set(x_6, x_145);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
else
{
uint8_t x_149; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_12);
if (x_149 == 0)
{
return x_12;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_12, 0);
lean_inc(x_150);
lean_dec(x_12);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofName(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofName(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(x_1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = l_Lean_mkFVar(x_11);
x_17 = l_Lean_MessageData_ofExpr(x_16);
x_18 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1;
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_18);
lean_ctor_set(x_6, 0, x_17);
x_19 = lean_box(0);
x_20 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(x_19, x_14);
lean_dec(x_14);
x_21 = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(x_20, x_19);
x_22 = l_Lean_MessageData_ofList(x_21);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_22);
lean_ctor_set(x_5, 0, x_6);
x_23 = l_Lean_indentD(x_5);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = l_Lean_mkFVar(x_11);
x_27 = l_Lean_MessageData_ofExpr(x_26);
x_28 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(x_30, x_25);
lean_dec(x_25);
x_32 = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(x_31, x_30);
x_33 = l_Lean_MessageData_ofList(x_32);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_29);
x_34 = l_Lean_indentD(x_5);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_38 = x_6;
} else {
 lean_dec_ref(x_6);
 x_38 = lean_box(0);
}
x_39 = l_Lean_mkFVar(x_36);
x_40 = l_Lean_MessageData_ofExpr(x_39);
x_41 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1;
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(7, 2, 0);
} else {
 x_42 = x_38;
 lean_ctor_set_tag(x_42, 7);
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(x_43, x_37);
lean_dec(x_37);
x_45 = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(x_44, x_43);
x_46 = l_Lean_MessageData_ofList(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_indentD(x_47);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_48);
lean_ctor_set(x_1, 0, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_5, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_52 = x_5;
} else {
 lean_dec_ref(x_5);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_54 = x_6;
} else {
 lean_dec_ref(x_6);
 x_54 = lean_box(0);
}
x_55 = l_Lean_mkFVar(x_51);
x_56 = l_Lean_MessageData_ofExpr(x_55);
x_57 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1;
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(7, 2, 0);
} else {
 x_58 = x_54;
 lean_ctor_set_tag(x_58, 7);
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_box(0);
x_60 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(x_59, x_53);
lean_dec(x_53);
x_61 = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(x_60, x_59);
x_62 = l_Lean_MessageData_ofList(x_61);
if (lean_is_scalar(x_52)) {
 x_63 = lean_alloc_ctor(7, 2, 0);
} else {
 x_63 = x_52;
 lean_ctor_set_tag(x_63, 7);
}
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_indentD(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_64);
x_1 = x_50;
x_2 = x_65;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_27; 
x_9 = lean_ctor_get(x_7, 0);
x_27 = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(x_9);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_7, 0, x_28);
return x_7;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_7);
x_29 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
x_30 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(x_29, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
x_10 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6;
x_34 = lean_box(0);
x_35 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(x_34, x_9);
x_36 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(x_35, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(x_29, x_37, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_10 = lean_box(0);
goto block_26;
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
block_26:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(1);
x_12 = lean_st_mk_ref(x_11);
x_13 = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2;
x_14 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_1, x_9, x_12, x_13, x_2, x_3, x_4, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_12);
lean_dec(x_12);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_st_ref_get(x_12);
lean_dec(x_12);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_57; 
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
lean_dec(x_7);
x_57 = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(x_42);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
x_61 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(x_60, x_4);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
x_43 = lean_box(0);
goto block_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6;
x_65 = lean_box(0);
x_66 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(x_65, x_42);
x_67 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(x_66, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(x_60, x_68, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_43 = lean_box(0);
goto block_56;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
}
block_56:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_box(1);
x_45 = lean_st_mk_ref(x_44);
x_46 = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2;
x_47 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(x_1, x_42, x_45, x_46, x_2, x_3, x_4, x_5);
lean_dec(x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_st_ref_get(x_45);
lean_dec(x_45);
lean_dec(x_50);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_48);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_45);
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_7);
if (x_73 == 0)
{
return x_7;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_7, 0);
lean_inc(x_74);
lean_dec(x_7);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(x_2, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DiscrM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0);
l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default);
l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo);
l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0 = _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0);
l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1 = _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1);
l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2 = _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2();
lean_mark_persistent(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2);
l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0 = _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1);
l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0 = _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0);
l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1 = _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1();
lean_mark_persistent(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__3);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0);
l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3();
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5);
l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1);
l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6);
if (builtin) {res = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
