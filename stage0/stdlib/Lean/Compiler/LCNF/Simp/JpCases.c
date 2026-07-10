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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0;
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Compiler.LCNF.Simp.JpCases"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Compiler.LCNF.Simp.JpCases.0.Lean.Compiler.LCNF.Simp.extractJpCases.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0;
static const lean_array_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "jpCases"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 92, 220, 8, 204, 108, 198, 7)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "candidates"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0(lean_object* v_cases_1_, lean_object* v_as_2_, lean_object* v_j_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_array_get_size(v_as_2_);
v___x_5_ = lean_nat_dec_lt(v_j_3_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
lean_dec(v_j_3_);
v___x_6_ = lean_box(0);
return v___x_6_;
}
else
{
lean_object* v_discr_7_; lean_object* v___x_8_; lean_object* v_fvarId_9_; uint8_t v___x_10_; 
v_discr_7_ = lean_ctor_get(v_cases_1_, 2);
v___x_8_ = lean_array_fget_borrowed(v_as_2_, v_j_3_);
v_fvarId_9_ = lean_ctor_get(v___x_8_, 0);
v___x_10_ = l_Lean_instBEqFVarId_beq(v_discr_7_, v_fvarId_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_j_3_, v___x_11_);
lean_dec(v_j_3_);
v_j_3_ = v___x_12_;
goto _start;
}
else
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v_j_3_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0___boxed(lean_object* v_cases_15_, lean_object* v_as_16_, lean_object* v_j_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0(v_cases_15_, v_as_16_, v_j_17_);
lean_dec_ref(v_as_16_);
lean_dec_ref(v_cases_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(lean_object* v_decl_19_, lean_object* v_small_20_, lean_object* v_code_21_, lean_object* v_prefixSize_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_lt(v_small_20_, v_prefixSize_22_);
if (v___x_23_ == 0)
{
switch(lean_obj_tag(v_code_21_))
{
case 0:
{
lean_object* v_k_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_k_24_ = lean_ctor_get(v_code_21_, 1);
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = lean_nat_add(v_prefixSize_22_, v___x_25_);
lean_dec(v_prefixSize_22_);
v_code_21_ = v_k_24_;
v_prefixSize_22_ = v___x_26_;
goto _start;
}
case 4:
{
lean_object* v_cases_28_; lean_object* v_params_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
lean_dec(v_prefixSize_22_);
v_cases_28_ = lean_ctor_get(v_code_21_, 0);
v_params_29_ = lean_ctor_get(v_decl_19_, 2);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0(v_cases_28_, v_params_29_, v___x_30_);
return v___x_31_;
}
default: 
{
lean_object* v___x_32_; 
lean_dec(v_prefixSize_22_);
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
}
else
{
lean_object* v___x_33_; 
lean_dec(v_prefixSize_22_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___boxed(lean_object* v_decl_34_, lean_object* v_small_35_, lean_object* v_code_36_, lean_object* v_prefixSize_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(v_decl_34_, v_small_35_, v_code_36_, v_prefixSize_37_);
lean_dec_ref(v_code_36_);
lean_dec(v_small_35_);
lean_dec_ref(v_decl_34_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(lean_object* v_decl_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_params_42_; lean_object* v_value_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_params_42_ = lean_ctor_get(v_decl_39_, 2);
v_value_43_ = lean_ctor_get(v_decl_39_, 4);
v___x_44_ = lean_array_get_size(v_params_42_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_nat_dec_eq(v___x_44_, v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_40_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_57_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_57_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v_smallThreshold_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v_smallThreshold_52_ = lean_ctor_get(v_a_48_, 0);
lean_inc(v_smallThreshold_52_);
lean_dec(v_a_48_);
v___x_53_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(v_decl_39_, v_smallThreshold_52_, v_value_43_, v___x_45_);
lean_dec(v_smallThreshold_52_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_53_);
v___x_55_ = v___x_50_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_47_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_47_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
else
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_box(0);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg___boxed(lean_object* v_decl_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_68_, v_a_69_);
lean_dec_ref(v_a_69_);
lean_dec_ref(v_decl_68_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(lean_object* v_decl_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_72_, v_a_73_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___boxed(lean_object* v_decl_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(v_decl_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec_ref(v_decl_79_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = l_Lean_NameSet_empty;
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0, &l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo(void){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default;
return v___x_90_;
}
}
static uint8_t _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1(void){
_start:
{
uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 0;
v___x_95_ = lean_bool_not(v___x_94_);
return v___x_95_;
}
}
static uint8_t _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2(void){
_start:
{
uint8_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 1;
v___x_97_ = lean_bool_not(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object* v_init_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v_v_100_; lean_object* v_l_101_; lean_object* v_r_102_; lean_object* v___x_103_; 
v_v_100_ = lean_ctor_get(v_x_99_, 2);
lean_inc(v_v_100_);
v_l_101_ = lean_ctor_get(v_x_99_, 3);
lean_inc(v_l_101_);
v_r_102_ = lean_ctor_get(v_x_99_, 4);
lean_inc(v_r_102_);
lean_dec_ref_known(v_x_99_, 5);
v___x_103_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_98_, v_l_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_dec(v_r_102_);
lean_dec(v_v_100_);
return v___x_103_;
}
else
{
lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_128_; 
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_103_, 0);
lean_dec(v_unused_129_);
v___x_105_ = v___x_103_;
v_isShared_106_ = v_isSharedCheck_128_;
goto v_resetjp_104_;
}
else
{
lean_dec(v___x_103_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_128_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v_ctorNames_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_126_; 
v_ctorNames_107_ = lean_ctor_get(v_v_100_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_v_100_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v_v_100_, 0);
lean_dec(v_unused_127_);
v___x_109_ = v_v_100_;
v_isShared_110_ = v_isSharedCheck_126_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_ctorNames_107_);
lean_dec(v_v_100_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_126_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___y_114_; 
v___x_111_ = lean_box(0);
v___x_112_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0));
if (lean_obj_tag(v_ctorNames_107_) == 0)
{
uint8_t v___x_124_; 
lean_dec_ref_known(v_ctorNames_107_, 5);
v___x_124_ = lean_uint8_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1);
v___y_114_ = v___x_124_;
goto v___jp_113_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_uint8_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2);
v___y_114_ = v___x_125_;
goto v___jp_113_;
}
v___jp_113_:
{
if (v___y_114_ == 0)
{
lean_del_object(v___x_109_);
lean_del_object(v___x_105_);
v_init_98_ = v___x_112_;
v_x_99_ = v_r_102_;
goto _start;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
lean_dec(v_r_102_);
v___x_116_ = lean_box(v___y_114_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_111_);
lean_ctor_set(v___x_109_, 0, v___x_117_);
v___x_119_ = v___x_109_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_111_);
v___x_119_ = v_reuseFailAlloc_123_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 0);
lean_ctor_set(v___x_105_, 0, v___x_119_);
v___x_121_ = v___x_105_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
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
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v_init_98_);
return v___x_130_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(lean_object* v_info_131_){
_start:
{
lean_object* v___y_133_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_a_140_; 
v___x_138_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0));
v___x_139_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v___x_138_, v_info_131_);
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref(v___x_139_);
v___y_133_ = v_a_140_;
goto v___jp_132_;
v___jp_132_:
{
lean_object* v_fst_134_; 
v_fst_134_ = lean_ctor_get(v___y_133_, 0);
lean_inc(v_fst_134_);
lean_dec_ref(v___y_133_);
if (lean_obj_tag(v_fst_134_) == 0)
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
else
{
lean_object* v_val_136_; uint8_t v___x_137_; 
v_val_136_ = lean_ctor_get(v_fst_134_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v_fst_134_, 1);
v___x_137_ = lean_unbox(v_val_136_);
lean_dec(v_val_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(lean_object* v_info_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_info_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(lean_object* v_t_144_, lean_object* v_k_145_){
_start:
{
if (lean_obj_tag(v_t_144_) == 0)
{
lean_object* v_k_146_; lean_object* v_v_147_; lean_object* v_l_148_; lean_object* v_r_149_; uint8_t v___x_150_; 
v_k_146_ = lean_ctor_get(v_t_144_, 1);
v_v_147_ = lean_ctor_get(v_t_144_, 2);
v_l_148_ = lean_ctor_get(v_t_144_, 3);
v_r_149_ = lean_ctor_get(v_t_144_, 4);
v___x_150_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_145_, v_k_146_);
switch(v___x_150_)
{
case 0:
{
v_t_144_ = v_l_148_;
goto _start;
}
case 1:
{
lean_object* v___x_152_; 
lean_inc(v_v_147_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_v_147_);
return v___x_152_;
}
default: 
{
v_t_144_ = v_r_149_;
goto _start;
}
}
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(lean_object* v_t_155_, lean_object* v_k_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_155_, v_k_156_);
lean_dec(v_k_156_);
lean_dec(v_t_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(lean_object* v_code_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
switch(lean_obj_tag(v_code_158_))
{
case 0:
{
lean_object* v_k_166_; 
v_k_166_ = lean_ctor_get(v_code_158_, 1);
lean_inc_ref(v_k_166_);
lean_dec_ref_known(v_code_158_, 2);
v_code_158_ = v_k_166_;
goto _start;
}
case 1:
{
lean_object* v_decl_168_; lean_object* v_k_169_; lean_object* v_value_170_; lean_object* v___x_171_; 
v_decl_168_ = lean_ctor_get(v_code_158_, 0);
lean_inc_ref(v_decl_168_);
v_k_169_ = lean_ctor_get(v_code_158_, 1);
lean_inc_ref(v_k_169_);
lean_dec_ref_known(v_code_158_, 2);
v_value_170_ = lean_ctor_get(v_decl_168_, 4);
lean_inc_ref(v_value_170_);
lean_dec_ref(v_decl_168_);
v___x_171_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_170_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_dec_ref_known(v___x_171_, 1);
v_code_158_ = v_k_169_;
goto _start;
}
else
{
lean_dec_ref(v_k_169_);
return v___x_171_;
}
}
case 2:
{
lean_object* v_decl_173_; lean_object* v_k_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_207_; 
v_decl_173_ = lean_ctor_get(v_code_158_, 0);
v_k_174_ = lean_ctor_get(v_code_158_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_code_158_);
if (v_isSharedCheck_207_ == 0)
{
v___x_176_ = v_code_158_;
v_isShared_177_ = v_isSharedCheck_207_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_k_174_);
lean_inc(v_decl_173_);
lean_dec(v_code_158_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_207_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___x_188_; 
v___x_188_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_173_, v_a_161_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_188_, 1);
if (lean_obj_tag(v_a_189_) == 1)
{
lean_object* v_val_190_; lean_object* v___x_191_; lean_object* v_fvarId_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v_val_190_ = lean_ctor_get(v_a_189_, 0);
lean_inc(v_val_190_);
lean_dec_ref_known(v_a_189_, 1);
v___x_191_ = lean_st_ref_take(v_a_159_);
v_fvarId_192_ = lean_ctor_get(v_decl_173_, 0);
v___x_193_ = l_Lean_NameSet_empty;
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 0);
lean_ctor_set(v___x_176_, 1, v___x_193_);
lean_ctor_set(v___x_176_, 0, v_val_190_);
v___x_195_ = v___x_176_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_val_190_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_193_);
v___x_195_ = v_reuseFailAlloc_198_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_inc(v_fvarId_192_);
v___x_196_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_192_, v___x_195_, v___x_191_);
v___x_197_ = lean_st_ref_set(v_a_159_, v___x_196_);
v___y_179_ = v_a_159_;
v___y_180_ = v_a_160_;
v___y_181_ = v_a_161_;
v___y_182_ = v_a_162_;
v___y_183_ = v_a_163_;
v___y_184_ = v_a_164_;
goto v___jp_178_;
}
}
else
{
lean_dec(v_a_189_);
lean_del_object(v___x_176_);
v___y_179_ = v_a_159_;
v___y_180_ = v_a_160_;
v___y_181_ = v_a_161_;
v___y_182_ = v_a_162_;
v___y_183_ = v_a_163_;
v___y_184_ = v_a_164_;
goto v___jp_178_;
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_del_object(v___x_176_);
lean_dec_ref(v_k_174_);
lean_dec_ref(v_decl_173_);
v_a_199_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_188_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_188_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
v___jp_178_:
{
lean_object* v_value_185_; lean_object* v___x_186_; 
v_value_185_ = lean_ctor_get(v_decl_173_, 4);
lean_inc_ref(v_value_185_);
lean_dec_ref(v_decl_173_);
v___x_186_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_185_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_dec_ref_known(v___x_186_, 1);
v_code_158_ = v_k_174_;
v_a_159_ = v___y_179_;
v_a_160_ = v___y_180_;
v_a_161_ = v___y_181_;
v_a_162_ = v___y_182_;
v_a_163_ = v___y_183_;
v_a_164_ = v___y_184_;
goto _start;
}
else
{
lean_dec_ref(v_k_174_);
return v___x_186_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_208_; lean_object* v_args_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_fvarId_208_ = lean_ctor_get(v_code_158_, 0);
lean_inc(v_fvarId_208_);
v_args_209_ = lean_ctor_get(v_code_158_, 1);
lean_inc_ref(v_args_209_);
lean_dec_ref_known(v_code_158_, 2);
v___x_210_ = lean_st_ref_get(v_a_159_);
v___x_211_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_210_, v_fvarId_208_);
lean_dec(v___x_210_);
if (lean_obj_tag(v___x_211_) == 1)
{
lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_259_; 
v_val_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_259_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_259_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_259_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_paramIdx_216_; lean_object* v_ctorNames_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_258_; 
v_paramIdx_216_ = lean_ctor_get(v_val_212_, 0);
v_ctorNames_217_ = lean_ctor_get(v_val_212_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_val_212_);
if (v_isSharedCheck_258_ == 0)
{
v___x_219_ = v_val_212_;
v_isShared_220_ = v_isSharedCheck_258_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_ctorNames_217_);
lean_inc(v_paramIdx_216_);
lean_dec(v_val_212_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_258_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_box(0);
v___x_222_ = lean_array_get(v___x_221_, v_args_209_, v_paramIdx_216_);
lean_dec_ref(v_args_209_);
if (lean_obj_tag(v___x_222_) == 1)
{
lean_object* v_fvarId_223_; lean_object* v___x_224_; 
lean_del_object(v___x_214_);
v_fvarId_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_fvarId_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(v_fvarId_223_, v_a_160_, v_a_162_, v_a_164_);
lean_dec(v_fvarId_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_245_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_245_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_245_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_245_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
if (lean_obj_tag(v_a_225_) == 1)
{
lean_object* v_val_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v_val_229_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v_a_225_, 1);
v___x_230_ = lean_st_ref_take(v_a_159_);
v___x_231_ = l_Lean_NameSet_insert(v_ctorNames_217_, v_val_229_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_231_);
v___x_233_ = v___x_219_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_paramIdx_216_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_240_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_234_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_208_, v___x_233_, v___x_230_);
v___x_235_ = lean_st_ref_set(v_a_159_, v___x_234_);
v___x_236_ = lean_box(0);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_236_);
v___x_238_ = v___x_227_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_243_; 
lean_dec(v_a_225_);
lean_del_object(v___x_219_);
lean_dec(v_ctorNames_217_);
lean_dec(v_paramIdx_216_);
lean_dec(v_fvarId_208_);
v___x_241_ = lean_box(0);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_241_);
v___x_243_ = v___x_227_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_del_object(v___x_219_);
lean_dec(v_ctorNames_217_);
lean_dec(v_paramIdx_216_);
lean_dec(v_fvarId_208_);
v_a_246_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_224_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_224_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_256_; 
lean_dec(v___x_222_);
lean_del_object(v___x_219_);
lean_dec(v_ctorNames_217_);
lean_dec(v_paramIdx_216_);
lean_dec(v_fvarId_208_);
v___x_254_ = lean_box(0);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 0);
lean_ctor_set(v___x_214_, 0, v___x_254_);
v___x_256_ = v___x_214_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v___x_211_);
lean_dec_ref(v_args_209_);
lean_dec(v_fvarId_208_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
case 4:
{
lean_object* v_cases_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_285_; 
v_cases_262_ = lean_ctor_get(v_code_158_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_code_158_);
if (v_isSharedCheck_285_ == 0)
{
v___x_264_ = v_code_158_;
v_isShared_265_ = v_isSharedCheck_285_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_cases_262_);
lean_dec(v_code_158_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_285_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v_discr_266_; lean_object* v_alts_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_discr_266_ = lean_ctor_get(v_cases_262_, 2);
lean_inc(v_discr_266_);
v_alts_267_ = lean_ctor_get(v_cases_262_, 3);
lean_inc_ref(v_alts_267_);
lean_dec_ref(v_cases_262_);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_array_get_size(v_alts_267_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_nat_dec_lt(v___x_268_, v___x_269_);
if (v___x_271_ == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v_alts_267_);
lean_dec(v_discr_266_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 0);
lean_ctor_set(v___x_264_, 0, v___x_270_);
v___x_273_ = v___x_264_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_270_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_le(v___x_269_, v___x_269_);
if (v___x_275_ == 0)
{
if (v___x_271_ == 0)
{
lean_object* v___x_277_; 
lean_dec_ref(v_alts_267_);
lean_dec(v_discr_266_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 0);
lean_ctor_set(v___x_264_, 0, v___x_270_);
v___x_277_ = v___x_264_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_270_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; 
lean_del_object(v___x_264_);
v___x_279_ = ((size_t)0ULL);
v___x_280_ = lean_usize_of_nat(v___x_269_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_266_, v_alts_267_, v___x_279_, v___x_280_, v___x_270_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec_ref(v_alts_267_);
return v___x_281_;
}
}
else
{
size_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; 
lean_del_object(v___x_264_);
v___x_282_ = ((size_t)0ULL);
v___x_283_ = lean_usize_of_nat(v___x_269_);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_266_, v_alts_267_, v___x_282_, v___x_283_, v___x_270_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec_ref(v_alts_267_);
return v___x_284_;
}
}
}
}
default: 
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
v_isSharedCheck_293_ = !lean_is_exclusive(v_code_158_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_code_158_, 0);
lean_dec(v_unused_294_);
v___x_287_ = v_code_158_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_code_158_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_box(0);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 0);
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object* v_discr_295_, lean_object* v_as_296_, size_t v_i_297_, size_t v_stop_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___y_308_; uint8_t v___x_313_; 
v___x_313_ = lean_usize_dec_eq(v_i_297_, v_stop_298_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
v___x_314_ = lean_array_uget_borrowed(v_as_296_, v_i_297_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_ctorName_315_; lean_object* v_params_316_; lean_object* v_code_317_; lean_object* v___x_318_; 
v_ctorName_315_ = lean_ctor_get(v___x_314_, 0);
v_params_316_ = lean_ctor_get(v___x_314_, 1);
v_code_317_ = lean_ctor_get(v___x_314_, 2);
lean_inc_ref(v_params_316_);
lean_inc(v_ctorName_315_);
lean_inc(v_discr_295_);
v___x_318_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_295_, v_ctorName_315_, v_params_316_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
lean_inc_ref(v_code_317_);
v___x_320_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_317_, v___y_300_, v_a_319_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v_a_319_);
v___y_308_ = v___x_320_;
goto v___jp_307_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_discr_295_);
v_a_321_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_318_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v_code_329_; lean_object* v___x_330_; 
v_code_329_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_code_329_);
v___x_330_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_329_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
v___y_308_ = v___x_330_;
goto v___jp_307_;
}
}
else
{
lean_object* v___x_331_; 
lean_dec(v_discr_295_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_b_299_);
return v___x_331_;
}
v___jp_307_:
{
if (lean_obj_tag(v___y_308_) == 0)
{
lean_object* v_a_309_; size_t v___x_310_; size_t v___x_311_; 
v_a_309_ = lean_ctor_get(v___y_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___y_308_, 1);
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_297_, v___x_310_);
v_i_297_ = v___x_311_;
v_b_299_ = v_a_309_;
goto _start;
}
else
{
lean_dec(v_discr_295_);
return v___y_308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object* v_discr_332_, lean_object* v_as_333_, lean_object* v_i_334_, lean_object* v_stop_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_334_);
lean_dec(v_i_334_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_335_);
lean_dec(v_stop_335_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_332_, v_as_333_, v_i_boxed_344_, v_stop_boxed_345_, v_b_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v_as_333_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object* v_code_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object* v_00_u03b4_356_, lean_object* v_t_357_, lean_object* v_k_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_357_, v_k_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object* v_00_u03b4_360_, lean_object* v_t_361_, lean_object* v_k_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(v_00_u03b4_360_, v_t_361_, v_k_362_);
lean_dec(v_k_362_);
lean_dec(v_t_361_);
return v_res_363_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0(void){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1);
v___x_368_ = lean_box(1);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object* v_code_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = lean_box(1);
v___x_377_ = lean_st_mk_ref(v___x_376_);
v___x_378_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_379_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_370_, v___x_377_, v___x_378_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_387_; 
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_379_, 0);
lean_dec(v_unused_388_);
v___x_381_ = v___x_379_;
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
else
{
lean_dec(v___x_379_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_st_ref_get(v___x_377_);
lean_dec(v___x_377_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v___x_377_);
v_a_389_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object* v_code_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_403_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Array_instInhabited(lean_box(0));
return v___x_404_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1(void){
_start:
{
uint8_t v___x_405_; lean_object* v___x_406_; 
v___x_405_ = 0;
v___x_406_ = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(lean_object* v_msg_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_408_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0);
v___x_409_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_panic_fn_borrowed(v___x_410_, v_msg_407_);
lean_dec_ref_known(v___x_410_, 2);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_415_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2));
v___x_416_ = lean_unsigned_to_nat(11u);
v___x_417_ = lean_unsigned_to_nat(100u);
v___x_418_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1));
v___x_419_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0));
v___x_420_ = l_mkPanicMessageWithDecl(v___x_419_, v___x_418_, v___x_417_, v___x_416_, v___x_415_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(lean_object* v_code_421_, lean_object* v_decls_422_){
_start:
{
switch(lean_obj_tag(v_code_421_))
{
case 0:
{
lean_object* v_decl_423_; lean_object* v_k_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_decl_423_ = lean_ctor_get(v_code_421_, 0);
v_k_424_ = lean_ctor_get(v_code_421_, 1);
lean_inc_ref(v_decl_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_decl_423_);
v___x_426_ = lean_array_push(v_decls_422_, v___x_425_);
v_code_421_ = v_k_424_;
v_decls_422_ = v___x_426_;
goto _start;
}
case 4:
{
lean_object* v_cases_428_; lean_object* v___x_429_; 
v_cases_428_ = lean_ctor_get(v_code_421_, 0);
lean_inc_ref(v_cases_428_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_decls_422_);
lean_ctor_set(v___x_429_, 1, v_cases_428_);
return v___x_429_;
}
default: 
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v_decls_422_);
v___x_430_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3);
v___x_431_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(v___x_430_);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(lean_object* v_code_432_, lean_object* v_decls_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_432_, v_decls_433_);
lean_dec_ref(v_code_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(lean_object* v_code_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0));
v___x_439_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_437_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(lean_object* v_code_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_code_440_);
lean_dec_ref(v_code_440_);
return v_res_441_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object* v_singleton_442_, lean_object* v_as_443_, size_t v_i_444_, size_t v_stop_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_eq(v_i_444_, v_stop_445_);
if (v___x_446_ == 0)
{
uint8_t v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = 0;
v___x_448_ = lean_array_uget_borrowed(v_as_443_, v_i_444_);
v___x_449_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_447_, v___x_448_, v_singleton_442_);
if (v___x_449_ == 0)
{
size_t v___x_450_; size_t v___x_451_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_444_, v___x_450_);
v_i_444_ = v___x_451_;
goto _start;
}
else
{
return v___x_449_;
}
}
else
{
uint8_t v___x_453_; 
v___x_453_ = 0;
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object* v_singleton_454_, lean_object* v_as_455_, lean_object* v_i_456_, lean_object* v_stop_457_){
_start:
{
size_t v_i_boxed_458_; size_t v_stop_boxed_459_; uint8_t v_res_460_; lean_object* v_r_461_; 
v_i_boxed_458_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_stop_boxed_459_ = lean_unbox_usize(v_stop_457_);
lean_dec(v_stop_457_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_454_, v_as_455_, v_i_boxed_458_, v_stop_boxed_459_);
lean_dec_ref(v_as_455_);
lean_dec(v_singleton_454_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t v_sz_462_, size_t v_i_463_, lean_object* v_bs_464_, uint8_t v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_lt(v_i_463_, v_sz_462_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_bs_464_);
return v___x_473_;
}
else
{
uint8_t v___x_474_; lean_object* v_v_475_; lean_object* v___x_476_; 
v___x_474_ = 0;
v_v_475_ = lean_array_uget_borrowed(v_bs_464_, v_i_463_);
lean_inc(v_v_475_);
v___x_476_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_474_, v_v_475_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; lean_object* v_bs_x27_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v___x_478_ = lean_unsigned_to_nat(0u);
v_bs_x27_479_ = lean_array_uset(v_bs_464_, v_i_463_, v___x_478_);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_add(v_i_463_, v___x_480_);
v___x_482_ = lean_array_uset(v_bs_x27_479_, v_i_463_, v_a_477_);
v_i_463_ = v___x_481_;
v_bs_464_ = v___x_482_;
goto _start;
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v_bs_464_);
v_a_484_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_476_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_476_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object* v_sz_492_, lean_object* v_i_493_, lean_object* v_bs_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; uint8_t v___y_5526__boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_492_);
lean_dec(v_sz_492_);
v_i_boxed_503_ = lean_unbox_usize(v_i_493_);
lean_dec(v_i_493_);
v___y_5526__boxed_504_ = lean_unbox(v___y_495_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_boxed_502_, v_i_boxed_503_, v_bs_494_, v___y_5526__boxed_504_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object* v_fields_506_, lean_object* v_____r_507_, lean_object* v_paramsNew_508_, uint8_t v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
size_t v_sz_516_; size_t v___x_517_; lean_object* v___x_518_; 
v_sz_516_ = lean_array_size(v_fields_506_);
v___x_517_ = ((size_t)0ULL);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_516_, v___x_517_, v_fields_506_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_528_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_523_ = l_Array_append___redArg(v_paramsNew_508_, v_a_519_);
lean_dec(v_a_519_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_paramsNew_508_);
v_a_529_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_518_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_518_);
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
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object* v_fields_537_, lean_object* v_____r_538_, lean_object* v_paramsNew_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
uint8_t v___y_5584__boxed_547_; lean_object* v_res_548_; 
v___y_5584__boxed_547_ = lean_unbox(v___y_540_);
v_res_548_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_537_, v_____r_538_, v_paramsNew_539_, v___y_5584__boxed_547_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object* v_upperBound_549_, lean_object* v_params_550_, lean_object* v_targetParamIdx_551_, uint8_t v___y_552_, lean_object* v_fields_553_, lean_object* v_a_554_, lean_object* v_b_555_, uint8_t v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_a_564_; lean_object* v___y_569_; uint8_t v___x_588_; 
v___x_588_ = lean_nat_dec_lt(v_a_554_, v_upperBound_549_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_dec(v_a_554_);
lean_dec_ref(v_fields_553_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_b_555_);
return v___x_589_;
}
else
{
uint8_t v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = 0;
v___x_591_ = lean_array_fget_borrowed(v_params_550_, v_a_554_);
v___x_592_ = lean_nat_dec_eq(v_targetParamIdx_551_, v_a_554_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_inc(v___x_591_);
v___x_593_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_590_, v___x_591_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_array_push(v_b_555_, v_a_594_);
v_a_564_ = v___x_595_;
goto v___jp_563_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_b_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_fields_553_);
v_a_596_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_593_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
if (v___y_552_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_box(0);
lean_inc_ref(v_fields_553_);
v___x_605_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_553_, v___x_604_, v_b_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v___y_569_ = v___x_605_;
goto v___jp_568_;
}
else
{
lean_object* v___x_606_; 
lean_inc(v___x_591_);
v___x_606_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_590_, v___x_591_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = lean_array_push(v_b_555_, v_a_607_);
v___x_609_ = lean_box(0);
lean_inc_ref(v_fields_553_);
v___x_610_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_553_, v___x_609_, v___x_608_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v___y_569_ = v___x_610_;
goto v___jp_568_;
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v_b_555_);
lean_dec(v_a_554_);
lean_dec_ref(v_fields_553_);
v_a_611_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_606_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_606_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_a_554_, v___x_565_);
lean_dec(v_a_554_);
v_a_554_ = v___x_566_;
v_b_555_ = v_a_564_;
goto _start;
}
v___jp_568_:
{
if (lean_obj_tag(v___y_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_579_; 
v_a_570_ = lean_ctor_get(v___y_569_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___y_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_572_ = v___y_569_;
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___y_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_a_570_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; 
lean_dec(v_a_554_);
lean_dec_ref(v_fields_553_);
v_a_574_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v_a_570_, 1);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_a_574_);
v___x_576_ = v___x_572_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
else
{
lean_object* v_a_578_; 
lean_del_object(v___x_572_);
v_a_578_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v_a_570_, 1);
v_a_564_ = v_a_578_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_a_554_);
lean_dec_ref(v_fields_553_);
v_a_580_ = lean_ctor_get(v___y_569_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___y_569_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___y_569_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___y_569_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object* v_upperBound_619_, lean_object* v_params_620_, lean_object* v_targetParamIdx_621_, lean_object* v___y_622_, lean_object* v_fields_623_, lean_object* v_a_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
uint8_t v___y_5648__boxed_633_; uint8_t v___y_5649__boxed_634_; lean_object* v_res_635_; 
v___y_5648__boxed_633_ = lean_unbox(v___y_622_);
v___y_5649__boxed_634_ = lean_unbox(v___y_626_);
v_res_635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_619_, v_params_620_, v_targetParamIdx_621_, v___y_5648__boxed_633_, v_fields_623_, v_a_624_, v_b_625_, v___y_5649__boxed_634_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec(v_targetParamIdx_621_);
lean_dec_ref(v_params_620_);
lean_dec(v_upperBound_619_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(size_t v_sz_636_, size_t v_i_637_, lean_object* v_bs_638_, uint8_t v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_usize_dec_lt(v_i_637_, v_sz_636_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v_bs_638_);
return v___x_647_;
}
else
{
uint8_t v___x_648_; lean_object* v_v_649_; lean_object* v___x_650_; 
v___x_648_ = 0;
v_v_649_ = lean_array_uget_borrowed(v_bs_638_, v_i_637_);
lean_inc(v_v_649_);
v___x_650_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_648_, v_v_649_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v_bs_x27_653_; size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = lean_unsigned_to_nat(0u);
v_bs_x27_653_ = lean_array_uset(v_bs_638_, v_i_637_, v___x_652_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_637_, v___x_654_);
v___x_656_ = lean_array_uset(v_bs_x27_653_, v_i_637_, v_a_651_);
v_i_637_ = v___x_655_;
v_bs_638_ = v___x_656_;
goto _start;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_bs_638_);
v_a_658_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_650_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_650_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(lean_object* v_sz_666_, lean_object* v_i_667_, lean_object* v_bs_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; uint8_t v___y_5786__boxed_678_; lean_object* v_res_679_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_666_);
lean_dec(v_sz_666_);
v_i_boxed_677_ = lean_unbox_usize(v_i_667_);
lean_dec(v_i_667_);
v___y_5786__boxed_678_ = lean_unbox(v___y_669_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_boxed_676_, v_i_boxed_677_, v_bs_668_, v___y_5786__boxed_678_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
return v_res_679_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0(void){
_start:
{
uint8_t v___x_680_; lean_object* v___x_681_; 
v___x_680_ = 0;
v___x_681_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object* v_decls_687_, lean_object* v_params_688_, lean_object* v_targetParamIdx_689_, lean_object* v_fields_690_, lean_object* v_k_691_, uint8_t v_default_692_, uint8_t v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_fvarId_703_; lean_object* v___x_704_; lean_object* v_paramsNew_705_; uint8_t v___y_707_; lean_object* v_singleton_761_; uint8_t v___x_762_; 
v___x_700_ = 0;
v___x_701_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0);
v___x_702_ = lean_array_get_borrowed(v___x_701_, v_params_688_, v_targetParamIdx_689_);
v_fvarId_703_ = lean_ctor_get(v___x_702_, 0);
v___x_704_ = lean_unsigned_to_nat(0u);
v_paramsNew_705_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
lean_inc(v_fvarId_703_);
v_singleton_761_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_703_);
v___x_762_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_700_, v_k_691_, v_singleton_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = lean_array_get_size(v_decls_687_);
v___x_764_ = lean_nat_dec_lt(v___x_704_, v___x_763_);
if (v___x_764_ == 0)
{
lean_dec(v_singleton_761_);
v___y_707_ = v___x_762_;
goto v___jp_706_;
}
else
{
if (v___x_764_ == 0)
{
lean_dec(v_singleton_761_);
v___y_707_ = v___x_762_;
goto v___jp_706_;
}
else
{
size_t v___x_765_; size_t v___x_766_; uint8_t v___x_767_; 
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_of_nat(v___x_763_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_761_, v_decls_687_, v___x_765_, v___x_766_);
lean_dec(v_singleton_761_);
v___y_707_ = v___x_767_;
goto v___jp_706_;
}
}
}
else
{
lean_dec(v_singleton_761_);
v___y_707_ = v___x_762_;
goto v___jp_706_;
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_array_get_size(v_params_688_);
v___x_709_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v___x_708_, v_params_688_, v_targetParamIdx_689_, v___y_707_, v_fields_690_, v___x_704_, v_paramsNew_705_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; size_t v_sz_711_; size_t v___x_712_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v_sz_711_ = lean_array_size(v_decls_687_);
v___x_712_ = ((size_t)0ULL);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_711_, v___x_712_, v_decls_687_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_700_, v_k_691_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_700_, v_a_714_, v_a_716_);
lean_dec(v_a_714_);
v___x_718_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3));
v___x_719_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___x_700_, v_a_710_, v___x_717_, v___x_718_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_724_, 0, v_a_720_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*1, v_default_692_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*1 + 1, v___y_707_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_a_729_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_719_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_719_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_a_714_);
lean_dec(v_a_710_);
v_a_737_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_715_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_715_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
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
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_a_710_);
lean_dec_ref(v_k_691_);
v_a_745_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_713_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_713_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_k_691_);
lean_dec_ref(v_decls_687_);
v_a_753_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_709_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_709_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object* v_decls_768_, lean_object* v_params_769_, lean_object* v_targetParamIdx_770_, lean_object* v_fields_771_, lean_object* v_k_772_, lean_object* v_default_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
uint8_t v_default_boxed_781_; uint8_t v_a_boxed_782_; lean_object* v_res_783_; 
v_default_boxed_781_ = lean_unbox(v_default_773_);
v_a_boxed_782_ = lean_unbox(v_a_774_);
v_res_783_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_768_, v_params_769_, v_targetParamIdx_770_, v_fields_771_, v_k_772_, v_default_boxed_781_, v_a_boxed_782_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec(v_targetParamIdx_770_);
lean_dec_ref(v_params_769_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object* v_upperBound_784_, lean_object* v_params_785_, lean_object* v_targetParamIdx_786_, uint8_t v___y_787_, lean_object* v_fields_788_, lean_object* v_inst_789_, lean_object* v_R_790_, lean_object* v_a_791_, lean_object* v_b_792_, lean_object* v_c_793_, uint8_t v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_784_, v_params_785_, v_targetParamIdx_786_, v___y_787_, v_fields_788_, v_a_791_, v_b_792_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_802_ = _args[0];
lean_object* v_params_803_ = _args[1];
lean_object* v_targetParamIdx_804_ = _args[2];
lean_object* v___y_805_ = _args[3];
lean_object* v_fields_806_ = _args[4];
lean_object* v_inst_807_ = _args[5];
lean_object* v_R_808_ = _args[6];
lean_object* v_a_809_ = _args[7];
lean_object* v_b_810_ = _args[8];
lean_object* v_c_811_ = _args[9];
lean_object* v___y_812_ = _args[10];
lean_object* v___y_813_ = _args[11];
lean_object* v___y_814_ = _args[12];
lean_object* v___y_815_ = _args[13];
lean_object* v___y_816_ = _args[14];
lean_object* v___y_817_ = _args[15];
lean_object* v___y_818_ = _args[16];
_start:
{
uint8_t v___y_5993__boxed_819_; uint8_t v___y_5995__boxed_820_; lean_object* v_res_821_; 
v___y_5993__boxed_819_ = lean_unbox(v___y_805_);
v___y_5995__boxed_820_ = lean_unbox(v___y_812_);
v_res_821_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(v_upperBound_802_, v_params_803_, v_targetParamIdx_804_, v___y_5993__boxed_819_, v_fields_806_, v_inst_807_, v_R_808_, v_a_809_, v_b_810_, v_c_811_, v___y_5995__boxed_820_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v_targetParamIdx_804_);
lean_dec_ref(v_params_803_);
lean_dec(v_upperBound_802_);
return v_res_821_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_box(0);
v___x_823_ = lean_unsigned_to_nat(16u);
v___x_824_ = lean_mk_array(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object* v_decls_828_, lean_object* v_params_829_, lean_object* v_targetParamIdx_830_, lean_object* v_fields_831_, lean_object* v_k_832_, uint8_t v_default_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; 
v___x_839_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1);
v___x_840_ = lean_st_mk_ref(v___x_839_);
v___x_841_ = 0;
v___x_842_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_828_, v_params_829_, v_targetParamIdx_830_, v_fields_831_, v_k_832_, v_default_833_, v___x_841_, v___x_840_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_851_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_st_ref_get(v___x_840_);
lean_dec(v___x_840_);
lean_dec(v___x_847_);
if (v_isShared_846_ == 0)
{
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_843_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_dec(v___x_840_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object* v_decls_852_, lean_object* v_params_853_, lean_object* v_targetParamIdx_854_, lean_object* v_fields_855_, lean_object* v_k_856_, lean_object* v_default_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
uint8_t v_default_boxed_863_; lean_object* v_res_864_; 
v_default_boxed_863_ = lean_unbox(v_default_857_);
v_res_864_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_decls_852_, v_params_853_, v_targetParamIdx_854_, v_fields_855_, v_k_856_, v_default_boxed_863_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_targetParamIdx_854_);
lean_dec_ref(v_params_853_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object* v_args_865_, lean_object* v_targetParamIdx_866_, lean_object* v_fields_867_, uint8_t v_dependsOnTarget_868_){
_start:
{
if (v_dependsOnTarget_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_lower_874_; lean_object* v_upper_875_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_869_ = lean_unsigned_to_nat(0u);
lean_inc(v_targetParamIdx_866_);
lean_inc_ref(v_args_865_);
v___x_870_ = l_Array_toSubarray___redArg(v_args_865_, v___x_869_, v_targetParamIdx_866_);
v___x_871_ = l_Subarray_copy___redArg(v___x_870_);
v___x_872_ = l_Array_append___redArg(v___x_871_, v_fields_867_);
v___x_879_ = lean_array_get_size(v_args_865_);
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_nat_add(v_targetParamIdx_866_, v___x_880_);
lean_dec(v_targetParamIdx_866_);
v___x_882_ = lean_nat_dec_le(v___x_881_, v___x_869_);
if (v___x_882_ == 0)
{
v_lower_874_ = v___x_881_;
v_upper_875_ = v___x_879_;
goto v___jp_873_;
}
else
{
lean_dec(v___x_881_);
v_lower_874_ = v___x_869_;
v_upper_875_ = v___x_879_;
goto v___jp_873_;
}
v___jp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = l_Array_toSubarray___redArg(v_args_865_, v_lower_874_, v_upper_875_);
v___x_877_ = l_Subarray_copy___redArg(v___x_876_);
v___x_878_ = l_Array_append___redArg(v___x_872_, v___x_877_);
lean_dec_ref(v___x_877_);
return v___x_878_;
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_lower_890_; lean_object* v_upper_891_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_targetParamIdx_866_, v___x_884_);
lean_dec(v_targetParamIdx_866_);
lean_inc(v___x_885_);
lean_inc_ref(v_args_865_);
v___x_886_ = l_Array_toSubarray___redArg(v_args_865_, v___x_883_, v___x_885_);
v___x_887_ = l_Subarray_copy___redArg(v___x_886_);
v___x_888_ = l_Array_append___redArg(v___x_887_, v_fields_867_);
v___x_895_ = lean_array_get_size(v_args_865_);
v___x_896_ = lean_nat_dec_le(v___x_885_, v___x_883_);
if (v___x_896_ == 0)
{
v_lower_890_ = v___x_885_;
v_upper_891_ = v___x_895_;
goto v___jp_889_;
}
else
{
lean_dec(v___x_885_);
v_lower_890_ = v___x_883_;
v_upper_891_ = v___x_895_;
goto v___jp_889_;
}
v___jp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = l_Array_toSubarray___redArg(v_args_865_, v_lower_890_, v_upper_891_);
v___x_893_ = l_Subarray_copy___redArg(v___x_892_);
v___x_894_ = l_Array_append___redArg(v___x_888_, v___x_893_);
lean_dec_ref(v___x_893_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object* v_args_897_, lean_object* v_targetParamIdx_898_, lean_object* v_fields_899_, lean_object* v_dependsOnTarget_900_){
_start:
{
uint8_t v_dependsOnTarget_boxed_901_; lean_object* v_res_902_; 
v_dependsOnTarget_boxed_901_ = lean_unbox(v_dependsOnTarget_900_);
v_res_902_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_897_, v_targetParamIdx_898_, v_fields_899_, v_dependsOnTarget_boxed_901_);
lean_dec_ref(v_fields_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t v_sz_903_, size_t v_i_904_, lean_object* v_bs_905_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_904_, v_sz_903_);
if (v___x_906_ == 0)
{
return v_bs_905_;
}
else
{
lean_object* v_v_907_; lean_object* v_fvarId_908_; lean_object* v___x_909_; lean_object* v_bs_x27_910_; lean_object* v___x_911_; size_t v___x_912_; size_t v___x_913_; lean_object* v___x_914_; 
v_v_907_ = lean_array_uget_borrowed(v_bs_905_, v_i_904_);
v_fvarId_908_ = lean_ctor_get(v_v_907_, 0);
lean_inc(v_fvarId_908_);
v___x_909_ = lean_unsigned_to_nat(0u);
v_bs_x27_910_ = lean_array_uset(v_bs_905_, v_i_904_, v___x_909_);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v_fvarId_908_);
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_add(v_i_904_, v___x_912_);
v___x_914_ = lean_array_uset(v_bs_x27_910_, v_i_904_, v___x_911_);
v_i_904_ = v___x_913_;
v_bs_905_ = v___x_914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_bs_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_920_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_boxed_919_, v_i_boxed_920_, v_bs_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t v_sz_922_, size_t v_i_923_, lean_object* v_bs_924_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_lt(v_i_923_, v_sz_922_);
if (v___x_925_ == 0)
{
return v_bs_924_;
}
else
{
lean_object* v_v_926_; lean_object* v_fvarId_927_; lean_object* v___x_928_; lean_object* v_bs_x27_929_; lean_object* v___x_930_; size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_v_926_ = lean_array_uget_borrowed(v_bs_924_, v_i_923_);
v_fvarId_927_ = lean_ctor_get(v_v_926_, 0);
lean_inc(v_fvarId_927_);
v___x_928_ = lean_unsigned_to_nat(0u);
v_bs_x27_929_ = lean_array_uset(v_bs_924_, v_i_923_, v___x_928_);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v_fvarId_927_);
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_923_, v___x_931_);
v___x_933_ = lean_array_uset(v_bs_x27_929_, v_i_923_, v___x_930_);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_922_, v___x_932_, v___x_933_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(lean_object* v_sz_935_, lean_object* v_i_936_, lean_object* v_bs_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_935_);
lean_dec(v_sz_935_);
v_i_boxed_939_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_boxed_938_, v_i_boxed_939_, v_bs_937_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object* v_params_941_, lean_object* v_targetParamIdx_942_, lean_object* v_fields_943_, uint8_t v_dependsOnTarget_944_){
_start:
{
size_t v_sz_945_; size_t v___x_946_; lean_object* v___x_947_; size_t v_sz_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_sz_945_ = lean_array_size(v_params_941_);
v___x_946_ = ((size_t)0ULL);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_945_, v___x_946_, v_params_941_);
v_sz_948_ = lean_array_size(v_fields_943_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_948_, v___x_946_, v_fields_943_);
v___x_950_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v___x_947_, v_targetParamIdx_942_, v___x_949_, v_dependsOnTarget_944_);
lean_dec_ref(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object* v_params_951_, lean_object* v_targetParamIdx_952_, lean_object* v_fields_953_, lean_object* v_dependsOnTarget_954_){
_start:
{
uint8_t v_dependsOnTarget_boxed_955_; lean_object* v_res_956_; 
v_dependsOnTarget_boxed_955_ = lean_unbox(v_dependsOnTarget_954_);
v_res_956_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_951_, v_targetParamIdx_952_, v_fields_953_, v_dependsOnTarget_boxed_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object* v_fvarId_962_, lean_object* v_args_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_st_ref_get(v_a_965_);
v___x_973_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_972_, v_fvarId_962_);
lean_dec(v___x_972_);
if (lean_obj_tag(v___x_973_) == 1)
{
lean_object* v_val_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1156_; 
v_val_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_1156_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_val_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1156_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_964_, v_fvarId_962_);
if (lean_obj_tag(v___x_978_) == 1)
{
lean_object* v_val_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1151_; 
lean_del_object(v___x_976_);
v_val_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_1151_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_val_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1151_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_paramIdx_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1149_; 
v_paramIdx_983_ = lean_ctor_get(v_val_979_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_val_979_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_val_979_, 1);
lean_dec(v_unused_1150_);
v___x_985_ = v_val_979_;
v_isShared_986_ = v_isSharedCheck_1149_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_paramIdx_983_);
lean_dec(v_val_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1149_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_box(0);
v___x_988_ = lean_array_get(v___x_987_, v_args_963_, v_paramIdx_983_);
if (lean_obj_tag(v___x_988_) == 1)
{
lean_object* v_fvarId_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1144_; 
lean_del_object(v___x_981_);
v_fvarId_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1144_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_fvarId_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1144_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_989_, v_a_966_, v_a_968_, v_a_970_);
lean_dec(v_fvarId_989_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1135_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1135_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1135_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
if (lean_obj_tag(v_a_994_) == 1)
{
lean_object* v_val_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1130_; 
v_val_998_ = lean_ctor_get(v_a_994_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_a_994_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1000_ = v_a_994_;
v_isShared_1001_ = v_isSharedCheck_1130_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_val_998_);
lean_dec(v_a_994_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1130_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_998_);
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_974_, v___x_1002_);
lean_dec(v___x_1002_);
lean_dec(v_val_974_);
if (lean_obj_tag(v___x_1003_) == 1)
{
lean_object* v_val_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1125_; 
v_val_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1125_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_val_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1125_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
uint8_t v_default_1008_; 
v_default_1008_ = lean_ctor_get_uint8(v_val_1004_, sizeof(void*)*1);
if (v_default_1008_ == 0)
{
if (lean_obj_tag(v_val_998_) == 0)
{
lean_object* v_decl_1009_; uint8_t v_dependsOnDiscr_1010_; lean_object* v_val_1011_; lean_object* v_args_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1047_; 
lean_del_object(v___x_1000_);
lean_del_object(v___x_991_);
lean_del_object(v___x_985_);
v_decl_1009_ = lean_ctor_get(v_val_1004_, 0);
lean_inc_ref(v_decl_1009_);
v_dependsOnDiscr_1010_ = lean_ctor_get_uint8(v_val_1004_, sizeof(void*)*1 + 1);
lean_dec(v_val_1004_);
v_val_1011_ = lean_ctor_get(v_val_998_, 0);
v_args_1012_ = lean_ctor_get(v_val_998_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_val_998_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1014_ = v_val_998_;
v_isShared_1015_ = v_isSharedCheck_1047_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_args_1012_);
lean_inc(v_val_1011_);
lean_dec(v_val_998_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1047_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___y_1017_; lean_object* v_numParams_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_numParams_1037_ = lean_ctor_get(v_val_1011_, 3);
lean_inc(v_numParams_1037_);
lean_dec_ref(v_val_1011_);
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = lean_array_get_size(v_args_1012_);
v___x_1040_ = lean_nat_dec_le(v_numParams_1037_, v___x_1038_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1042_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1039_);
lean_ctor_set(v___x_1014_, 0, v_numParams_1037_);
v___x_1042_ = v___x_1014_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_numParams_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1039_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
v___y_1017_ = v___x_1042_;
goto v___jp_1016_;
}
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_numParams_1037_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1039_);
lean_ctor_set(v___x_1014_, 0, v___x_1038_);
v___x_1045_ = v___x_1014_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1039_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
v___y_1017_ = v___x_1045_;
goto v___jp_1016_;
}
}
v___jp_1016_:
{
lean_object* v_fvarId_1018_; lean_object* v_lower_1019_; lean_object* v_upper_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1036_; 
v_fvarId_1018_ = lean_ctor_get(v_decl_1009_, 0);
lean_inc(v_fvarId_1018_);
lean_dec_ref(v_decl_1009_);
v_lower_1019_ = lean_ctor_get(v___y_1017_, 0);
v_upper_1020_ = lean_ctor_get(v___y_1017_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___y_1017_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1022_ = v___y_1017_;
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_upper_1020_);
lean_inc(v_lower_1019_);
lean_dec(v___y_1017_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1024_ = l_Array_toSubarray___redArg(v_args_1012_, v_lower_1019_, v_upper_1020_);
v___x_1025_ = l_Subarray_copy___redArg(v___x_1024_);
v___x_1026_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_963_, v_paramIdx_983_, v___x_1025_, v_dependsOnDiscr_1010_);
lean_dec_ref(v___x_1025_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 3);
lean_ctor_set(v___x_1022_, 1, v___x_1026_);
lean_ctor_set(v___x_1022_, 0, v_fvarId_1018_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_fvarId_1018_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1028_);
v___x_1030_ = v___x_1006_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1030_);
v___x_1032_ = v___x_996_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
}
else
{
lean_object* v_decl_1048_; uint8_t v_dependsOnDiscr_1049_; lean_object* v_n_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1110_; 
v_decl_1048_ = lean_ctor_get(v_val_1004_, 0);
lean_inc_ref(v_decl_1048_);
v_dependsOnDiscr_1049_ = lean_ctor_get_uint8(v_val_1004_, sizeof(void*)*1 + 1);
lean_dec(v_val_1004_);
v_n_1050_ = lean_ctor_get(v_val_998_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_val_998_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1052_ = v_val_998_;
v_isShared_1053_ = v_isSharedCheck_1110_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_n_1050_);
lean_dec(v_val_998_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1110_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_zero_1054_; uint8_t v_isZero_1055_; 
v_zero_1054_ = lean_unsigned_to_nat(0u);
v_isZero_1055_ = lean_nat_dec_eq(v_n_1050_, v_zero_1054_);
if (v_isZero_1055_ == 1)
{
lean_object* v_fvarId_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
lean_del_object(v___x_1052_);
lean_dec(v_n_1050_);
lean_del_object(v___x_1000_);
lean_del_object(v___x_991_);
v_fvarId_1056_ = lean_ctor_get(v_decl_1048_, 0);
lean_inc(v_fvarId_1056_);
lean_dec_ref(v_decl_1048_);
v___x_1057_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1058_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_963_, v_paramIdx_983_, v___x_1057_, v_dependsOnDiscr_1049_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 3);
lean_ctor_set(v___x_985_, 1, v___x_1058_);
lean_ctor_set(v___x_985_, 0, v_fvarId_1056_);
v___x_1060_ = v___x_985_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_fvarId_1056_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1060_);
v___x_1062_ = v___x_1006_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1064_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1062_);
v___x_1064_ = v___x_996_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
else
{
uint8_t v___x_1068_; lean_object* v_one_1069_; lean_object* v_n_1070_; lean_object* v___x_1072_; 
lean_del_object(v___x_996_);
v___x_1068_ = 0;
v_one_1069_ = lean_unsigned_to_nat(1u);
v_n_1070_ = lean_nat_sub(v_n_1050_, v_one_1069_);
lean_dec(v_n_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 0);
lean_ctor_set(v___x_1052_, 0, v_n_1070_);
v___x_1072_ = v___x_1052_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_n_1070_);
v___x_1072_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 0);
lean_ctor_set(v___x_1000_, 0, v___x_1072_);
v___x_1074_ = v___x_1000_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
v___x_1076_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1068_, v___x_1074_, v___x_1075_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1099_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1099_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1099_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_fvarId_1081_; lean_object* v_fvarId_1082_; lean_object* v___x_1084_; 
v_fvarId_1081_ = lean_ctor_get(v_decl_1048_, 0);
lean_inc(v_fvarId_1081_);
lean_dec_ref(v_decl_1048_);
v_fvarId_1082_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_fvarId_1082_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_fvarId_1082_);
v___x_1084_ = v___x_991_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fvarId_1082_);
v___x_1084_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1085_ = lean_mk_empty_array_with_capacity(v_one_1069_);
v___x_1086_ = lean_array_push(v___x_1085_, v___x_1084_);
v___x_1087_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_963_, v_paramIdx_983_, v___x_1086_, v_dependsOnDiscr_1049_);
lean_dec_ref(v___x_1086_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 3);
lean_ctor_set(v___x_985_, 1, v___x_1087_);
lean_ctor_set(v___x_985_, 0, v_fvarId_1081_);
v___x_1089_ = v___x_985_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_fvarId_1081_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_a_1077_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1090_);
v___x_1092_ = v___x_1006_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1092_);
v___x_1094_ = v___x_1079_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
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
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v_decl_1048_);
lean_del_object(v___x_1006_);
lean_del_object(v___x_991_);
lean_del_object(v___x_985_);
lean_dec(v_paramIdx_983_);
lean_dec_ref(v_args_963_);
v_a_1100_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1076_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1076_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
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
lean_object* v_decl_1111_; uint8_t v_dependsOnDiscr_1112_; lean_object* v_fvarId_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_del_object(v___x_1000_);
lean_dec(v_val_998_);
lean_del_object(v___x_991_);
v_decl_1111_ = lean_ctor_get(v_val_1004_, 0);
lean_inc_ref(v_decl_1111_);
v_dependsOnDiscr_1112_ = lean_ctor_get_uint8(v_val_1004_, sizeof(void*)*1 + 1);
lean_dec(v_val_1004_);
v_fvarId_1113_ = lean_ctor_get(v_decl_1111_, 0);
lean_inc(v_fvarId_1113_);
lean_dec_ref(v_decl_1111_);
v___x_1114_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1115_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_963_, v_paramIdx_983_, v___x_1114_, v_dependsOnDiscr_1112_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 3);
lean_ctor_set(v___x_985_, 1, v___x_1115_);
lean_ctor_set(v___x_985_, 0, v_fvarId_1113_);
v___x_1117_ = v___x_985_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_fvarId_1113_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1117_);
v___x_1119_ = v___x_1006_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1119_);
v___x_1121_ = v___x_996_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
lean_dec(v___x_1003_);
lean_del_object(v___x_1000_);
lean_dec(v_val_998_);
lean_del_object(v___x_991_);
lean_del_object(v___x_985_);
lean_dec(v_paramIdx_983_);
lean_dec_ref(v_args_963_);
v___x_1126_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1126_);
v___x_1128_ = v___x_996_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
lean_dec(v_a_994_);
lean_del_object(v___x_991_);
lean_del_object(v___x_985_);
lean_dec(v_paramIdx_983_);
lean_dec(v_val_974_);
lean_dec_ref(v_args_963_);
v___x_1131_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1131_);
v___x_1133_ = v___x_996_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_del_object(v___x_991_);
lean_del_object(v___x_985_);
lean_dec(v_paramIdx_983_);
lean_dec(v_val_974_);
lean_dec_ref(v_args_963_);
v_a_1136_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_993_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_993_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v___x_988_);
lean_del_object(v___x_985_);
lean_dec(v_paramIdx_983_);
lean_dec(v_val_974_);
lean_dec_ref(v_args_963_);
v___x_1145_ = lean_box(0);
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 0, v___x_1145_);
v___x_1147_ = v___x_981_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_dec(v___x_978_);
lean_dec(v_val_974_);
lean_dec_ref(v_args_963_);
v___x_1152_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 0);
lean_ctor_set(v___x_976_, 0, v___x_1152_);
v___x_1154_ = v___x_976_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v___x_973_);
lean_dec_ref(v_args_963_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object* v_fvarId_1159_, lean_object* v_args_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1159_, v_args_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec(v_fvarId_1159_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object* v___x_1170_, lean_object* v_init_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v_k_1173_; lean_object* v_l_1174_; lean_object* v_r_1175_; lean_object* v___x_1176_; 
v_k_1173_ = lean_ctor_get(v_x_1172_, 1);
v_l_1174_ = lean_ctor_get(v_x_1172_, 3);
v_r_1175_ = lean_ctor_get(v_x_1172_, 4);
v___x_1176_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1170_, v_init_1171_, v_l_1174_);
if (lean_obj_tag(v___x_1176_) == 0)
{
return v___x_1176_;
}
else
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1191_; 
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v___x_1176_, 0);
lean_dec(v_unused_1192_);
v___x_1178_ = v___x_1176_;
v_isShared_1179_ = v_isSharedCheck_1191_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v___x_1176_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1191_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = l_Lean_NameSet_contains(v___x_1170_, v_k_1173_);
v___x_1182_ = lean_bool_not(v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_del_object(v___x_1178_);
v___x_1183_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0));
v_init_1171_ = v___x_1183_;
v_x_1172_ = v_r_1175_;
goto _start;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1185_ = lean_box(v___x_1182_);
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1180_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set_tag(v___x_1178_, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1187_);
v___x_1189_ = v___x_1178_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_init_1171_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object* v___x_1194_, lean_object* v_init_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1194_, v_init_1195_, v_x_1196_);
lean_dec(v_x_1196_);
lean_dec(v___x_1194_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object* v___x_1198_, lean_object* v_a_1199_, lean_object* v_init_1200_, lean_object* v_x_1201_){
_start:
{
lean_object* v_d_1204_; 
if (lean_obj_tag(v_x_1201_) == 0)
{
lean_object* v_k_1207_; lean_object* v_l_1208_; lean_object* v_r_1209_; lean_object* v___x_1210_; lean_object* v_a_1211_; 
v_k_1207_ = lean_ctor_get(v_x_1201_, 1);
lean_inc(v_k_1207_);
v_l_1208_ = lean_ctor_get(v_x_1201_, 3);
lean_inc(v_l_1208_);
v_r_1209_ = lean_ctor_get(v_x_1201_, 4);
lean_inc(v_r_1209_);
lean_dec_ref_known(v_x_1201_, 5);
lean_inc_ref(v_a_1199_);
v___x_1210_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1198_, v_a_1199_, v_init_1200_, v_l_1208_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
if (lean_obj_tag(v_a_1211_) == 0)
{
lean_object* v_a_1212_; 
lean_dec_ref(v___x_1210_);
lean_dec(v_r_1209_);
lean_dec(v_k_1207_);
lean_dec_ref(v_a_1199_);
v_a_1212_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v_a_1211_, 1);
v_d_1204_ = v_a_1212_;
goto v___jp_1203_;
}
else
{
lean_object* v_a_1213_; uint8_t v___x_1214_; 
v_a_1213_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v_a_1211_, 1);
v___x_1214_ = l_Lean_NameSet_contains(v___x_1198_, v_k_1207_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec_ref(v___x_1210_);
lean_inc_ref(v_a_1199_);
v___x_1215_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1207_, v_a_1199_, v_a_1213_);
v_init_1200_ = v___x_1215_;
v_x_1201_ = v_r_1209_;
goto _start;
}
else
{
lean_object* v_a_1217_; 
lean_dec(v_a_1213_);
lean_dec(v_k_1207_);
v_a_1217_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1210_);
if (lean_obj_tag(v_a_1217_) == 0)
{
lean_object* v_a_1218_; 
lean_dec(v_r_1209_);
lean_dec_ref(v_a_1199_);
v_a_1218_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v_a_1217_, 1);
v_d_1204_ = v_a_1218_;
goto v___jp_1203_;
}
else
{
lean_object* v_a_1219_; 
v_a_1219_ = lean_ctor_get(v_a_1217_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v_a_1217_, 1);
v_init_1200_ = v_a_1219_;
v_x_1201_ = v_r_1209_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v_a_1199_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_init_1200_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_d_1204_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object* v___x_1223_, lean_object* v_a_1224_, lean_object* v_init_1225_, lean_object* v_x_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1223_, v_a_1224_, v_init_1225_, v_x_1226_);
lean_dec(v___x_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object* v_discr_1234_, lean_object* v___x_1235_, lean_object* v_val_1236_, lean_object* v_fst_1237_, lean_object* v_params_1238_, lean_object* v_snd_1239_, lean_object* v_as_1240_, size_t v_sz_1241_, size_t v_i_1242_, lean_object* v_b_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_a_1253_; uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1242_, v_sz_1241_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_b_1243_);
return v___x_1258_;
}
else
{
lean_object* v_snd_1259_; lean_object* v_fst_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1418_; 
v_snd_1259_ = lean_ctor_get(v_b_1243_, 1);
v_fst_1260_ = lean_ctor_get(v_b_1243_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_b_1243_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1262_ = v_b_1243_;
v_isShared_1263_ = v_isSharedCheck_1418_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1259_);
lean_inc(v_fst_1260_);
lean_dec(v_b_1243_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1418_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_fst_1264_; lean_object* v_snd_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1417_; 
v_fst_1264_ = lean_ctor_get(v_snd_1259_, 0);
v_snd_1265_ = lean_ctor_get(v_snd_1259_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_snd_1259_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1267_ = v_snd_1259_;
v_isShared_1268_ = v_isSharedCheck_1417_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snd_1265_);
lean_inc(v_fst_1264_);
lean_dec(v_snd_1259_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1417_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
uint8_t v___x_1269_; lean_object* v_a_1270_; uint8_t v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v_a_1277_; 
v___x_1269_ = 0;
v_a_1270_ = lean_array_uget_borrowed(v_as_1240_, v_i_1242_);
if (lean_obj_tag(v_a_1270_) == 0)
{
lean_object* v_ctorName_1289_; lean_object* v_params_1290_; lean_object* v_code_1291_; lean_object* v___x_1292_; 
lean_del_object(v___x_1267_);
lean_del_object(v___x_1262_);
v_ctorName_1289_ = lean_ctor_get(v_a_1270_, 0);
v_params_1290_ = lean_ctor_get(v_a_1270_, 1);
v_code_1291_ = lean_ctor_get(v_a_1270_, 2);
lean_inc_ref(v_params_1290_);
lean_inc(v_ctorName_1289_);
lean_inc(v_discr_1234_);
v___x_1292_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1234_, v_ctorName_1289_, v_params_1290_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
lean_inc_ref(v_code_1291_);
v___x_1294_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1291_, v___y_1244_, v___y_1245_, v_a_1293_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v_a_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; uint8_t v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = l_Lean_NameSet_contains(v___x_1235_, v_ctorName_1289_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_inc_ref(v_a_1270_);
v___x_1297_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1270_, v_a_1295_);
v___x_1298_ = lean_array_push(v_snd_1265_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_fst_1264_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_fst_1260_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v_a_1253_ = v___x_1300_;
goto v___jp_1252_;
}
else
{
lean_object* v_paramIdx_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; 
v_paramIdx_1301_ = lean_ctor_get(v_val_1236_, 0);
v___x_1302_ = 0;
lean_inc(v_a_1295_);
lean_inc_ref(v_params_1290_);
lean_inc_ref(v_fst_1237_);
v___x_1303_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1237_, v_params_1238_, v_paramIdx_1301_, v_params_1290_, v_a_1295_, v___x_1302_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v_decl_1305_; uint8_t v_dependsOnDiscr_1306_; lean_object* v___x_1307_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v_decl_1305_ = lean_ctor_get(v_a_1304_, 0);
v_dependsOnDiscr_1306_ = lean_ctor_get_uint8(v_a_1304_, sizeof(void*)*1 + 1);
v___x_1307_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1269_, v_a_1295_, v___y_1248_);
lean_dec(v_a_1295_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_fvarId_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref_known(v___x_1307_, 1);
v_fvarId_1308_ = lean_ctor_get(v_decl_1305_, 0);
lean_inc(v_fvarId_1308_);
lean_inc_ref(v_decl_1305_);
v___x_1309_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_decl_1305_);
v___x_1310_ = lean_array_push(v_fst_1264_, v___x_1309_);
lean_inc(v_ctorName_1289_);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_ctorName_1289_, v_a_1304_, v_fst_1260_);
lean_inc_ref(v_params_1290_);
lean_inc(v_paramIdx_1301_);
lean_inc_ref(v_params_1238_);
v___x_1312_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1238_, v_paramIdx_1301_, v_params_1290_, v_dependsOnDiscr_1306_);
v___x_1313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_fvarId_1308_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
lean_inc_ref(v_a_1270_);
v___x_1314_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1270_, v___x_1313_);
v___x_1315_ = lean_array_push(v_snd_1265_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1310_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1311_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v_a_1253_ = v___x_1317_;
goto v___jp_1252_;
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_a_1304_);
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_dec(v_fst_1260_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1318_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1307_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1307_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_a_1295_);
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_dec(v_fst_1260_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1326_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1303_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1303_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_dec(v_fst_1260_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1334_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1294_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1294_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_dec(v_fst_1260_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1342_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1292_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1292_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_code_1350_; lean_object* v___x_1351_; 
v_code_1350_ = lean_ctor_get(v_a_1270_, 0);
lean_inc_ref(v_code_1350_);
v___x_1351_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1350_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1358_; lean_object* v___y_1360_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v_a_1408_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1358_ = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(v_snd_1239_);
v___x_1406_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0));
v___x_1407_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1358_, v___x_1406_, v___x_1235_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref(v___x_1407_);
v___y_1360_ = v_a_1408_;
goto v___jp_1359_;
v___jp_1353_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_inc_ref(v_a_1270_);
v___x_1354_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1270_, v_a_1352_);
v___x_1355_ = lean_array_push(v_snd_1265_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_fst_1264_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_fst_1260_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v_a_1253_ = v___x_1357_;
goto v___jp_1252_;
}
v___jp_1359_:
{
lean_object* v_fst_1361_; 
v_fst_1361_ = lean_ctor_get(v___y_1360_, 0);
lean_inc(v_fst_1361_);
lean_dec_ref(v___y_1360_);
if (lean_obj_tag(v_fst_1361_) == 0)
{
lean_dec(v___x_1358_);
lean_del_object(v___x_1267_);
lean_del_object(v___x_1262_);
goto v___jp_1353_;
}
else
{
lean_object* v_val_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1405_; 
v_val_1362_ = lean_ctor_get(v_fst_1361_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_fst_1361_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1364_ = v_fst_1361_;
v_isShared_1365_ = v_isSharedCheck_1405_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_val_1362_);
lean_dec(v_fst_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1405_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_unbox(v_val_1362_);
lean_dec(v_val_1362_);
if (v___x_1366_ == 0)
{
lean_del_object(v___x_1364_);
lean_dec(v___x_1358_);
lean_del_object(v___x_1267_);
lean_del_object(v___x_1262_);
goto v___jp_1353_;
}
else
{
lean_object* v_paramIdx_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_paramIdx_1367_ = lean_ctor_get(v_val_1236_, 0);
v___x_1368_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
lean_inc(v_a_1352_);
lean_inc_ref(v_fst_1237_);
v___x_1369_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1237_, v_params_1238_, v_paramIdx_1367_, v___x_1368_, v_a_1352_, v___x_1257_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v_decl_1371_; uint8_t v_dependsOnDiscr_1372_; lean_object* v___x_1373_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v_decl_1371_ = lean_ctor_get(v_a_1370_, 0);
lean_inc_ref(v_decl_1371_);
v_dependsOnDiscr_1372_ = lean_ctor_get_uint8(v_a_1370_, sizeof(void*)*1 + 1);
v___x_1373_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1269_, v_a_1352_, v___y_1248_);
lean_dec(v_a_1352_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1374_; 
lean_dec_ref_known(v___x_1373_, 1);
lean_inc(v___x_1235_);
v___x_1374_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1358_, v_a_1370_, v_fst_1260_, v___x_1235_);
lean_dec(v___x_1358_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
lean_inc_ref(v_decl_1371_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set_tag(v___x_1364_, 2);
lean_ctor_set(v___x_1364_, 0, v_decl_1371_);
v___x_1377_ = v___x_1364_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_decl_1371_);
v___x_1377_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; lean_object* v_a_1379_; 
v___x_1378_ = lean_array_push(v_fst_1264_, v___x_1377_);
v_a_1379_ = lean_ctor_get(v_a_1375_, 0);
lean_inc(v_a_1379_);
lean_dec(v_a_1375_);
lean_inc(v_paramIdx_1367_);
v___y_1272_ = v_dependsOnDiscr_1372_;
v___y_1273_ = v_paramIdx_1367_;
v___y_1274_ = v_decl_1371_;
v___y_1275_ = v___x_1368_;
v___y_1276_ = v___x_1378_;
v_a_1277_ = v_a_1379_;
goto v___jp_1271_;
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_decl_1371_);
lean_del_object(v___x_1364_);
lean_del_object(v___x_1267_);
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_del_object(v___x_1262_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1381_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1374_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1374_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_decl_1371_);
lean_dec(v_a_1370_);
lean_del_object(v___x_1364_);
lean_dec(v___x_1358_);
lean_del_object(v___x_1267_);
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_del_object(v___x_1262_);
lean_dec(v_fst_1260_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1389_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1373_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1373_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_del_object(v___x_1364_);
lean_dec(v___x_1358_);
lean_dec(v_a_1352_);
lean_del_object(v___x_1267_);
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_del_object(v___x_1262_);
lean_dec(v_fst_1260_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1397_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1369_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1369_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
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
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_del_object(v___x_1267_);
lean_dec(v_snd_1265_);
lean_dec(v_fst_1264_);
lean_del_object(v___x_1262_);
lean_dec(v_fst_1260_);
lean_dec_ref(v_params_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_val_1236_);
lean_dec(v___x_1235_);
lean_dec(v_discr_1234_);
v_a_1409_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1351_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1351_);
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
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
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
v___jp_1271_:
{
lean_object* v_fvarId_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v_fvarId_1278_ = lean_ctor_get(v___y_1274_, 0);
lean_inc(v_fvarId_1278_);
lean_dec_ref(v___y_1274_);
lean_inc_ref(v_params_1238_);
v___x_1279_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1238_, v___y_1273_, v___y_1275_, v___y_1272_);
v___x_1280_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_fvarId_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
lean_inc(v_a_1270_);
v___x_1281_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1270_, v___x_1280_);
v___x_1282_ = lean_array_push(v_snd_1265_, v___x_1281_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v___x_1282_);
lean_ctor_set(v___x_1267_, 0, v___y_1276_);
v___x_1284_ = v___x_1267_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___y_1276_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1284_);
lean_ctor_set(v___x_1262_, 0, v_a_1277_);
v___x_1286_ = v___x_1262_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1277_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
v_a_1253_ = v___x_1286_;
goto v___jp_1252_;
}
}
}
}
}
}
v___jp_1252_:
{
size_t v___x_1254_; size_t v___x_1255_; 
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_add(v_i_1242_, v___x_1254_);
v_i_1242_ = v___x_1255_;
v_b_1243_ = v_a_1253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object* v_decl_1419_, lean_object* v_k_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_fvarId_1429_; lean_object* v_params_1430_; lean_object* v_type_1431_; lean_object* v_value_1432_; lean_object* v___x_1433_; 
v_fvarId_1429_ = lean_ctor_get(v_decl_1419_, 0);
v_params_1430_ = lean_ctor_get(v_decl_1419_, 2);
lean_inc_ref(v_params_1430_);
v_type_1431_ = lean_ctor_get(v_decl_1419_, 3);
lean_inc_ref(v_type_1431_);
v_value_1432_ = lean_ctor_get(v_decl_1419_, 4);
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_1421_, v_fvarId_1429_);
if (lean_obj_tag(v___x_1433_) == 1)
{
lean_object* v_val_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1510_; 
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1510_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_val_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1510_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_ctorNames_1438_; 
v_ctorNames_1438_ = lean_ctor_get(v_val_1434_, 1);
lean_inc(v_ctorNames_1438_);
if (lean_obj_tag(v_ctorNames_1438_) == 0)
{
lean_object* v___x_1439_; lean_object* v_snd_1440_; lean_object* v_fst_1441_; lean_object* v_typeName_1442_; lean_object* v_resultType_1443_; lean_object* v_discr_1444_; lean_object* v_alts_1445_; lean_object* v___x_1446_; size_t v_sz_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1439_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_value_1432_);
v_snd_1440_ = lean_ctor_get(v___x_1439_, 1);
lean_inc(v_snd_1440_);
v_fst_1441_ = lean_ctor_get(v___x_1439_, 0);
lean_inc_n(v_fst_1441_, 2);
lean_dec_ref(v___x_1439_);
v_typeName_1442_ = lean_ctor_get(v_snd_1440_, 0);
lean_inc(v_typeName_1442_);
v_resultType_1443_ = lean_ctor_get(v_snd_1440_, 1);
lean_inc_ref(v_resultType_1443_);
v_discr_1444_ = lean_ctor_get(v_snd_1440_, 2);
lean_inc_n(v_discr_1444_, 2);
v_alts_1445_ = lean_ctor_get(v_snd_1440_, 3);
lean_inc_ref(v_alts_1445_);
v___x_1446_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1));
v_sz_1447_ = lean_array_size(v_alts_1445_);
v___x_1448_ = ((size_t)0ULL);
lean_inc_ref(v_params_1430_);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1444_, v_ctorNames_1438_, v_val_1434_, v_fst_1441_, v_params_1430_, v_snd_1440_, v_alts_1445_, v_sz_1447_, v___x_1448_, v___x_1446_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec_ref(v_alts_1445_);
lean_dec(v_snd_1440_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v_fst_1452_; lean_object* v_snd_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_fst_1456_; lean_object* v_snd_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1499_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = lean_st_ref_take(v_a_1422_);
v_fst_1452_ = lean_ctor_get(v_a_1450_, 0);
lean_inc(v_fst_1452_);
v_snd_1453_ = lean_ctor_get(v_a_1450_, 1);
lean_inc(v_snd_1453_);
lean_dec(v_a_1450_);
lean_inc(v_fvarId_1429_);
v___x_1454_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1429_, v_fst_1452_, v___x_1451_);
v___x_1455_ = lean_st_ref_set(v_a_1422_, v___x_1454_);
v_fst_1456_ = lean_ctor_get(v_snd_1453_, 0);
v_snd_1457_ = lean_ctor_get(v_snd_1453_, 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_snd_1453_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1459_ = v_snd_1453_;
v_isShared_1460_ = v_isSharedCheck_1499_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_snd_1457_);
lean_inc(v_fst_1456_);
lean_dec(v_snd_1453_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1499_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1461_ = 0;
v___x_1462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1462_, 0, v_typeName_1442_);
lean_ctor_set(v___x_1462_, 1, v_resultType_1443_);
lean_ctor_set(v___x_1462_, 2, v_discr_1444_);
lean_ctor_set(v___x_1462_, 3, v_snd_1457_);
v___x_1463_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
v___x_1464_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1461_, v_fst_1441_, v___x_1463_);
lean_dec(v_fst_1441_);
v___x_1465_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1461_, v_decl_1419_, v_type_1431_, v_params_1430_, v___x_1464_, v_a_1425_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1482_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1482_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1482_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set_tag(v___x_1459_, 2);
lean_ctor_set(v___x_1459_, 1, v_a_1468_);
lean_ctor_set(v___x_1459_, 0, v_a_1466_);
v___x_1473_ = v___x_1459_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1466_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1461_, v_fst_1456_, v___x_1473_);
lean_dec(v_fst_1456_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1474_);
v___x_1476_ = v___x_1436_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1476_);
v___x_1478_ = v___x_1470_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
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
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_a_1466_);
lean_del_object(v___x_1459_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1436_);
v_a_1483_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1467_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1467_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_del_object(v___x_1459_);
lean_dec(v_fst_1456_);
lean_del_object(v___x_1436_);
lean_dec_ref(v_k_1420_);
v_a_1491_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1465_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1465_);
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
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
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
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_discr_1444_);
lean_dec_ref(v_resultType_1443_);
lean_dec(v_typeName_1442_);
lean_dec(v_fst_1441_);
lean_del_object(v___x_1436_);
lean_dec_ref(v_type_1431_);
lean_dec_ref(v_params_1430_);
lean_dec_ref(v_k_1420_);
lean_dec_ref(v_decl_1419_);
v_a_1500_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1449_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1449_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_del_object(v___x_1436_);
lean_dec(v_val_1434_);
lean_dec_ref(v_type_1431_);
lean_dec_ref(v_params_1430_);
lean_dec_ref(v_k_1420_);
lean_dec_ref(v_decl_1419_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v___x_1433_);
lean_dec_ref(v_type_1431_);
lean_dec_ref(v_params_1430_);
lean_dec_ref(v_k_1420_);
lean_dec_ref(v_decl_1419_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object* v_code_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
switch(lean_obj_tag(v_code_1513_))
{
case 0:
{
lean_object* v_decl_1522_; lean_object* v_k_1523_; lean_object* v___x_1524_; 
v_decl_1522_ = lean_ctor_get(v_code_1513_, 0);
v_k_1523_ = lean_ctor_get(v_code_1513_, 1);
lean_inc_ref(v_k_1523_);
v___x_1524_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1523_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1551_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1551_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1551_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___y_1530_; size_t v___x_1546_; size_t v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_ptr_addr(v_k_1523_);
v___x_1547_ = lean_ptr_addr(v_a_1525_);
v___x_1548_ = lean_usize_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
v___y_1530_ = v___x_1548_;
goto v___jp_1529_;
}
else
{
size_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_ptr_addr(v_decl_1522_);
v___x_1550_ = lean_usize_dec_eq(v___x_1549_, v___x_1549_);
v___y_1530_ = v___x_1550_;
goto v___jp_1529_;
}
v___jp_1529_:
{
if (v___y_1530_ == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1540_; 
lean_inc_ref(v_decl_1522_);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_code_1513_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; lean_object* v_unused_1542_; 
v_unused_1541_ = lean_ctor_get(v_code_1513_, 1);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_code_1513_, 0);
lean_dec(v_unused_1542_);
v___x_1532_ = v_code_1513_;
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_code_1513_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 1, v_a_1525_);
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_decl_1522_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_a_1525_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1537_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1535_);
v___x_1537_ = v___x_1527_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v___x_1544_; 
lean_dec(v_a_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_code_1513_);
v___x_1544_ = v___x_1527_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_code_1513_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1513_, 2);
return v___x_1524_;
}
}
case 1:
{
lean_object* v_decl_1552_; lean_object* v_k_1553_; lean_object* v_params_1554_; lean_object* v_type_1555_; lean_object* v_value_1556_; lean_object* v___x_1557_; 
v_decl_1552_ = lean_ctor_get(v_code_1513_, 0);
v_k_1553_ = lean_ctor_get(v_code_1513_, 1);
v_params_1554_ = lean_ctor_get(v_decl_1552_, 2);
v_type_1555_ = lean_ctor_get(v_decl_1552_, 3);
v_value_1556_ = lean_ctor_get(v_decl_1552_, 4);
lean_inc_ref(v_value_1556_);
v___x_1557_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1556_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = 0;
lean_inc_ref(v_params_1554_);
lean_inc_ref(v_type_1555_);
lean_inc_ref(v_decl_1552_);
v___x_1560_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1559_, v_decl_1552_, v_type_1555_, v_params_1554_, v_a_1558_, v_a_1518_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
lean_inc_ref(v_k_1553_);
v___x_1562_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1553_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1590_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1590_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1590_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint8_t v___y_1568_; size_t v___x_1584_; size_t v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = lean_ptr_addr(v_k_1553_);
v___x_1585_ = lean_ptr_addr(v_a_1563_);
v___x_1586_ = lean_usize_dec_eq(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
v___y_1568_ = v___x_1586_;
goto v___jp_1567_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = lean_ptr_addr(v_decl_1552_);
v___x_1588_ = lean_ptr_addr(v_a_1561_);
v___x_1589_ = lean_usize_dec_eq(v___x_1587_, v___x_1588_);
v___y_1568_ = v___x_1589_;
goto v___jp_1567_;
}
v___jp_1567_:
{
if (v___y_1568_ == 0)
{
lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1578_; 
v_isSharedCheck_1578_ = !lean_is_exclusive(v_code_1513_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; lean_object* v_unused_1580_; 
v_unused_1579_ = lean_ctor_get(v_code_1513_, 1);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v_code_1513_, 0);
lean_dec(v_unused_1580_);
v___x_1570_ = v_code_1513_;
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
else
{
lean_dec(v_code_1513_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v_a_1563_);
lean_ctor_set(v___x_1570_, 0, v_a_1561_);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1561_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_a_1563_);
v___x_1573_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1575_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1573_);
v___x_1575_ = v___x_1565_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v___x_1582_; 
lean_dec(v_a_1563_);
lean_dec(v_a_1561_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_code_1513_);
v___x_1582_ = v___x_1565_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_code_1513_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
else
{
lean_dec(v_a_1561_);
lean_dec_ref_known(v_code_1513_, 2);
return v___x_1562_;
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref_known(v_code_1513_, 2);
v_a_1591_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1560_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1560_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1513_, 2);
return v___x_1557_;
}
}
case 2:
{
lean_object* v_decl_1599_; lean_object* v_k_1600_; lean_object* v___x_1601_; 
v_decl_1599_ = lean_ctor_get(v_code_1513_, 0);
v_k_1600_ = lean_ctor_get(v_code_1513_, 1);
lean_inc_ref(v_k_1600_);
lean_inc_ref(v_decl_1599_);
v___x_1601_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1599_, v_k_1600_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1655_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1655_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1655_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
if (lean_obj_tag(v_a_1602_) == 1)
{
lean_object* v_val_1606_; lean_object* v___x_1608_; 
lean_dec_ref_known(v_code_1513_, 2);
v_val_1606_ = lean_ctor_get(v_a_1602_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v_a_1602_, 1);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v_val_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_val_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
else
{
lean_object* v_params_1610_; lean_object* v_type_1611_; lean_object* v_value_1612_; lean_object* v___x_1613_; 
lean_del_object(v___x_1604_);
lean_dec(v_a_1602_);
v_params_1610_ = lean_ctor_get(v_decl_1599_, 2);
v_type_1611_ = lean_ctor_get(v_decl_1599_, 3);
v_value_1612_ = lean_ctor_get(v_decl_1599_, 4);
lean_inc_ref(v_value_1612_);
v___x_1613_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1612_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___x_1615_ = 0;
lean_inc_ref(v_params_1610_);
lean_inc_ref(v_type_1611_);
lean_inc_ref(v_decl_1599_);
v___x_1616_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1615_, v_decl_1599_, v_type_1611_, v_params_1610_, v_a_1614_, v_a_1518_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
lean_inc_ref(v_k_1600_);
v___x_1618_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1600_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1646_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1646_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1646_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
uint8_t v___y_1624_; size_t v___x_1640_; size_t v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = lean_ptr_addr(v_k_1600_);
v___x_1641_ = lean_ptr_addr(v_a_1619_);
v___x_1642_ = lean_usize_dec_eq(v___x_1640_, v___x_1641_);
if (v___x_1642_ == 0)
{
v___y_1624_ = v___x_1642_;
goto v___jp_1623_;
}
else
{
size_t v___x_1643_; size_t v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_ptr_addr(v_decl_1599_);
v___x_1644_ = lean_ptr_addr(v_a_1617_);
v___x_1645_ = lean_usize_dec_eq(v___x_1643_, v___x_1644_);
v___y_1624_ = v___x_1645_;
goto v___jp_1623_;
}
v___jp_1623_:
{
if (v___y_1624_ == 0)
{
lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1634_; 
v_isSharedCheck_1634_ = !lean_is_exclusive(v_code_1513_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1635_ = lean_ctor_get(v_code_1513_, 1);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_code_1513_, 0);
lean_dec(v_unused_1636_);
v___x_1626_ = v_code_1513_;
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v_code_1513_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v_a_1619_);
lean_ctor_set(v___x_1626_, 0, v_a_1617_);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1617_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_a_1619_);
v___x_1629_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1629_);
v___x_1631_ = v___x_1621_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_object* v___x_1638_; 
lean_dec(v_a_1619_);
lean_dec(v_a_1617_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_code_1513_);
v___x_1638_ = v___x_1621_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_code_1513_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
else
{
lean_dec(v_a_1617_);
lean_dec_ref_known(v_code_1513_, 2);
return v___x_1618_;
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref_known(v_code_1513_, 2);
v_a_1647_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1616_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1616_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1513_, 2);
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref_known(v_code_1513_, 2);
v_a_1656_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1601_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1601_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1664_; lean_object* v_args_1665_; lean_object* v___x_1666_; 
v_fvarId_1664_ = lean_ctor_get(v_code_1513_, 0);
v_args_1665_ = lean_ctor_get(v_code_1513_, 1);
lean_inc_ref(v_args_1665_);
v___x_1666_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1664_, v_args_1665_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1678_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1678_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1678_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
if (lean_obj_tag(v_a_1667_) == 1)
{
lean_object* v_val_1671_; lean_object* v___x_1673_; 
lean_dec_ref_known(v_code_1513_, 2);
v_val_1671_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_val_1671_);
lean_dec_ref_known(v_a_1667_, 1);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_val_1671_);
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_val_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_a_1667_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_code_1513_);
v___x_1676_ = v___x_1669_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_code_1513_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref_known(v_code_1513_, 2);
v_a_1679_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1666_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1666_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
case 4:
{
lean_object* v_cases_1687_; lean_object* v_typeName_1688_; lean_object* v_resultType_1689_; lean_object* v_discr_1690_; lean_object* v_alts_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1730_; 
v_cases_1687_ = lean_ctor_get(v_code_1513_, 0);
lean_inc_ref(v_cases_1687_);
v_typeName_1688_ = lean_ctor_get(v_cases_1687_, 0);
v_resultType_1689_ = lean_ctor_get(v_cases_1687_, 1);
v_discr_1690_ = lean_ctor_get(v_cases_1687_, 2);
v_alts_1691_ = lean_ctor_get(v_cases_1687_, 3);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_cases_1687_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1693_ = v_cases_1687_;
v_isShared_1694_ = v_isSharedCheck_1730_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_alts_1691_);
lean_inc(v_discr_1690_);
lean_inc(v_resultType_1689_);
lean_inc(v_typeName_1688_);
lean_dec(v_cases_1687_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1730_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1691_);
lean_inc(v_discr_1690_);
v___x_1696_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1690_, v___x_1695_, v_alts_1691_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1721_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1721_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1721_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
size_t v___x_1701_; size_t v___x_1702_; uint8_t v___x_1703_; 
v___x_1701_ = lean_ptr_addr(v_alts_1691_);
lean_dec_ref(v_alts_1691_);
v___x_1702_ = lean_ptr_addr(v_a_1697_);
v___x_1703_ = lean_usize_dec_eq(v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1716_; 
v_isSharedCheck_1716_ = !lean_is_exclusive(v_code_1513_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v_code_1513_, 0);
lean_dec(v_unused_1717_);
v___x_1705_ = v_code_1513_;
v_isShared_1706_ = v_isSharedCheck_1716_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_code_1513_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1716_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 3, v_a_1697_);
v___x_1708_ = v___x_1693_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_typeName_1688_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_resultType_1689_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_discr_1690_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_a_1697_);
v___x_1708_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1710_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1708_);
v___x_1710_ = v___x_1705_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1712_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1710_);
v___x_1712_ = v___x_1699_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
else
{
lean_object* v___x_1719_; 
lean_dec(v_a_1697_);
lean_del_object(v___x_1693_);
lean_dec(v_discr_1690_);
lean_dec_ref(v_resultType_1689_);
lean_dec(v_typeName_1688_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v_code_1513_);
v___x_1719_ = v___x_1699_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_code_1513_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_del_object(v___x_1693_);
lean_dec_ref(v_alts_1691_);
lean_dec(v_discr_1690_);
lean_dec_ref(v_resultType_1689_);
lean_dec(v_typeName_1688_);
lean_dec_ref_known(v_code_1513_, 1);
v_a_1722_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1696_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1696_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
default: 
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_code_1513_);
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object* v_discr_1732_, lean_object* v_i_1733_, lean_object* v_as_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_array_get_size(v_as_1734_);
v___x_1744_ = lean_nat_dec_lt(v_i_1733_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_dec(v_i_1733_);
lean_dec(v_discr_1732_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_as_1734_);
return v___x_1745_;
}
else
{
lean_object* v_a_1746_; lean_object* v_a_1748_; 
v_a_1746_ = lean_array_fget_borrowed(v_as_1734_, v_i_1733_);
if (lean_obj_tag(v_a_1746_) == 0)
{
lean_object* v_ctorName_1759_; lean_object* v_params_1760_; lean_object* v_code_1761_; lean_object* v___x_1762_; 
v_ctorName_1759_ = lean_ctor_get(v_a_1746_, 0);
v_params_1760_ = lean_ctor_get(v_a_1746_, 1);
v_code_1761_ = lean_ctor_get(v_a_1746_, 2);
lean_inc_ref(v_params_1760_);
lean_inc(v_ctorName_1759_);
lean_inc(v_discr_1732_);
v___x_1762_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1732_, v_ctorName_1759_, v_params_1760_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
lean_inc_ref(v_code_1761_);
v___x_1764_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1761_, v___y_1735_, v___y_1736_, v_a_1763_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v_a_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
lean_inc_ref(v_a_1746_);
v___x_1766_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1746_, v_a_1765_);
v_a_1748_ = v___x_1766_;
goto v___jp_1747_;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref(v_as_1734_);
lean_dec(v_i_1733_);
lean_dec(v_discr_1732_);
v_a_1767_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1764_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1764_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v_as_1734_);
lean_dec(v_i_1733_);
lean_dec(v_discr_1732_);
v_a_1775_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1762_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1762_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_code_1783_; lean_object* v___x_1784_; 
v_code_1783_ = lean_ctor_get(v_a_1746_, 0);
lean_inc_ref(v_code_1783_);
v___x_1784_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1783_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
lean_inc_ref(v_a_1746_);
v___x_1786_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1746_, v_a_1785_);
v_a_1748_ = v___x_1786_;
goto v___jp_1747_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_as_1734_);
lean_dec(v_i_1733_);
lean_dec(v_discr_1732_);
v_a_1787_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1784_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1784_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
v___jp_1747_:
{
size_t v___x_1749_; size_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1749_ = lean_ptr_addr(v_a_1746_);
v___x_1750_ = lean_ptr_addr(v_a_1748_);
v___x_1751_ = lean_usize_dec_eq(v___x_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_i_1733_, v___x_1752_);
v___x_1754_ = lean_array_fset(v_as_1734_, v_i_1733_, v_a_1748_);
lean_dec(v_i_1733_);
v_i_1733_ = v___x_1753_;
v_as_1734_ = v___x_1754_;
goto _start;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v_a_1748_);
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_nat_add(v_i_1733_, v___x_1756_);
lean_dec(v_i_1733_);
v_i_1733_ = v___x_1757_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object* v_discr_1795_, lean_object* v_i_1796_, lean_object* v_as_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1795_, v_i_1796_, v_as_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec(v___y_1798_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object* v_decl_1807_, lean_object* v_k_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1807_, v_k_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec(v_a_1809_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object** _args){
lean_object* v_discr_1818_ = _args[0];
lean_object* v___x_1819_ = _args[1];
lean_object* v_val_1820_ = _args[2];
lean_object* v_fst_1821_ = _args[3];
lean_object* v_params_1822_ = _args[4];
lean_object* v_snd_1823_ = _args[5];
lean_object* v_as_1824_ = _args[6];
lean_object* v_sz_1825_ = _args[7];
lean_object* v_i_1826_ = _args[8];
lean_object* v_b_1827_ = _args[9];
lean_object* v___y_1828_ = _args[10];
lean_object* v___y_1829_ = _args[11];
lean_object* v___y_1830_ = _args[12];
lean_object* v___y_1831_ = _args[13];
lean_object* v___y_1832_ = _args[14];
lean_object* v___y_1833_ = _args[15];
lean_object* v___y_1834_ = _args[16];
lean_object* v___y_1835_ = _args[17];
_start:
{
size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1825_);
lean_dec(v_sz_1825_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1826_);
lean_dec(v_i_1826_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1818_, v___x_1819_, v_val_1820_, v_fst_1821_, v_params_1822_, v_snd_1823_, v_as_1824_, v_sz_boxed_1836_, v_i_boxed_1837_, v_b_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v_as_1824_);
lean_dec_ref(v_snd_1823_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object* v_code_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec(v_a_1840_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object* v___x_1849_, lean_object* v_a_1850_, lean_object* v_init_1851_, lean_object* v_x_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1849_, v_a_1850_, v_init_1851_, v_x_1852_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object* v___x_1862_, lean_object* v_a_1863_, lean_object* v_init_1864_, lean_object* v_x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(v___x_1862_, v_a_1863_, v_init_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec(v___x_1862_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
lean_ctor_set(v___x_1880_, 2, v___x_1879_);
lean_ctor_set(v___x_1880_, 3, v___x_1879_);
lean_ctor_set(v___x_1880_, 4, v___x_1878_);
lean_ctor_set(v___x_1880_, 5, v___x_1878_);
lean_ctor_set(v___x_1880_, 6, v___x_1878_);
lean_ctor_set(v___x_1880_, 7, v___x_1878_);
lean_ctor_set(v___x_1880_, 8, v___x_1878_);
lean_ctor_set(v___x_1880_, 9, v___x_1878_);
return v___x_1880_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1881_; double v___x_1882_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = lean_float_of_nat(v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object* v_cls_1886_, lean_object* v_msg_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_options_1893_; lean_object* v_ref_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_options_1893_ = lean_ctor_get(v___y_1890_, 2);
v_ref_1894_ = lean_ctor_get(v___y_1890_, 5);
v___x_1895_ = lean_st_ref_get(v___y_1891_);
v___x_1896_ = lean_st_ref_get(v___y_1889_);
v___x_1897_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1888_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1956_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1956_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1956_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_env_1902_; lean_object* v_lctx_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1954_; 
v_env_1902_ = lean_ctor_get(v___x_1895_, 0);
lean_inc_ref(v_env_1902_);
lean_dec(v___x_1895_);
v_lctx_1903_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v___x_1896_, 1);
lean_dec(v_unused_1955_);
v___x_1905_ = v___x_1896_;
v_isShared_1906_ = v_isSharedCheck_1954_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_lctx_1903_);
lean_dec(v___x_1896_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1954_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_traceState_1909_; lean_object* v_env_1910_; lean_object* v_nextMacroScope_1911_; lean_object* v_ngen_1912_; lean_object* v_auxDeclNGen_1913_; lean_object* v_cache_1914_; lean_object* v_messages_1915_; lean_object* v_infoState_1916_; lean_object* v_snapshotTasks_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1953_; 
v___x_1907_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2);
v___x_1908_ = lean_st_ref_take(v___y_1891_);
v_traceState_1909_ = lean_ctor_get(v___x_1908_, 4);
v_env_1910_ = lean_ctor_get(v___x_1908_, 0);
v_nextMacroScope_1911_ = lean_ctor_get(v___x_1908_, 1);
v_ngen_1912_ = lean_ctor_get(v___x_1908_, 2);
v_auxDeclNGen_1913_ = lean_ctor_get(v___x_1908_, 3);
v_cache_1914_ = lean_ctor_get(v___x_1908_, 5);
v_messages_1915_ = lean_ctor_get(v___x_1908_, 6);
v_infoState_1916_ = lean_ctor_get(v___x_1908_, 7);
v_snapshotTasks_1917_ = lean_ctor_get(v___x_1908_, 8);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1919_ = v___x_1908_;
v_isShared_1920_ = v_isSharedCheck_1953_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_snapshotTasks_1917_);
lean_inc(v_infoState_1916_);
lean_inc(v_messages_1915_);
lean_inc(v_cache_1914_);
lean_inc(v_traceState_1909_);
lean_inc(v_auxDeclNGen_1913_);
lean_inc(v_ngen_1912_);
lean_inc(v_nextMacroScope_1911_);
lean_inc(v_env_1910_);
lean_dec(v___x_1908_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1953_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
uint64_t v_tid_1921_; lean_object* v_traces_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1952_; 
v_tid_1921_ = lean_ctor_get_uint64(v_traceState_1909_, sizeof(void*)*1);
v_traces_1922_ = lean_ctor_get(v_traceState_1909_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_traceState_1909_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1924_ = v_traceState_1909_;
v_isShared_1925_ = v_isSharedCheck_1952_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_traces_1922_);
lean_dec(v_traceState_1909_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1952_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1926_ = lean_unbox(v_a_1898_);
lean_dec(v_a_1898_);
v___x_1927_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1903_, v___x_1926_);
lean_dec_ref(v_lctx_1903_);
lean_inc_ref(v_options_1893_);
v___x_1928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1928_, 0, v_env_1902_);
lean_ctor_set(v___x_1928_, 1, v___x_1907_);
lean_ctor_set(v___x_1928_, 2, v___x_1927_);
lean_ctor_set(v___x_1928_, 3, v_options_1893_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 3);
lean_ctor_set(v___x_1905_, 1, v_msg_1887_);
lean_ctor_set(v___x_1905_, 0, v___x_1928_);
v___x_1930_ = v___x_1905_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_msg_1887_);
v___x_1930_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; double v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3);
v___x_1933_ = 0;
v___x_1934_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4));
v___x_1935_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1935_, 0, v_cls_1886_);
lean_ctor_set(v___x_1935_, 1, v___x_1931_);
lean_ctor_set(v___x_1935_, 2, v___x_1934_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3, v___x_1932_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3 + 8, v___x_1932_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*3 + 16, v___x_1933_);
v___x_1936_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5));
v___x_1937_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1930_);
lean_ctor_set(v___x_1937_, 2, v___x_1936_);
lean_inc(v_ref_1894_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_ref_1894_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_PersistentArray_push___redArg(v_traces_1922_, v___x_1938_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1939_);
v___x_1941_ = v___x_1924_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1939_);
lean_ctor_set_uint64(v_reuseFailAlloc_1950_, sizeof(void*)*1, v_tid_1921_);
v___x_1941_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 4, v___x_1941_);
v___x_1943_ = v___x_1919_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_env_1910_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_nextMacroScope_1911_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_ngen_1912_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_auxDeclNGen_1913_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1949_, 5, v_cache_1914_);
lean_ctor_set(v_reuseFailAlloc_1949_, 6, v_messages_1915_);
lean_ctor_set(v_reuseFailAlloc_1949_, 7, v_infoState_1916_);
lean_ctor_set(v_reuseFailAlloc_1949_, 8, v_snapshotTasks_1917_);
v___x_1943_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1944_ = lean_st_ref_set(v___y_1891_, v___x_1943_);
v___x_1945_ = lean_box(0);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1945_);
v___x_1947_ = v___x_1900_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
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
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v___x_1896_);
lean_dec(v___x_1895_);
lean_dec_ref(v_msg_1887_);
lean_dec(v_cls_1886_);
v_a_1957_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1897_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1897_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object* v_cls_1965_, lean_object* v_msg_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v_cls_1965_, v_msg_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object* v_init_1973_, lean_object* v_x_1974_){
_start:
{
if (lean_obj_tag(v_x_1974_) == 0)
{
lean_object* v_k_1975_; lean_object* v_v_1976_; lean_object* v_l_1977_; lean_object* v_r_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_k_1975_ = lean_ctor_get(v_x_1974_, 1);
v_v_1976_ = lean_ctor_get(v_x_1974_, 2);
v_l_1977_ = lean_ctor_get(v_x_1974_, 3);
v_r_1978_ = lean_ctor_get(v_x_1974_, 4);
v___x_1979_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_1973_, v_r_1978_);
lean_inc(v_v_1976_);
lean_inc(v_k_1975_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_k_1975_);
lean_ctor_set(v___x_1980_, 1, v_v_1976_);
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1979_);
v_init_1973_ = v___x_1981_;
v_x_1974_ = v_l_1977_;
goto _start;
}
else
{
return v_init_1973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object* v_init_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_1983_, v_x_1984_);
lean_dec(v_x_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
if (lean_obj_tag(v_a_1986_) == 0)
{
lean_object* v___x_1988_; 
v___x_1988_ = l_List_reverse___redArg(v_a_1987_);
return v___x_1988_;
}
else
{
lean_object* v_head_1989_; lean_object* v_tail_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1999_; 
v_head_1989_ = lean_ctor_get(v_a_1986_, 0);
v_tail_1990_ = lean_ctor_get(v_a_1986_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_a_1986_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1992_ = v_a_1986_;
v_isShared_1993_ = v_isSharedCheck_1999_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_tail_1990_);
lean_inc(v_head_1989_);
lean_dec(v_a_1986_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1999_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = l_Lean_MessageData_ofName(v_head_1989_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_a_1987_);
lean_ctor_set(v___x_1992_, 0, v___x_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_a_1987_);
v___x_1996_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
v_a_1986_ = v_tail_1990_;
v_a_1987_ = v___x_1996_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object* v_init_2000_, lean_object* v_x_2001_){
_start:
{
if (lean_obj_tag(v_x_2001_) == 0)
{
lean_object* v_k_2002_; lean_object* v_l_2003_; lean_object* v_r_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_k_2002_ = lean_ctor_get(v_x_2001_, 1);
v_l_2003_ = lean_ctor_get(v_x_2001_, 3);
v_r_2004_ = lean_ctor_get(v_x_2001_, 4);
v___x_2005_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_2000_, v_r_2004_);
lean_inc(v_k_2002_);
v___x_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_k_2002_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v_init_2000_ = v___x_2006_;
v_x_2001_ = v_l_2003_;
goto _start;
}
else
{
return v_init_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object* v_init_2008_, lean_object* v_x_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_2008_, v_x_2009_);
lean_dec(v_x_2009_);
return v_res_2010_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0));
v___x_2013_ = l_Lean_stringToMessageData(v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(lean_object* v_as_x27_2014_, lean_object* v_b_2015_){
_start:
{
if (lean_obj_tag(v_as_x27_2014_) == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_b_2015_);
return v___x_2017_;
}
else
{
lean_object* v_head_2018_; lean_object* v_snd_2019_; lean_object* v_tail_2020_; lean_object* v_fst_2021_; lean_object* v_ctorNames_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_head_2018_ = lean_ctor_get(v_as_x27_2014_, 0);
v_snd_2019_ = lean_ctor_get(v_head_2018_, 1);
v_tail_2020_ = lean_ctor_get(v_as_x27_2014_, 1);
v_fst_2021_ = lean_ctor_get(v_head_2018_, 0);
v_ctorNames_2022_ = lean_ctor_get(v_snd_2019_, 1);
lean_inc(v_fst_2021_);
v___x_2023_ = l_Lean_mkFVar(v_fst_2021_);
v___x_2024_ = l_Lean_MessageData_ofExpr(v___x_2023_);
v___x_2025_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_box(0);
v___x_2028_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v___x_2027_, v_ctorNames_2022_);
v___x_2029_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(v___x_2028_, v___x_2027_);
v___x_2030_ = l_Lean_MessageData_ofList(v___x_2029_);
v___x_2031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2026_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = l_Lean_indentD(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_b_2015_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v_as_x27_2014_ = v_tail_2020_;
v_b_2015_ = v___x_2033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___boxed(lean_object* v_as_x27_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2035_, v_b_2036_);
lean_dec(v_as_x27_2035_);
return v_res_2038_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2050_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5));
v___x_2051_ = l_Lean_Name_append(v___x_2050_, v___x_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8));
v___x_2056_ = l_Lean_MessageData_ofFormat(v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object* v_code_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v___x_2063_; 
lean_inc_ref(v_code_2057_);
v___x_2063_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2116_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2116_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2116_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
uint8_t v___x_2091_; 
lean_inc(v_a_2064_);
v___x_2091_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_a_2064_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
lean_dec(v_a_2064_);
lean_dec_ref(v_code_2057_);
v___x_2092_ = lean_box(0);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2092_);
v___x_2094_ = v___x_2066_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
else
{
lean_object* v_options_2096_; uint8_t v_hasTrace_2097_; 
lean_del_object(v___x_2066_);
v_options_2096_ = lean_ctor_get(v_a_2060_, 2);
v_hasTrace_2097_ = lean_ctor_get_uint8(v_options_2096_, sizeof(void*)*1);
if (v_hasTrace_2097_ == 0)
{
goto v___jp_2068_;
}
else
{
lean_object* v_inheritedTraceOptions_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_inheritedTraceOptions_2098_ = lean_ctor_get(v_a_2060_, 13);
v___x_2099_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2100_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6);
v___x_2101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2098_, v_options_2096_, v___x_2100_);
if (v___x_2101_ == 0)
{
goto v___jp_2068_;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_a_2106_; lean_object* v___x_2107_; 
v___x_2102_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9);
v___x_2103_ = lean_box(0);
v___x_2104_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v___x_2103_, v_a_2064_);
v___x_2105_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v___x_2104_, v___x_2102_);
lean_dec(v___x_2104_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v___x_2099_, v_a_2106_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_dec_ref_known(v___x_2107_, 1);
goto v___jp_2068_;
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_a_2064_);
lean_dec_ref(v_code_2057_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
v___jp_2068_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_box(1);
v___x_2070_ = lean_st_mk_ref(v___x_2069_);
v___x_2071_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_2072_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_2057_, v_a_2064_, v___x_2070_, v___x_2071_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2064_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2082_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2082_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2082_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2077_ = lean_st_ref_get(v___x_2070_);
lean_dec(v___x_2070_);
lean_dec(v___x_2077_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_a_2073_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2078_);
v___x_2080_ = v___x_2075_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v___x_2070_);
v_a_2083_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2072_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2072_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v_code_2057_);
v_a_2117_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2063_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2063_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object* v_code_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v_code_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object* v_as_2132_, lean_object* v_as_x27_2133_, lean_object* v_b_2134_, lean_object* v_a_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2133_, v_b_2134_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object* v_as_2142_, lean_object* v_as_x27_2143_, lean_object* v_b_2144_, lean_object* v_a_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v_as_2142_, v_as_x27_2143_, v_b_2144_, v_a_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v_as_x27_2143_);
lean_dec(v_as_2142_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2225_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2226_ = 0;
v___x_2227_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_));
v___x_2228_ = l_Lean_registerTraceClass(v___x_2225_, v___x_2226_, v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
return v_res_2230_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default);
l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo);
res = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
}
#ifdef __cplusplus
}
#endif
