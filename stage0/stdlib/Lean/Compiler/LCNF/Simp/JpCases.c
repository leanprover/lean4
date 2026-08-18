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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__2;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object* v_init_102_, lean_object* v_x_103_){
_start:
{
if (lean_obj_tag(v_x_103_) == 0)
{
lean_object* v_v_104_; lean_object* v_l_105_; lean_object* v_r_106_; lean_object* v___x_107_; 
v_v_104_ = lean_ctor_get(v_x_103_, 2);
v_l_105_ = lean_ctor_get(v_x_103_, 3);
v_r_106_ = lean_ctor_get(v_x_103_, 4);
v___x_107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_102_, v_l_105_);
if (lean_obj_tag(v___x_107_) == 0)
{
return v___x_107_;
}
else
{
lean_object* v_ctorNames_108_; 
lean_dec_ref_known(v___x_107_, 1);
v_ctorNames_108_ = lean_ctor_get(v_v_104_, 1);
if (lean_obj_tag(v_ctorNames_108_) == 0)
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2));
return v___x_109_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v_init_102_ = v___x_110_;
v_x_103_ = v_r_106_;
goto _start;
}
}
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_init_102_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___boxed(lean_object* v_init_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_113_, v_x_114_);
lean_dec(v_x_114_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(lean_object* v_info_116_){
_start:
{
lean_object* v___y_118_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_a_125_; 
v___x_123_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v___x_124_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v___x_123_, v_info_116_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref(v___x_124_);
v___y_118_ = v_a_125_;
goto v___jp_117_;
v___jp_117_:
{
lean_object* v_fst_119_; 
v_fst_119_ = lean_ctor_get(v___y_118_, 0);
lean_inc(v_fst_119_);
lean_dec_ref(v___y_118_);
if (lean_obj_tag(v_fst_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
else
{
lean_object* v_val_121_; uint8_t v___x_122_; 
v_val_121_ = lean_ctor_get(v_fst_119_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v_fst_119_, 1);
v___x_122_ = lean_unbox(v_val_121_);
lean_dec(v_val_121_);
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(lean_object* v_info_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_info_126_);
lean_dec(v_info_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(lean_object* v_t_129_, lean_object* v_k_130_){
_start:
{
if (lean_obj_tag(v_t_129_) == 0)
{
lean_object* v_k_131_; lean_object* v_v_132_; lean_object* v_l_133_; lean_object* v_r_134_; uint8_t v___x_135_; 
v_k_131_ = lean_ctor_get(v_t_129_, 1);
v_v_132_ = lean_ctor_get(v_t_129_, 2);
v_l_133_ = lean_ctor_get(v_t_129_, 3);
v_r_134_ = lean_ctor_get(v_t_129_, 4);
v___x_135_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_130_, v_k_131_);
switch(v___x_135_)
{
case 0:
{
v_t_129_ = v_l_133_;
goto _start;
}
case 1:
{
lean_object* v___x_137_; 
lean_inc(v_v_132_);
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_v_132_);
return v___x_137_;
}
default: 
{
v_t_129_ = v_r_134_;
goto _start;
}
}
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(lean_object* v_t_140_, lean_object* v_k_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_140_, v_k_141_);
lean_dec(v_k_141_);
lean_dec(v_t_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(lean_object* v_code_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
switch(lean_obj_tag(v_code_143_))
{
case 0:
{
lean_object* v_k_151_; 
v_k_151_ = lean_ctor_get(v_code_143_, 1);
lean_inc_ref(v_k_151_);
lean_dec_ref_known(v_code_143_, 2);
v_code_143_ = v_k_151_;
goto _start;
}
case 1:
{
lean_object* v_decl_153_; lean_object* v_k_154_; lean_object* v_value_155_; lean_object* v___x_156_; 
v_decl_153_ = lean_ctor_get(v_code_143_, 0);
lean_inc_ref(v_decl_153_);
v_k_154_ = lean_ctor_get(v_code_143_, 1);
lean_inc_ref(v_k_154_);
lean_dec_ref_known(v_code_143_, 2);
v_value_155_ = lean_ctor_get(v_decl_153_, 4);
lean_inc_ref(v_value_155_);
lean_dec_ref(v_decl_153_);
v___x_156_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_155_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_dec_ref_known(v___x_156_, 1);
v_code_143_ = v_k_154_;
goto _start;
}
else
{
lean_dec_ref(v_k_154_);
return v___x_156_;
}
}
case 2:
{
lean_object* v_decl_158_; lean_object* v_k_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_192_; 
v_decl_158_ = lean_ctor_get(v_code_143_, 0);
v_k_159_ = lean_ctor_get(v_code_143_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_code_143_);
if (v_isSharedCheck_192_ == 0)
{
v___x_161_ = v_code_143_;
v_isShared_162_ = v_isSharedCheck_192_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_k_159_);
lean_inc(v_decl_158_);
lean_dec(v_code_143_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_192_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___x_173_; 
v___x_173_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_158_, v_a_146_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
if (lean_obj_tag(v_a_174_) == 1)
{
lean_object* v_val_175_; lean_object* v___x_176_; lean_object* v_fvarId_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v_val_175_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v_a_174_, 1);
v___x_176_ = lean_st_ref_take(v_a_144_);
v_fvarId_177_ = lean_ctor_get(v_decl_158_, 0);
v___x_178_ = l_Lean_NameSet_empty;
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 0);
lean_ctor_set(v___x_161_, 1, v___x_178_);
lean_ctor_set(v___x_161_, 0, v_val_175_);
v___x_180_ = v___x_161_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_val_175_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_183_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_inc(v_fvarId_177_);
v___x_181_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_177_, v___x_180_, v___x_176_);
v___x_182_ = lean_st_ref_put(v_a_144_, v___x_181_);
v___y_164_ = v_a_144_;
v___y_165_ = v_a_145_;
v___y_166_ = v_a_146_;
v___y_167_ = v_a_147_;
v___y_168_ = v_a_148_;
v___y_169_ = v_a_149_;
goto v___jp_163_;
}
}
else
{
lean_dec(v_a_174_);
lean_del_object(v___x_161_);
v___y_164_ = v_a_144_;
v___y_165_ = v_a_145_;
v___y_166_ = v_a_146_;
v___y_167_ = v_a_147_;
v___y_168_ = v_a_148_;
v___y_169_ = v_a_149_;
goto v___jp_163_;
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_del_object(v___x_161_);
lean_dec_ref(v_k_159_);
lean_dec_ref(v_decl_158_);
v_a_184_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_173_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_173_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
v___jp_163_:
{
lean_object* v_value_170_; lean_object* v___x_171_; 
v_value_170_ = lean_ctor_get(v_decl_158_, 4);
lean_inc_ref(v_value_170_);
lean_dec_ref(v_decl_158_);
v___x_171_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_170_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_dec_ref_known(v___x_171_, 1);
v_code_143_ = v_k_159_;
v_a_144_ = v___y_164_;
v_a_145_ = v___y_165_;
v_a_146_ = v___y_166_;
v_a_147_ = v___y_167_;
v_a_148_ = v___y_168_;
v_a_149_ = v___y_169_;
goto _start;
}
else
{
lean_dec_ref(v_k_159_);
return v___x_171_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_193_; lean_object* v_args_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_fvarId_193_ = lean_ctor_get(v_code_143_, 0);
lean_inc(v_fvarId_193_);
v_args_194_ = lean_ctor_get(v_code_143_, 1);
lean_inc_ref(v_args_194_);
lean_dec_ref_known(v_code_143_, 2);
v___x_195_ = lean_st_ref_get(v_a_144_);
v___x_196_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_195_, v_fvarId_193_);
lean_dec(v___x_195_);
if (lean_obj_tag(v___x_196_) == 1)
{
lean_object* v_val_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_244_; 
v_val_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_244_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_244_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_val_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_244_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_paramIdx_201_; lean_object* v_ctorNames_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_243_; 
v_paramIdx_201_ = lean_ctor_get(v_val_197_, 0);
v_ctorNames_202_ = lean_ctor_get(v_val_197_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_val_197_);
if (v_isSharedCheck_243_ == 0)
{
v___x_204_ = v_val_197_;
v_isShared_205_ = v_isSharedCheck_243_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_ctorNames_202_);
lean_inc(v_paramIdx_201_);
lean_dec(v_val_197_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_243_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_box(0);
v___x_207_ = lean_array_get(v___x_206_, v_args_194_, v_paramIdx_201_);
lean_dec_ref(v_args_194_);
if (lean_obj_tag(v___x_207_) == 1)
{
lean_object* v_fvarId_208_; lean_object* v___x_209_; 
lean_del_object(v___x_199_);
v_fvarId_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_fvarId_208_);
lean_dec_ref_known(v___x_207_, 1);
v___x_209_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(v_fvarId_208_, v_a_145_, v_a_147_, v_a_149_);
lean_dec(v_fvarId_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_230_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_230_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_230_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_230_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
if (lean_obj_tag(v_a_210_) == 1)
{
lean_object* v_val_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v_val_214_ = lean_ctor_get(v_a_210_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v_a_210_, 1);
v___x_215_ = lean_st_ref_take(v_a_144_);
v___x_216_ = l_Lean_NameSet_insert(v_ctorNames_202_, v_val_214_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_216_);
v___x_218_ = v___x_204_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_paramIdx_201_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_225_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_193_, v___x_218_, v___x_215_);
v___x_220_ = lean_st_ref_put(v_a_144_, v___x_219_);
v___x_221_ = lean_box(0);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_221_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v___x_226_; lean_object* v___x_228_; 
lean_dec(v_a_210_);
lean_del_object(v___x_204_);
lean_dec(v_ctorNames_202_);
lean_dec(v_paramIdx_201_);
lean_dec(v_fvarId_193_);
v___x_226_ = lean_box(0);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_226_);
v___x_228_ = v___x_212_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_del_object(v___x_204_);
lean_dec(v_ctorNames_202_);
lean_dec(v_paramIdx_201_);
lean_dec(v_fvarId_193_);
v_a_231_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_209_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_209_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_241_; 
lean_dec(v___x_207_);
lean_del_object(v___x_204_);
lean_dec(v_ctorNames_202_);
lean_dec(v_paramIdx_201_);
lean_dec(v_fvarId_193_);
v___x_239_ = lean_box(0);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 0);
lean_ctor_set(v___x_199_, 0, v___x_239_);
v___x_241_ = v___x_199_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec(v___x_196_);
lean_dec_ref(v_args_194_);
lean_dec(v_fvarId_193_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
case 4:
{
lean_object* v_cases_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_270_; 
v_cases_247_ = lean_ctor_get(v_code_143_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_code_143_);
if (v_isSharedCheck_270_ == 0)
{
v___x_249_ = v_code_143_;
v_isShared_250_ = v_isSharedCheck_270_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_cases_247_);
lean_dec(v_code_143_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_270_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_discr_251_; lean_object* v_alts_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_discr_251_ = lean_ctor_get(v_cases_247_, 2);
lean_inc(v_discr_251_);
v_alts_252_ = lean_ctor_get(v_cases_247_, 3);
lean_inc_ref(v_alts_252_);
lean_dec_ref(v_cases_247_);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_array_get_size(v_alts_252_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_nat_dec_lt(v___x_253_, v___x_254_);
if (v___x_256_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_alts_252_);
lean_dec(v_discr_251_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 0);
lean_ctor_set(v___x_249_, 0, v___x_255_);
v___x_258_ = v___x_249_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_255_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
else
{
uint8_t v___x_260_; 
v___x_260_ = lean_nat_dec_le(v___x_254_, v___x_254_);
if (v___x_260_ == 0)
{
if (v___x_256_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v_alts_252_);
lean_dec(v_discr_251_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 0);
lean_ctor_set(v___x_249_, 0, v___x_255_);
v___x_262_ = v___x_249_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_255_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; 
lean_del_object(v___x_249_);
v___x_264_ = ((size_t)0ULL);
v___x_265_ = lean_usize_of_nat(v___x_254_);
v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_251_, v_alts_252_, v___x_264_, v___x_265_, v___x_255_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec_ref(v_alts_252_);
return v___x_266_;
}
}
else
{
size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; 
lean_del_object(v___x_249_);
v___x_267_ = ((size_t)0ULL);
v___x_268_ = lean_usize_of_nat(v___x_254_);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_251_, v_alts_252_, v___x_267_, v___x_268_, v___x_255_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec_ref(v_alts_252_);
return v___x_269_;
}
}
}
}
default: 
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_isSharedCheck_278_ = !lean_is_exclusive(v_code_143_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_code_143_, 0);
lean_dec(v_unused_279_);
v___x_272_ = v_code_143_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_dec(v_code_143_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 0);
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object* v_discr_280_, lean_object* v_as_281_, size_t v_i_282_, size_t v_stop_283_, lean_object* v_b_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___y_293_; uint8_t v___x_298_; 
v___x_298_ = lean_usize_dec_eq(v_i_282_, v_stop_283_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_array_uget_borrowed(v_as_281_, v_i_282_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_ctorName_300_; lean_object* v_params_301_; lean_object* v_code_302_; lean_object* v___x_303_; 
v_ctorName_300_ = lean_ctor_get(v___x_299_, 0);
v_params_301_ = lean_ctor_get(v___x_299_, 1);
v_code_302_ = lean_ctor_get(v___x_299_, 2);
lean_inc_ref(v_params_301_);
lean_inc(v_ctorName_300_);
lean_inc(v_discr_280_);
v___x_303_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_280_, v_ctorName_300_, v_params_301_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
lean_inc_ref(v_code_302_);
v___x_305_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_302_, v___y_285_, v_a_304_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v_a_304_);
v___y_293_ = v___x_305_;
goto v___jp_292_;
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_discr_280_);
v_a_306_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_303_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
else
{
lean_object* v_code_314_; lean_object* v___x_315_; 
v_code_314_ = lean_ctor_get(v___x_299_, 0);
lean_inc_ref(v_code_314_);
v___x_315_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_314_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
v___y_293_ = v___x_315_;
goto v___jp_292_;
}
}
else
{
lean_object* v___x_316_; 
lean_dec(v_discr_280_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v_b_284_);
return v___x_316_;
}
v___jp_292_:
{
if (lean_obj_tag(v___y_293_) == 0)
{
lean_object* v_a_294_; size_t v___x_295_; size_t v___x_296_; 
v_a_294_ = lean_ctor_get(v___y_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___y_293_, 1);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_add(v_i_282_, v___x_295_);
v_i_282_ = v___x_296_;
v_b_284_ = v_a_294_;
goto _start;
}
else
{
lean_dec(v_discr_280_);
return v___y_293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object* v_discr_317_, lean_object* v_as_318_, lean_object* v_i_319_, lean_object* v_stop_320_, lean_object* v_b_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
size_t v_i_boxed_329_; size_t v_stop_boxed_330_; lean_object* v_res_331_; 
v_i_boxed_329_ = lean_unbox_usize(v_i_319_);
lean_dec(v_i_319_);
v_stop_boxed_330_ = lean_unbox_usize(v_stop_320_);
lean_dec(v_stop_320_);
v_res_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_317_, v_as_318_, v_i_boxed_329_, v_stop_boxed_330_, v_b_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v_as_318_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object* v_code_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object* v_00_u03b4_341_, lean_object* v_t_342_, lean_object* v_k_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_342_, v_k_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object* v_00_u03b4_345_, lean_object* v_t_346_, lean_object* v_k_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(v_00_u03b4_345_, v_t_346_, v_k_347_);
lean_dec(v_k_347_);
lean_dec(v_t_346_);
return v_res_348_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0(void){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1);
v___x_353_ = lean_box(1);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object* v_code_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_361_ = lean_box(1);
v___x_362_ = lean_st_mk_ref(v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_364_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_355_, v___x_362_, v___x_363_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_373_);
v___x_366_ = v___x_364_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_dec(v___x_364_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_st_ref_get(v___x_362_);
lean_dec(v___x_362_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v___x_362_);
v_a_374_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object* v_code_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
return v_res_388_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Array_instInhabited(lean_box(0));
return v___x_389_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1(void){
_start:
{
uint8_t v___x_390_; lean_object* v___x_391_; 
v___x_390_ = 0;
v___x_391_ = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(lean_object* v_msg_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0);
v___x_394_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_panic_fn_borrowed(v___x_395_, v_msg_392_);
lean_dec_ref_known(v___x_395_, 2);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2));
v___x_401_ = lean_unsigned_to_nat(11u);
v___x_402_ = lean_unsigned_to_nat(100u);
v___x_403_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1));
v___x_404_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0));
v___x_405_ = l_mkPanicMessageWithDecl(v___x_404_, v___x_403_, v___x_402_, v___x_401_, v___x_400_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(lean_object* v_code_406_, lean_object* v_decls_407_){
_start:
{
switch(lean_obj_tag(v_code_406_))
{
case 0:
{
lean_object* v_decl_408_; lean_object* v_k_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_decl_408_ = lean_ctor_get(v_code_406_, 0);
v_k_409_ = lean_ctor_get(v_code_406_, 1);
lean_inc_ref(v_decl_408_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_decl_408_);
v___x_411_ = lean_array_push(v_decls_407_, v___x_410_);
v_code_406_ = v_k_409_;
v_decls_407_ = v___x_411_;
goto _start;
}
case 4:
{
lean_object* v_cases_413_; lean_object* v___x_414_; 
v_cases_413_ = lean_ctor_get(v_code_406_, 0);
lean_inc_ref(v_cases_413_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_decls_407_);
lean_ctor_set(v___x_414_, 1, v_cases_413_);
return v___x_414_;
}
default: 
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec_ref(v_decls_407_);
v___x_415_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3);
v___x_416_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(v___x_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(lean_object* v_code_417_, lean_object* v_decls_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_417_, v_decls_418_);
lean_dec_ref(v_code_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(lean_object* v_code_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0));
v___x_424_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_422_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(lean_object* v_code_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_code_425_);
lean_dec_ref(v_code_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t v_sz_427_, size_t v_i_428_, lean_object* v_bs_429_, uint8_t v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v_bs_429_);
return v___x_438_;
}
else
{
uint8_t v___x_439_; lean_object* v_v_440_; lean_object* v___x_441_; 
v___x_439_ = 0;
v_v_440_ = lean_array_uget_borrowed(v_bs_429_, v_i_428_);
lean_inc(v_v_440_);
v___x_441_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_439_, v_v_440_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v_bs_x27_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = lean_unsigned_to_nat(0u);
v_bs_x27_444_ = lean_array_uset(v_bs_429_, v_i_428_, v___x_443_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_428_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_444_, v_i_428_, v_a_442_);
v_i_428_ = v___x_446_;
v_bs_429_ = v___x_447_;
goto _start;
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec_ref(v_bs_429_);
v_a_449_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_441_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_441_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object* v_sz_457_, lean_object* v_i_458_, lean_object* v_bs_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
size_t v_sz_boxed_467_; size_t v_i_boxed_468_; uint8_t v___y_5510__boxed_469_; lean_object* v_res_470_; 
v_sz_boxed_467_ = lean_unbox_usize(v_sz_457_);
lean_dec(v_sz_457_);
v_i_boxed_468_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v___y_5510__boxed_469_ = lean_unbox(v___y_460_);
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_boxed_467_, v_i_boxed_468_, v_bs_459_, v___y_5510__boxed_469_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object* v_fields_471_, lean_object* v_____r_472_, lean_object* v_paramsNew_473_, uint8_t v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; 
v_sz_481_ = lean_array_size(v_fields_471_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_481_, v___x_482_, v_fields_471_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_493_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_493_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = l_Array_append___redArg(v_paramsNew_473_, v_a_484_);
lean_dec(v_a_484_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_489_);
v___x_491_ = v___x_486_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v_paramsNew_473_);
v_a_494_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_483_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_483_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object* v_fields_502_, lean_object* v_____r_503_, lean_object* v_paramsNew_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
uint8_t v___y_5568__boxed_512_; lean_object* v_res_513_; 
v___y_5568__boxed_512_ = lean_unbox(v___y_505_);
v_res_513_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_502_, v_____r_503_, v_paramsNew_504_, v___y_5568__boxed_512_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object* v_upperBound_514_, lean_object* v_params_515_, lean_object* v_targetParamIdx_516_, uint8_t v___y_517_, lean_object* v_fields_518_, lean_object* v_a_519_, lean_object* v_b_520_, uint8_t v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_a_529_; lean_object* v___y_534_; uint8_t v___x_553_; 
v___x_553_ = lean_nat_dec_lt(v_a_519_, v_upperBound_514_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec(v_a_519_);
lean_dec_ref(v_fields_518_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_b_520_);
return v___x_554_;
}
else
{
uint8_t v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = 0;
v___x_556_ = lean_array_fget_borrowed(v_params_515_, v_a_519_);
v___x_557_ = lean_nat_dec_eq(v_targetParamIdx_516_, v_a_519_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_inc(v___x_556_);
v___x_558_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_555_, v___x_556_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = lean_array_push(v_b_520_, v_a_559_);
v_a_529_ = v___x_560_;
goto v___jp_528_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref(v_b_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_fields_518_);
v_a_561_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_558_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_558_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
if (v___y_517_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_box(0);
lean_inc_ref(v_fields_518_);
v___x_570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_518_, v___x_569_, v_b_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
v___y_534_ = v___x_570_;
goto v___jp_533_;
}
else
{
lean_object* v___x_571_; 
lean_inc(v___x_556_);
v___x_571_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_555_, v___x_556_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = lean_array_push(v_b_520_, v_a_572_);
v___x_574_ = lean_box(0);
lean_inc_ref(v_fields_518_);
v___x_575_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_518_, v___x_574_, v___x_573_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
v___y_534_ = v___x_575_;
goto v___jp_533_;
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_b_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_fields_518_);
v_a_576_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_571_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_571_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_a_519_, v___x_530_);
lean_dec(v_a_519_);
v_a_519_ = v___x_531_;
v_b_520_ = v_a_529_;
goto _start;
}
v___jp_533_:
{
if (lean_obj_tag(v___y_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_544_; 
v_a_535_ = lean_ctor_get(v___y_534_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___y_534_);
if (v_isSharedCheck_544_ == 0)
{
v___x_537_ = v___y_534_;
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___y_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_544_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
if (lean_obj_tag(v_a_535_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; 
lean_dec(v_a_519_);
lean_dec_ref(v_fields_518_);
v_a_539_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v_a_535_, 1);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_a_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
else
{
lean_object* v_a_543_; 
lean_del_object(v___x_537_);
v_a_543_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v_a_535_, 1);
v_a_529_ = v_a_543_;
goto v___jp_528_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v_a_519_);
lean_dec_ref(v_fields_518_);
v_a_545_ = lean_ctor_get(v___y_534_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___y_534_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___y_534_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___y_534_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object* v_upperBound_584_, lean_object* v_params_585_, lean_object* v_targetParamIdx_586_, lean_object* v___y_587_, lean_object* v_fields_588_, lean_object* v_a_589_, lean_object* v_b_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v___y_5632__boxed_598_; uint8_t v___y_5633__boxed_599_; lean_object* v_res_600_; 
v___y_5632__boxed_598_ = lean_unbox(v___y_587_);
v___y_5633__boxed_599_ = lean_unbox(v___y_591_);
v_res_600_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_584_, v_params_585_, v_targetParamIdx_586_, v___y_5632__boxed_598_, v_fields_588_, v_a_589_, v_b_590_, v___y_5633__boxed_599_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec(v_targetParamIdx_586_);
lean_dec_ref(v_params_585_);
lean_dec(v_upperBound_584_);
return v_res_600_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object* v_singleton_601_, lean_object* v_as_602_, size_t v_i_603_, size_t v_stop_604_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_eq(v_i_603_, v_stop_604_);
if (v___x_605_ == 0)
{
uint8_t v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = 0;
v___x_607_ = lean_array_uget_borrowed(v_as_602_, v_i_603_);
v___x_608_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_606_, v___x_607_, v_singleton_601_);
if (v___x_608_ == 0)
{
size_t v___x_609_; size_t v___x_610_; 
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_603_, v___x_609_);
v_i_603_ = v___x_610_;
goto _start;
}
else
{
return v___x_608_;
}
}
else
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object* v_singleton_613_, lean_object* v_as_614_, lean_object* v_i_615_, lean_object* v_stop_616_){
_start:
{
size_t v_i_boxed_617_; size_t v_stop_boxed_618_; uint8_t v_res_619_; lean_object* v_r_620_; 
v_i_boxed_617_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_stop_boxed_618_ = lean_unbox_usize(v_stop_616_);
lean_dec(v_stop_616_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_613_, v_as_614_, v_i_boxed_617_, v_stop_boxed_618_);
lean_dec_ref(v_as_614_);
lean_dec(v_singleton_613_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(size_t v_sz_621_, size_t v_i_622_, lean_object* v_bs_623_, uint8_t v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_lt(v_i_622_, v_sz_621_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_bs_623_);
return v___x_632_;
}
else
{
uint8_t v___x_633_; lean_object* v_v_634_; lean_object* v___x_635_; 
v___x_633_ = 0;
v_v_634_ = lean_array_uget_borrowed(v_bs_623_, v_i_622_);
lean_inc(v_v_634_);
v___x_635_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_633_, v_v_634_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v_bs_x27_638_; size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = lean_unsigned_to_nat(0u);
v_bs_x27_638_ = lean_array_uset(v_bs_623_, v_i_622_, v___x_637_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_add(v_i_622_, v___x_639_);
v___x_641_ = lean_array_uset(v_bs_x27_638_, v_i_622_, v_a_636_);
v_i_622_ = v___x_640_;
v_bs_623_ = v___x_641_;
goto _start;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v_bs_623_);
v_a_643_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_635_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_635_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(lean_object* v_sz_651_, lean_object* v_i_652_, lean_object* v_bs_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
size_t v_sz_boxed_661_; size_t v_i_boxed_662_; uint8_t v___y_5786__boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_661_ = lean_unbox_usize(v_sz_651_);
lean_dec(v_sz_651_);
v_i_boxed_662_ = lean_unbox_usize(v_i_652_);
lean_dec(v_i_652_);
v___y_5786__boxed_663_ = lean_unbox(v___y_654_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_boxed_661_, v_i_boxed_662_, v_bs_653_, v___y_5786__boxed_663_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
return v_res_664_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0(void){
_start:
{
uint8_t v___x_665_; lean_object* v___x_666_; 
v___x_665_ = 0;
v___x_666_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object* v_decls_672_, lean_object* v_params_673_, lean_object* v_targetParamIdx_674_, lean_object* v_fields_675_, lean_object* v_k_676_, uint8_t v_default_677_, uint8_t v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_fvarId_688_; lean_object* v___x_689_; lean_object* v_paramsNew_690_; uint8_t v___y_692_; lean_object* v_singleton_746_; uint8_t v___x_747_; 
v___x_685_ = 0;
v___x_686_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0);
v___x_687_ = lean_array_get_borrowed(v___x_686_, v_params_673_, v_targetParamIdx_674_);
v_fvarId_688_ = lean_ctor_get(v___x_687_, 0);
v___x_689_ = lean_unsigned_to_nat(0u);
v_paramsNew_690_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
lean_inc(v_fvarId_688_);
v_singleton_746_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_688_);
v___x_747_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_685_, v_k_676_, v_singleton_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_array_get_size(v_decls_672_);
v___x_749_ = lean_nat_dec_lt(v___x_689_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec(v_singleton_746_);
v___y_692_ = v___x_747_;
goto v___jp_691_;
}
else
{
if (v___x_749_ == 0)
{
lean_dec(v_singleton_746_);
v___y_692_ = v___x_747_;
goto v___jp_691_;
}
else
{
size_t v___x_750_; size_t v___x_751_; uint8_t v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_748_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_746_, v_decls_672_, v___x_750_, v___x_751_);
lean_dec(v_singleton_746_);
v___y_692_ = v___x_752_;
goto v___jp_691_;
}
}
}
else
{
lean_dec(v_singleton_746_);
v___y_692_ = v___x_747_;
goto v___jp_691_;
}
v___jp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_array_get_size(v_params_673_);
v___x_694_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v___x_693_, v_params_673_, v_targetParamIdx_674_, v___y_692_, v_fields_675_, v___x_689_, v_paramsNew_690_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; size_t v_sz_696_; size_t v___x_697_; lean_object* v___x_698_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v_sz_696_ = lean_array_size(v_decls_672_);
v___x_697_ = ((size_t)0ULL);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_696_, v___x_697_, v_decls_672_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_685_, v_k_676_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_685_, v_a_699_, v_a_701_);
lean_dec(v_a_699_);
v___x_703_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3));
v___x_704_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___x_685_, v_a_695_, v___x_702_, v___x_703_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_713_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_713_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_709_, 0, v_a_705_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*1, v_default_677_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*1 + 1, v___y_692_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_a_714_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_704_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_704_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_699_);
lean_dec(v_a_695_);
v_a_722_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_700_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_700_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_a_695_);
lean_dec_ref(v_k_676_);
v_a_730_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_698_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_698_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_k_676_);
lean_dec_ref(v_decls_672_);
v_a_738_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_694_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_694_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object* v_decls_753_, lean_object* v_params_754_, lean_object* v_targetParamIdx_755_, lean_object* v_fields_756_, lean_object* v_k_757_, lean_object* v_default_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
uint8_t v_default_boxed_766_; uint8_t v_a_boxed_767_; lean_object* v_res_768_; 
v_default_boxed_766_ = lean_unbox(v_default_758_);
v_a_boxed_767_ = lean_unbox(v_a_759_);
v_res_768_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_753_, v_params_754_, v_targetParamIdx_755_, v_fields_756_, v_k_757_, v_default_boxed_766_, v_a_boxed_767_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec(v_targetParamIdx_755_);
lean_dec_ref(v_params_754_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object* v_upperBound_769_, lean_object* v_params_770_, lean_object* v_targetParamIdx_771_, uint8_t v___y_772_, lean_object* v_fields_773_, lean_object* v_inst_774_, lean_object* v_R_775_, lean_object* v_a_776_, lean_object* v_b_777_, lean_object* v_c_778_, uint8_t v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_769_, v_params_770_, v_targetParamIdx_771_, v___y_772_, v_fields_773_, v_a_776_, v_b_777_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_787_ = _args[0];
lean_object* v_params_788_ = _args[1];
lean_object* v_targetParamIdx_789_ = _args[2];
lean_object* v___y_790_ = _args[3];
lean_object* v_fields_791_ = _args[4];
lean_object* v_inst_792_ = _args[5];
lean_object* v_R_793_ = _args[6];
lean_object* v_a_794_ = _args[7];
lean_object* v_b_795_ = _args[8];
lean_object* v_c_796_ = _args[9];
lean_object* v___y_797_ = _args[10];
lean_object* v___y_798_ = _args[11];
lean_object* v___y_799_ = _args[12];
lean_object* v___y_800_ = _args[13];
lean_object* v___y_801_ = _args[14];
lean_object* v___y_802_ = _args[15];
lean_object* v___y_803_ = _args[16];
_start:
{
uint8_t v___y_5993__boxed_804_; uint8_t v___y_5995__boxed_805_; lean_object* v_res_806_; 
v___y_5993__boxed_804_ = lean_unbox(v___y_790_);
v___y_5995__boxed_805_ = lean_unbox(v___y_797_);
v_res_806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(v_upperBound_787_, v_params_788_, v_targetParamIdx_789_, v___y_5993__boxed_804_, v_fields_791_, v_inst_792_, v_R_793_, v_a_794_, v_b_795_, v_c_796_, v___y_5995__boxed_805_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec(v_targetParamIdx_789_);
lean_dec_ref(v_params_788_);
lean_dec(v_upperBound_787_);
return v_res_806_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0(void){
_start:
{
lean_object* v_cellCount_807_; lean_object* v___x_808_; 
v_cellCount_807_ = lean_unsigned_to_nat(16u);
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_807_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1(void){
_start:
{
lean_object* v_cellCount_809_; lean_object* v___x_810_; 
v_cellCount_809_ = lean_unsigned_to_nat(16u);
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_809_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__2(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_811_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1);
v___x_812_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
lean_ctor_set(v___x_814_, 2, v___x_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object* v_decls_815_, lean_object* v_params_816_, lean_object* v_targetParamIdx_817_, lean_object* v_fields_818_, lean_object* v_k_819_, uint8_t v_default_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__2, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__2_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__2);
v___x_827_ = lean_st_mk_ref(v___x_826_);
v___x_828_ = 0;
v___x_829_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_815_, v_params_816_, v_targetParamIdx_817_, v_fields_818_, v_k_819_, v_default_820_, v___x_828_, v___x_827_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_st_ref_get(v___x_827_);
lean_dec(v___x_827_);
lean_dec(v___x_834_);
if (v_isShared_833_ == 0)
{
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_830_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_dec(v___x_827_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object* v_decls_839_, lean_object* v_params_840_, lean_object* v_targetParamIdx_841_, lean_object* v_fields_842_, lean_object* v_k_843_, lean_object* v_default_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
uint8_t v_default_boxed_850_; lean_object* v_res_851_; 
v_default_boxed_850_ = lean_unbox(v_default_844_);
v_res_851_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_decls_839_, v_params_840_, v_targetParamIdx_841_, v_fields_842_, v_k_843_, v_default_boxed_850_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_targetParamIdx_841_);
lean_dec_ref(v_params_840_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object* v_args_852_, lean_object* v_targetParamIdx_853_, lean_object* v_fields_854_, uint8_t v_dependsOnTarget_855_){
_start:
{
if (v_dependsOnTarget_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_lower_861_; lean_object* v_upper_862_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_856_ = lean_unsigned_to_nat(0u);
lean_inc(v_targetParamIdx_853_);
lean_inc_ref(v_args_852_);
v___x_857_ = l_Array_toSubarray___redArg(v_args_852_, v___x_856_, v_targetParamIdx_853_);
v___x_858_ = l_Subarray_copy___redArg(v___x_857_);
v___x_859_ = l_Array_append___redArg(v___x_858_, v_fields_854_);
v___x_866_ = lean_array_get_size(v_args_852_);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_targetParamIdx_853_, v___x_867_);
lean_dec(v_targetParamIdx_853_);
v___x_869_ = lean_nat_dec_le(v___x_868_, v___x_856_);
if (v___x_869_ == 0)
{
v_lower_861_ = v___x_868_;
v_upper_862_ = v___x_866_;
goto v___jp_860_;
}
else
{
lean_dec(v___x_868_);
v_lower_861_ = v___x_856_;
v_upper_862_ = v___x_866_;
goto v___jp_860_;
}
v___jp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = l_Array_toSubarray___redArg(v_args_852_, v_lower_861_, v_upper_862_);
v___x_864_ = l_Subarray_copy___redArg(v___x_863_);
v___x_865_ = l_Array_append___redArg(v___x_859_, v___x_864_);
lean_dec_ref(v___x_864_);
return v___x_865_;
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_lower_877_; lean_object* v_upper_878_; lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_add(v_targetParamIdx_853_, v___x_871_);
lean_dec(v_targetParamIdx_853_);
lean_inc(v___x_872_);
lean_inc_ref(v_args_852_);
v___x_873_ = l_Array_toSubarray___redArg(v_args_852_, v___x_870_, v___x_872_);
v___x_874_ = l_Subarray_copy___redArg(v___x_873_);
v___x_875_ = l_Array_append___redArg(v___x_874_, v_fields_854_);
v___x_882_ = lean_array_get_size(v_args_852_);
v___x_883_ = lean_nat_dec_le(v___x_872_, v___x_870_);
if (v___x_883_ == 0)
{
v_lower_877_ = v___x_872_;
v_upper_878_ = v___x_882_;
goto v___jp_876_;
}
else
{
lean_dec(v___x_872_);
v_lower_877_ = v___x_870_;
v_upper_878_ = v___x_882_;
goto v___jp_876_;
}
v___jp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = l_Array_toSubarray___redArg(v_args_852_, v_lower_877_, v_upper_878_);
v___x_880_ = l_Subarray_copy___redArg(v___x_879_);
v___x_881_ = l_Array_append___redArg(v___x_875_, v___x_880_);
lean_dec_ref(v___x_880_);
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object* v_args_884_, lean_object* v_targetParamIdx_885_, lean_object* v_fields_886_, lean_object* v_dependsOnTarget_887_){
_start:
{
uint8_t v_dependsOnTarget_boxed_888_; lean_object* v_res_889_; 
v_dependsOnTarget_boxed_888_ = lean_unbox(v_dependsOnTarget_887_);
v_res_889_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_884_, v_targetParamIdx_885_, v_fields_886_, v_dependsOnTarget_boxed_888_);
lean_dec_ref(v_fields_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t v_sz_890_, size_t v_i_891_, lean_object* v_bs_892_){
_start:
{
uint8_t v___x_893_; 
v___x_893_ = lean_usize_dec_lt(v_i_891_, v_sz_890_);
if (v___x_893_ == 0)
{
return v_bs_892_;
}
else
{
lean_object* v_v_894_; lean_object* v_fvarId_895_; lean_object* v___x_896_; lean_object* v_bs_x27_897_; lean_object* v___x_898_; size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v_v_894_ = lean_array_uget_borrowed(v_bs_892_, v_i_891_);
v_fvarId_895_ = lean_ctor_get(v_v_894_, 0);
lean_inc(v_fvarId_895_);
v___x_896_ = lean_unsigned_to_nat(0u);
v_bs_x27_897_ = lean_array_uset(v_bs_892_, v_i_891_, v___x_896_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_fvarId_895_);
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_891_, v___x_899_);
v___x_901_ = lean_array_uset(v_bs_x27_897_, v_i_891_, v___x_898_);
v_i_891_ = v___x_900_;
v_bs_892_ = v___x_901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_bs_905_){
_start:
{
size_t v_sz_boxed_906_; size_t v_i_boxed_907_; lean_object* v_res_908_; 
v_sz_boxed_906_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_907_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_boxed_906_, v_i_boxed_907_, v_bs_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t v_sz_909_, size_t v_i_910_, lean_object* v_bs_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_912_ == 0)
{
return v_bs_911_;
}
else
{
lean_object* v_v_913_; lean_object* v_fvarId_914_; lean_object* v___x_915_; lean_object* v_bs_x27_916_; lean_object* v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_v_913_ = lean_array_uget_borrowed(v_bs_911_, v_i_910_);
v_fvarId_914_ = lean_ctor_get(v_v_913_, 0);
lean_inc(v_fvarId_914_);
v___x_915_ = lean_unsigned_to_nat(0u);
v_bs_x27_916_ = lean_array_uset(v_bs_911_, v_i_910_, v___x_915_);
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v_fvarId_914_);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_910_, v___x_918_);
v___x_920_ = lean_array_uset(v_bs_x27_916_, v_i_910_, v___x_917_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_909_, v___x_919_, v___x_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(lean_object* v_sz_922_, lean_object* v_i_923_, lean_object* v_bs_924_){
_start:
{
size_t v_sz_boxed_925_; size_t v_i_boxed_926_; lean_object* v_res_927_; 
v_sz_boxed_925_ = lean_unbox_usize(v_sz_922_);
lean_dec(v_sz_922_);
v_i_boxed_926_ = lean_unbox_usize(v_i_923_);
lean_dec(v_i_923_);
v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_boxed_925_, v_i_boxed_926_, v_bs_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object* v_params_928_, lean_object* v_targetParamIdx_929_, lean_object* v_fields_930_, uint8_t v_dependsOnTarget_931_){
_start:
{
size_t v_sz_932_; size_t v___x_933_; lean_object* v___x_934_; size_t v_sz_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_sz_932_ = lean_array_size(v_params_928_);
v___x_933_ = ((size_t)0ULL);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_932_, v___x_933_, v_params_928_);
v_sz_935_ = lean_array_size(v_fields_930_);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_935_, v___x_933_, v_fields_930_);
v___x_937_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v___x_934_, v_targetParamIdx_929_, v___x_936_, v_dependsOnTarget_931_);
lean_dec_ref(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object* v_params_938_, lean_object* v_targetParamIdx_939_, lean_object* v_fields_940_, lean_object* v_dependsOnTarget_941_){
_start:
{
uint8_t v_dependsOnTarget_boxed_942_; lean_object* v_res_943_; 
v_dependsOnTarget_boxed_942_ = lean_unbox(v_dependsOnTarget_941_);
v_res_943_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_938_, v_targetParamIdx_939_, v_fields_940_, v_dependsOnTarget_boxed_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object* v_fvarId_949_, lean_object* v_args_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_st_ref_get(v_a_952_);
v___x_960_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_959_, v_fvarId_949_);
lean_dec(v___x_959_);
if (lean_obj_tag(v___x_960_) == 1)
{
lean_object* v_val_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1143_; 
v_val_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_1143_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_val_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1143_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_951_, v_fvarId_949_);
if (lean_obj_tag(v___x_965_) == 1)
{
lean_object* v_val_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1138_; 
lean_del_object(v___x_963_);
v_val_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_1138_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_val_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1138_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v_paramIdx_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1136_; 
v_paramIdx_970_ = lean_ctor_get(v_val_966_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_val_966_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_val_966_, 1);
lean_dec(v_unused_1137_);
v___x_972_ = v_val_966_;
v_isShared_973_ = v_isSharedCheck_1136_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_paramIdx_970_);
lean_dec(v_val_966_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1136_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_box(0);
v___x_975_ = lean_array_get(v___x_974_, v_args_950_, v_paramIdx_970_);
if (lean_obj_tag(v___x_975_) == 1)
{
lean_object* v_fvarId_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1131_; 
lean_del_object(v___x_968_);
v_fvarId_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1131_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_fvarId_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1131_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_976_, v_a_953_, v_a_955_, v_a_957_);
lean_dec(v_fvarId_976_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1122_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1122_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1122_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
if (lean_obj_tag(v_a_981_) == 1)
{
lean_object* v_val_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1117_; 
v_val_985_ = lean_ctor_get(v_a_981_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_987_ = v_a_981_;
v_isShared_988_ = v_isSharedCheck_1117_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_val_985_);
lean_dec(v_a_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1117_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_985_);
v___x_990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_961_, v___x_989_);
lean_dec(v___x_989_);
lean_dec(v_val_961_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_val_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1112_; 
v_val_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1112_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_val_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1112_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
uint8_t v_default_995_; 
v_default_995_ = lean_ctor_get_uint8(v_val_991_, sizeof(void*)*1);
if (v_default_995_ == 0)
{
if (lean_obj_tag(v_val_985_) == 0)
{
lean_object* v_decl_996_; uint8_t v_dependsOnDiscr_997_; lean_object* v_val_998_; lean_object* v_args_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1034_; 
lean_del_object(v___x_987_);
lean_del_object(v___x_978_);
lean_del_object(v___x_972_);
v_decl_996_ = lean_ctor_get(v_val_991_, 0);
lean_inc_ref(v_decl_996_);
v_dependsOnDiscr_997_ = lean_ctor_get_uint8(v_val_991_, sizeof(void*)*1 + 1);
lean_dec(v_val_991_);
v_val_998_ = lean_ctor_get(v_val_985_, 0);
v_args_999_ = lean_ctor_get(v_val_985_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_val_985_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1001_ = v_val_985_;
v_isShared_1002_ = v_isSharedCheck_1034_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_args_999_);
lean_inc(v_val_998_);
lean_dec(v_val_985_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1034_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___y_1004_; lean_object* v_numParams_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_numParams_1024_ = lean_ctor_get(v_val_998_, 3);
lean_inc(v_numParams_1024_);
lean_dec_ref(v_val_998_);
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_array_get_size(v_args_999_);
v___x_1027_ = lean_nat_dec_le(v_numParams_1024_, v___x_1025_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1029_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1026_);
lean_ctor_set(v___x_1001_, 0, v_numParams_1024_);
v___x_1029_ = v___x_1001_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_numParams_1024_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1026_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
v___y_1004_ = v___x_1029_;
goto v___jp_1003_;
}
}
else
{
lean_object* v___x_1032_; 
lean_dec(v_numParams_1024_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1026_);
lean_ctor_set(v___x_1001_, 0, v___x_1025_);
v___x_1032_ = v___x_1001_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1026_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v___y_1004_ = v___x_1032_;
goto v___jp_1003_;
}
}
v___jp_1003_:
{
lean_object* v_fvarId_1005_; lean_object* v_lower_1006_; lean_object* v_upper_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1023_; 
v_fvarId_1005_ = lean_ctor_get(v_decl_996_, 0);
lean_inc(v_fvarId_1005_);
lean_dec_ref(v_decl_996_);
v_lower_1006_ = lean_ctor_get(v___y_1004_, 0);
v_upper_1007_ = lean_ctor_get(v___y_1004_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___y_1004_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1009_ = v___y_1004_;
v_isShared_1010_ = v_isSharedCheck_1023_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_upper_1007_);
lean_inc(v_lower_1006_);
lean_dec(v___y_1004_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1023_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1011_ = l_Array_toSubarray___redArg(v_args_999_, v_lower_1006_, v_upper_1007_);
v___x_1012_ = l_Subarray_copy___redArg(v___x_1011_);
v___x_1013_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_950_, v_paramIdx_970_, v___x_1012_, v_dependsOnDiscr_997_);
lean_dec_ref(v___x_1012_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 3);
lean_ctor_set(v___x_1009_, 1, v___x_1013_);
lean_ctor_set(v___x_1009_, 0, v_fvarId_1005_);
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_fvarId_1005_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1015_);
v___x_1017_ = v___x_993_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1017_);
v___x_1019_ = v___x_983_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
}
}
else
{
lean_object* v_decl_1035_; uint8_t v_dependsOnDiscr_1036_; lean_object* v_n_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1097_; 
v_decl_1035_ = lean_ctor_get(v_val_991_, 0);
lean_inc_ref(v_decl_1035_);
v_dependsOnDiscr_1036_ = lean_ctor_get_uint8(v_val_991_, sizeof(void*)*1 + 1);
lean_dec(v_val_991_);
v_n_1037_ = lean_ctor_get(v_val_985_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_val_985_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1039_ = v_val_985_;
v_isShared_1040_ = v_isSharedCheck_1097_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_n_1037_);
lean_dec(v_val_985_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1097_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_zero_1041_; uint8_t v_isZero_1042_; 
v_zero_1041_ = lean_unsigned_to_nat(0u);
v_isZero_1042_ = lean_nat_dec_eq(v_n_1037_, v_zero_1041_);
if (v_isZero_1042_ == 1)
{
lean_object* v_fvarId_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_del_object(v___x_1039_);
lean_dec(v_n_1037_);
lean_del_object(v___x_987_);
lean_del_object(v___x_978_);
v_fvarId_1043_ = lean_ctor_get(v_decl_1035_, 0);
lean_inc(v_fvarId_1043_);
lean_dec_ref(v_decl_1035_);
v___x_1044_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1045_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_950_, v_paramIdx_970_, v___x_1044_, v_dependsOnDiscr_1036_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 1, v___x_1045_);
lean_ctor_set(v___x_972_, 0, v_fvarId_1043_);
v___x_1047_ = v___x_972_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_fvarId_1043_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1049_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1047_);
v___x_1049_ = v___x_993_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1049_);
v___x_1051_ = v___x_983_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
uint8_t v___x_1055_; lean_object* v_one_1056_; lean_object* v_n_1057_; lean_object* v___x_1059_; 
lean_del_object(v___x_983_);
v___x_1055_ = 0;
v_one_1056_ = lean_unsigned_to_nat(1u);
v_n_1057_ = lean_nat_sub(v_n_1037_, v_one_1056_);
lean_dec(v_n_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 0);
lean_ctor_set(v___x_1039_, 0, v_n_1057_);
v___x_1059_ = v___x_1039_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_n_1057_);
v___x_1059_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 0, v___x_1059_);
v___x_1061_ = v___x_987_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
v___x_1063_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1055_, v___x_1061_, v___x_1062_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1086_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1086_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1086_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_fvarId_1068_; lean_object* v_fvarId_1069_; lean_object* v___x_1071_; 
v_fvarId_1068_ = lean_ctor_get(v_decl_1035_, 0);
lean_inc(v_fvarId_1068_);
lean_dec_ref(v_decl_1035_);
v_fvarId_1069_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_fvarId_1069_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_fvarId_1069_);
v___x_1071_ = v___x_978_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_fvarId_1069_);
v___x_1071_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1072_ = lean_mk_empty_array_with_capacity(v_one_1056_);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_1071_);
v___x_1074_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_950_, v_paramIdx_970_, v___x_1073_, v_dependsOnDiscr_1036_);
lean_dec_ref(v___x_1073_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 1, v___x_1074_);
lean_ctor_set(v___x_972_, 0, v_fvarId_1068_);
v___x_1076_ = v___x_972_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_fvarId_1068_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_a_1064_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1077_);
v___x_1079_ = v___x_993_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1079_);
v___x_1081_ = v___x_1066_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_decl_1035_);
lean_del_object(v___x_993_);
lean_del_object(v___x_978_);
lean_del_object(v___x_972_);
lean_dec(v_paramIdx_970_);
lean_dec_ref(v_args_950_);
v_a_1087_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1063_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1063_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
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
lean_object* v_decl_1098_; uint8_t v_dependsOnDiscr_1099_; lean_object* v_fvarId_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_del_object(v___x_987_);
lean_dec(v_val_985_);
lean_del_object(v___x_978_);
v_decl_1098_ = lean_ctor_get(v_val_991_, 0);
lean_inc_ref(v_decl_1098_);
v_dependsOnDiscr_1099_ = lean_ctor_get_uint8(v_val_991_, sizeof(void*)*1 + 1);
lean_dec(v_val_991_);
v_fvarId_1100_ = lean_ctor_get(v_decl_1098_, 0);
lean_inc(v_fvarId_1100_);
lean_dec_ref(v_decl_1098_);
v___x_1101_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1102_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_950_, v_paramIdx_970_, v___x_1101_, v_dependsOnDiscr_1099_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 1, v___x_1102_);
lean_ctor_set(v___x_972_, 0, v_fvarId_1100_);
v___x_1104_ = v___x_972_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fvarId_1100_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1104_);
v___x_1106_ = v___x_993_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1108_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1106_);
v___x_1108_ = v___x_983_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_dec(v___x_990_);
lean_del_object(v___x_987_);
lean_dec(v_val_985_);
lean_del_object(v___x_978_);
lean_del_object(v___x_972_);
lean_dec(v_paramIdx_970_);
lean_dec_ref(v_args_950_);
v___x_1113_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1113_);
v___x_1115_ = v___x_983_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec(v_a_981_);
lean_del_object(v___x_978_);
lean_del_object(v___x_972_);
lean_dec(v_paramIdx_970_);
lean_dec(v_val_961_);
lean_dec_ref(v_args_950_);
v___x_1118_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1118_);
v___x_1120_ = v___x_983_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
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
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_del_object(v___x_978_);
lean_del_object(v___x_972_);
lean_dec(v_paramIdx_970_);
lean_dec(v_val_961_);
lean_dec_ref(v_args_950_);
v_a_1123_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_980_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_980_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
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
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec(v___x_975_);
lean_del_object(v___x_972_);
lean_dec(v_paramIdx_970_);
lean_dec(v_val_961_);
lean_dec_ref(v_args_950_);
v___x_1132_ = lean_box(0);
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 0);
lean_ctor_set(v___x_968_, 0, v___x_1132_);
v___x_1134_ = v___x_968_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_dec(v___x_965_);
lean_dec(v_val_961_);
lean_dec_ref(v_args_950_);
v___x_1139_ = lean_box(0);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 0);
lean_ctor_set(v___x_963_, 0, v___x_1139_);
v___x_1141_ = v___x_963_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
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
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v___x_960_);
lean_dec_ref(v_args_950_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object* v_fvarId_1146_, lean_object* v_args_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1146_, v_args_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec(v_fvarId_1146_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object* v___x_1157_, lean_object* v_init_1158_, lean_object* v_x_1159_){
_start:
{
if (lean_obj_tag(v_x_1159_) == 0)
{
lean_object* v_k_1160_; lean_object* v_l_1161_; lean_object* v_r_1162_; lean_object* v___x_1163_; 
v_k_1160_ = lean_ctor_get(v_x_1159_, 1);
v_l_1161_ = lean_ctor_get(v_x_1159_, 3);
v_r_1162_ = lean_ctor_get(v_x_1159_, 4);
v___x_1163_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1157_, v_init_1158_, v_l_1161_);
if (lean_obj_tag(v___x_1163_) == 0)
{
return v___x_1163_;
}
else
{
uint8_t v___x_1164_; 
lean_dec_ref_known(v___x_1163_, 1);
v___x_1164_ = l_Lean_NameSet_contains(v___x_1157_, v_k_1160_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2));
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v_init_1158_ = v___x_1166_;
v_x_1159_ = v_r_1162_;
goto _start;
}
}
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_init_1158_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object* v___x_1169_, lean_object* v_init_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1169_, v_init_1170_, v_x_1171_);
lean_dec(v_x_1171_);
lean_dec(v___x_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object* v___x_1173_, lean_object* v_a_1174_, lean_object* v_init_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v_d_1179_; 
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_object* v_k_1182_; lean_object* v_l_1183_; lean_object* v_r_1184_; lean_object* v___x_1185_; lean_object* v_a_1186_; 
v_k_1182_ = lean_ctor_get(v_x_1176_, 1);
lean_inc(v_k_1182_);
v_l_1183_ = lean_ctor_get(v_x_1176_, 3);
lean_inc(v_l_1183_);
v_r_1184_ = lean_ctor_get(v_x_1176_, 4);
lean_inc(v_r_1184_);
lean_dec_ref_known(v_x_1176_, 5);
lean_inc_ref(v_a_1174_);
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1173_, v_a_1174_, v_init_1175_, v_l_1183_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
if (lean_obj_tag(v_a_1186_) == 0)
{
lean_object* v_a_1187_; 
lean_dec_ref(v___x_1185_);
lean_dec(v_r_1184_);
lean_dec(v_k_1182_);
lean_dec_ref(v_a_1174_);
v_a_1187_ = lean_ctor_get(v_a_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v_a_1186_, 1);
v_d_1179_ = v_a_1187_;
goto v___jp_1178_;
}
else
{
lean_object* v_a_1188_; uint8_t v___x_1189_; 
v_a_1188_ = lean_ctor_get(v_a_1186_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v_a_1186_, 1);
v___x_1189_ = l_Lean_NameSet_contains(v___x_1173_, v_k_1182_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v___x_1185_);
lean_inc_ref(v_a_1174_);
v___x_1190_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1182_, v_a_1174_, v_a_1188_);
v_init_1175_ = v___x_1190_;
v_x_1176_ = v_r_1184_;
goto _start;
}
else
{
lean_object* v_a_1192_; 
lean_dec(v_a_1188_);
lean_dec(v_k_1182_);
v_a_1192_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1185_);
if (lean_obj_tag(v_a_1192_) == 0)
{
lean_object* v_a_1193_; 
lean_dec(v_r_1184_);
lean_dec_ref(v_a_1174_);
v_a_1193_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v_a_1192_, 1);
v_d_1179_ = v_a_1193_;
goto v___jp_1178_;
}
else
{
lean_object* v_a_1194_; 
v_a_1194_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v_a_1192_, 1);
v_init_1175_ = v_a_1194_;
v_x_1176_ = v_r_1184_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref(v_a_1174_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_init_1175_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_d_1179_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object* v___x_1198_, lean_object* v_a_1199_, lean_object* v_init_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1198_, v_a_1199_, v_init_1200_, v_x_1201_);
lean_dec(v___x_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object* v_discr_1209_, lean_object* v___x_1210_, lean_object* v_val_1211_, lean_object* v_fst_1212_, lean_object* v_params_1213_, lean_object* v_snd_1214_, lean_object* v_as_1215_, size_t v_sz_1216_, size_t v_i_1217_, lean_object* v_b_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_a_1228_; uint8_t v___x_1232_; 
v___x_1232_ = lean_usize_dec_lt(v_i_1217_, v_sz_1216_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_b_1218_);
return v___x_1233_;
}
else
{
lean_object* v_snd_1234_; lean_object* v_fst_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1393_; 
v_snd_1234_ = lean_ctor_get(v_b_1218_, 1);
v_fst_1235_ = lean_ctor_get(v_b_1218_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_b_1218_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1237_ = v_b_1218_;
v_isShared_1238_ = v_isSharedCheck_1393_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snd_1234_);
lean_inc(v_fst_1235_);
lean_dec(v_b_1218_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1393_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_fst_1239_; lean_object* v_snd_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1392_; 
v_fst_1239_ = lean_ctor_get(v_snd_1234_, 0);
v_snd_1240_ = lean_ctor_get(v_snd_1234_, 1);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_snd_1234_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1242_ = v_snd_1234_;
v_isShared_1243_ = v_isSharedCheck_1392_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snd_1240_);
lean_inc(v_fst_1239_);
lean_dec(v_snd_1234_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1392_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint8_t v___x_1244_; lean_object* v_a_1245_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v_a_1252_; 
v___x_1244_ = 0;
v_a_1245_ = lean_array_uget_borrowed(v_as_1215_, v_i_1217_);
if (lean_obj_tag(v_a_1245_) == 0)
{
lean_object* v_ctorName_1264_; lean_object* v_params_1265_; lean_object* v_code_1266_; lean_object* v___x_1267_; 
lean_del_object(v___x_1242_);
lean_del_object(v___x_1237_);
v_ctorName_1264_ = lean_ctor_get(v_a_1245_, 0);
v_params_1265_ = lean_ctor_get(v_a_1245_, 1);
v_code_1266_ = lean_ctor_get(v_a_1245_, 2);
lean_inc_ref(v_params_1265_);
lean_inc(v_ctorName_1264_);
lean_inc(v_discr_1209_);
v___x_1267_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1209_, v_ctorName_1264_, v_params_1265_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
lean_inc_ref(v_code_1266_);
v___x_1269_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1266_, v___y_1219_, v___y_1220_, v_a_1268_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v_a_1268_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = l_Lean_NameSet_contains(v___x_1210_, v_ctorName_1264_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc_ref(v_a_1245_);
v___x_1272_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1245_, v_a_1270_);
v___x_1273_ = lean_array_push(v_snd_1240_, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_fst_1239_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_fst_1235_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v_a_1228_ = v___x_1275_;
goto v___jp_1227_;
}
else
{
lean_object* v_paramIdx_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; 
v_paramIdx_1276_ = lean_ctor_get(v_val_1211_, 0);
v___x_1277_ = 0;
lean_inc(v_a_1270_);
lean_inc_ref(v_params_1265_);
lean_inc_ref(v_fst_1212_);
v___x_1278_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1212_, v_params_1213_, v_paramIdx_1276_, v_params_1265_, v_a_1270_, v___x_1277_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_decl_1280_; uint8_t v_dependsOnDiscr_1281_; lean_object* v___x_1282_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v_decl_1280_ = lean_ctor_get(v_a_1279_, 0);
v_dependsOnDiscr_1281_ = lean_ctor_get_uint8(v_a_1279_, sizeof(void*)*1 + 1);
v___x_1282_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1244_, v_a_1270_, v___y_1223_);
lean_dec(v_a_1270_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_fvarId_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref_known(v___x_1282_, 1);
v_fvarId_1283_ = lean_ctor_get(v_decl_1280_, 0);
lean_inc(v_fvarId_1283_);
lean_inc_ref(v_decl_1280_);
v___x_1284_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1284_, 0, v_decl_1280_);
v___x_1285_ = lean_array_push(v_fst_1239_, v___x_1284_);
lean_inc(v_ctorName_1264_);
v___x_1286_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_ctorName_1264_, v_a_1279_, v_fst_1235_);
lean_inc_ref(v_params_1265_);
lean_inc(v_paramIdx_1276_);
lean_inc_ref(v_params_1213_);
v___x_1287_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1213_, v_paramIdx_1276_, v_params_1265_, v_dependsOnDiscr_1281_);
v___x_1288_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_fvarId_1283_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
lean_inc_ref(v_a_1245_);
v___x_1289_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1245_, v___x_1288_);
v___x_1290_ = lean_array_push(v_snd_1240_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1285_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1286_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v_a_1228_ = v___x_1292_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_a_1279_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_dec(v_fst_1235_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1293_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1282_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1282_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_a_1270_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_dec(v_fst_1235_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1301_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1278_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1278_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_dec(v_fst_1235_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1309_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1269_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1269_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_dec(v_fst_1235_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1317_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1267_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1267_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_code_1325_; lean_object* v___x_1326_; 
v_code_1325_ = lean_ctor_get(v_a_1245_, 0);
lean_inc_ref(v_code_1325_);
v___x_1326_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1325_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1333_; lean_object* v___y_1335_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v_a_1383_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1333_ = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(v_snd_1214_);
v___x_1381_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v___x_1382_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1333_, v___x_1381_, v___x_1210_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___y_1335_ = v_a_1383_;
goto v___jp_1334_;
v___jp_1328_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_inc_ref(v_a_1245_);
v___x_1329_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1245_, v_a_1327_);
v___x_1330_ = lean_array_push(v_snd_1240_, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_fst_1239_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v_fst_1235_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v_a_1228_ = v___x_1332_;
goto v___jp_1227_;
}
v___jp_1334_:
{
lean_object* v_fst_1336_; 
v_fst_1336_ = lean_ctor_get(v___y_1335_, 0);
lean_inc(v_fst_1336_);
lean_dec_ref(v___y_1335_);
if (lean_obj_tag(v_fst_1336_) == 0)
{
lean_dec(v___x_1333_);
lean_del_object(v___x_1242_);
lean_del_object(v___x_1237_);
goto v___jp_1328_;
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1380_; 
v_val_1337_ = lean_ctor_get(v_fst_1336_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_fst_1336_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1339_ = v_fst_1336_;
v_isShared_1340_ = v_isSharedCheck_1380_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_val_1337_);
lean_dec(v_fst_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1380_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_unbox(v_val_1337_);
lean_dec(v_val_1337_);
if (v___x_1341_ == 0)
{
lean_del_object(v___x_1339_);
lean_dec(v___x_1333_);
lean_del_object(v___x_1242_);
lean_del_object(v___x_1237_);
goto v___jp_1328_;
}
else
{
lean_object* v_paramIdx_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_paramIdx_1342_ = lean_ctor_get(v_val_1211_, 0);
v___x_1343_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
lean_inc(v_a_1327_);
lean_inc_ref(v_fst_1212_);
v___x_1344_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1212_, v_params_1213_, v_paramIdx_1342_, v___x_1343_, v_a_1327_, v___x_1232_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v_decl_1346_; uint8_t v_dependsOnDiscr_1347_; lean_object* v___x_1348_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v_decl_1346_ = lean_ctor_get(v_a_1345_, 0);
lean_inc_ref(v_decl_1346_);
v_dependsOnDiscr_1347_ = lean_ctor_get_uint8(v_a_1345_, sizeof(void*)*1 + 1);
v___x_1348_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1244_, v_a_1327_, v___y_1223_);
lean_dec(v_a_1327_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref_known(v___x_1348_, 1);
lean_inc(v___x_1210_);
v___x_1349_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1333_, v_a_1345_, v_fst_1235_, v___x_1210_);
lean_dec(v___x_1333_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
lean_inc_ref(v_decl_1346_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 2);
lean_ctor_set(v___x_1339_, 0, v_decl_1346_);
v___x_1352_ = v___x_1339_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_decl_1346_);
v___x_1352_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v_a_1354_; 
v___x_1353_ = lean_array_push(v_fst_1239_, v___x_1352_);
v_a_1354_ = lean_ctor_get(v_a_1350_, 0);
lean_inc(v_a_1354_);
lean_dec(v_a_1350_);
lean_inc(v_paramIdx_1342_);
v___y_1247_ = v___x_1343_;
v___y_1248_ = v_paramIdx_1342_;
v___y_1249_ = v___x_1353_;
v___y_1250_ = v_decl_1346_;
v___y_1251_ = v_dependsOnDiscr_1347_;
v_a_1252_ = v_a_1354_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v_decl_1346_);
lean_del_object(v___x_1339_);
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1356_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1349_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1349_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v_decl_1346_);
lean_dec(v_a_1345_);
lean_del_object(v___x_1339_);
lean_dec(v___x_1333_);
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec(v_fst_1235_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1364_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1348_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1348_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_del_object(v___x_1339_);
lean_dec(v___x_1333_);
lean_dec(v_a_1327_);
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec(v_fst_1235_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1372_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1344_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1344_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
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
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1237_);
lean_dec(v_fst_1235_);
lean_dec_ref(v_params_1213_);
lean_dec_ref(v_fst_1212_);
lean_dec_ref(v_val_1211_);
lean_dec(v___x_1210_);
lean_dec(v_discr_1209_);
v_a_1384_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1326_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1326_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
v___jp_1246_:
{
lean_object* v_fvarId_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_fvarId_1253_ = lean_ctor_get(v___y_1250_, 0);
lean_inc(v_fvarId_1253_);
lean_dec_ref(v___y_1250_);
lean_inc_ref(v_params_1213_);
v___x_1254_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1213_, v___y_1248_, v___y_1247_, v___y_1251_);
v___x_1255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_fvarId_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
lean_inc(v_a_1245_);
v___x_1256_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1245_, v___x_1255_);
v___x_1257_ = lean_array_push(v_snd_1240_, v___x_1256_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1257_);
lean_ctor_set(v___x_1242_, 0, v___y_1249_);
v___x_1259_ = v___x_1242_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___y_1249_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___x_1259_);
lean_ctor_set(v___x_1237_, 0, v_a_1252_);
v___x_1261_ = v___x_1237_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1252_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v_a_1228_ = v___x_1261_;
goto v___jp_1227_;
}
}
}
}
}
}
v___jp_1227_:
{
size_t v___x_1229_; size_t v___x_1230_; 
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_add(v_i_1217_, v___x_1229_);
v_i_1217_ = v___x_1230_;
v_b_1218_ = v_a_1228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object* v_decl_1394_, lean_object* v_k_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_fvarId_1404_; lean_object* v_params_1405_; lean_object* v_type_1406_; lean_object* v_value_1407_; lean_object* v___x_1408_; 
v_fvarId_1404_ = lean_ctor_get(v_decl_1394_, 0);
v_params_1405_ = lean_ctor_get(v_decl_1394_, 2);
lean_inc_ref(v_params_1405_);
v_type_1406_ = lean_ctor_get(v_decl_1394_, 3);
lean_inc_ref(v_type_1406_);
v_value_1407_ = lean_ctor_get(v_decl_1394_, 4);
v___x_1408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_1396_, v_fvarId_1404_);
if (lean_obj_tag(v___x_1408_) == 1)
{
lean_object* v_val_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1485_; 
v_val_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1485_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_val_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1485_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_ctorNames_1413_; 
v_ctorNames_1413_ = lean_ctor_get(v_val_1409_, 1);
lean_inc(v_ctorNames_1413_);
if (lean_obj_tag(v_ctorNames_1413_) == 0)
{
lean_object* v___x_1414_; lean_object* v_snd_1415_; lean_object* v_fst_1416_; lean_object* v_typeName_1417_; lean_object* v_resultType_1418_; lean_object* v_discr_1419_; lean_object* v_alts_1420_; lean_object* v___x_1421_; size_t v_sz_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1414_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_value_1407_);
v_snd_1415_ = lean_ctor_get(v___x_1414_, 1);
lean_inc(v_snd_1415_);
v_fst_1416_ = lean_ctor_get(v___x_1414_, 0);
lean_inc_n(v_fst_1416_, 2);
lean_dec_ref(v___x_1414_);
v_typeName_1417_ = lean_ctor_get(v_snd_1415_, 0);
lean_inc(v_typeName_1417_);
v_resultType_1418_ = lean_ctor_get(v_snd_1415_, 1);
lean_inc_ref(v_resultType_1418_);
v_discr_1419_ = lean_ctor_get(v_snd_1415_, 2);
lean_inc_n(v_discr_1419_, 2);
v_alts_1420_ = lean_ctor_get(v_snd_1415_, 3);
lean_inc_ref(v_alts_1420_);
v___x_1421_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1));
v_sz_1422_ = lean_array_size(v_alts_1420_);
v___x_1423_ = ((size_t)0ULL);
lean_inc_ref(v_params_1405_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1419_, v_ctorNames_1413_, v_val_1409_, v_fst_1416_, v_params_1405_, v_snd_1415_, v_alts_1420_, v_sz_1422_, v___x_1423_, v___x_1421_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec_ref(v_alts_1420_);
lean_dec(v_snd_1415_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1474_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = lean_st_ref_take(v_a_1397_);
v_fst_1427_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_fst_1427_);
v_snd_1428_ = lean_ctor_get(v_a_1425_, 1);
lean_inc(v_snd_1428_);
lean_dec(v_a_1425_);
lean_inc(v_fvarId_1404_);
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1404_, v_fst_1427_, v___x_1426_);
v___x_1430_ = lean_st_ref_put(v_a_1397_, v___x_1429_);
v_fst_1431_ = lean_ctor_get(v_snd_1428_, 0);
v_snd_1432_ = lean_ctor_get(v_snd_1428_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_snd_1428_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1434_ = v_snd_1428_;
v_isShared_1435_ = v_isSharedCheck_1474_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v_snd_1428_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1474_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1436_ = 0;
v___x_1437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1437_, 0, v_typeName_1417_);
lean_ctor_set(v___x_1437_, 1, v_resultType_1418_);
lean_ctor_set(v___x_1437_, 2, v_discr_1419_);
lean_ctor_set(v___x_1437_, 3, v_snd_1432_);
v___x_1438_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
v___x_1439_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1436_, v_fst_1416_, v___x_1438_);
lean_dec(v_fst_1416_);
v___x_1440_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1436_, v_decl_1394_, v_type_1406_, v_params_1405_, v___x_1439_, v_a_1400_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1457_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1457_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1457_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 2);
lean_ctor_set(v___x_1434_, 1, v_a_1443_);
lean_ctor_set(v___x_1434_, 0, v_a_1441_);
v___x_1448_ = v___x_1434_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1441_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1436_, v_fst_1431_, v___x_1448_);
lean_dec(v_fst_1431_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1449_);
v___x_1451_ = v___x_1411_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1451_);
v___x_1453_ = v___x_1445_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_a_1441_);
lean_del_object(v___x_1434_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1411_);
v_a_1458_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1442_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1442_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_del_object(v___x_1434_);
lean_dec(v_fst_1431_);
lean_del_object(v___x_1411_);
lean_dec_ref(v_k_1395_);
v_a_1466_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1440_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1440_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_discr_1419_);
lean_dec_ref(v_resultType_1418_);
lean_dec(v_typeName_1417_);
lean_dec(v_fst_1416_);
lean_del_object(v___x_1411_);
lean_dec_ref(v_type_1406_);
lean_dec_ref(v_params_1405_);
lean_dec_ref(v_k_1395_);
lean_dec_ref(v_decl_1394_);
v_a_1475_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1424_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1424_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_del_object(v___x_1411_);
lean_dec(v_val_1409_);
lean_dec_ref(v_type_1406_);
lean_dec_ref(v_params_1405_);
lean_dec_ref(v_k_1395_);
lean_dec_ref(v_decl_1394_);
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v___x_1408_);
lean_dec_ref(v_type_1406_);
lean_dec_ref(v_params_1405_);
lean_dec_ref(v_k_1395_);
lean_dec_ref(v_decl_1394_);
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object* v_code_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
switch(lean_obj_tag(v_code_1488_))
{
case 0:
{
lean_object* v_decl_1497_; lean_object* v_k_1498_; lean_object* v___x_1499_; 
v_decl_1497_ = lean_ctor_get(v_code_1488_, 0);
v_k_1498_ = lean_ctor_get(v_code_1488_, 1);
lean_inc_ref(v_k_1498_);
v___x_1499_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1498_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1526_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1526_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1526_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
uint8_t v___y_1505_; size_t v___x_1521_; size_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_ptr_addr(v_k_1498_);
v___x_1522_ = lean_ptr_addr(v_a_1500_);
v___x_1523_ = lean_usize_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
v___y_1505_ = v___x_1523_;
goto v___jp_1504_;
}
else
{
size_t v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = lean_ptr_addr(v_decl_1497_);
v___x_1525_ = lean_usize_dec_eq(v___x_1524_, v___x_1524_);
v___y_1505_ = v___x_1525_;
goto v___jp_1504_;
}
v___jp_1504_:
{
if (v___y_1505_ == 0)
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1515_; 
lean_inc_ref(v_decl_1497_);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_code_1488_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; 
v_unused_1516_ = lean_ctor_get(v_code_1488_, 1);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_code_1488_, 0);
lean_dec(v_unused_1517_);
v___x_1507_ = v_code_1488_;
v_isShared_1508_ = v_isSharedCheck_1515_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_code_1488_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1515_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_a_1500_);
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_decl_1497_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_a_1500_);
v___x_1510_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1510_);
v___x_1512_ = v___x_1502_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v___x_1519_; 
lean_dec(v_a_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v_code_1488_);
v___x_1519_ = v___x_1502_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_code_1488_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1488_, 2);
return v___x_1499_;
}
}
case 1:
{
lean_object* v_decl_1527_; lean_object* v_k_1528_; lean_object* v_params_1529_; lean_object* v_type_1530_; lean_object* v_value_1531_; lean_object* v___x_1532_; 
v_decl_1527_ = lean_ctor_get(v_code_1488_, 0);
v_k_1528_ = lean_ctor_get(v_code_1488_, 1);
v_params_1529_ = lean_ctor_get(v_decl_1527_, 2);
v_type_1530_ = lean_ctor_get(v_decl_1527_, 3);
v_value_1531_ = lean_ctor_get(v_decl_1527_, 4);
lean_inc_ref(v_value_1531_);
v___x_1532_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1531_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = 0;
lean_inc_ref(v_params_1529_);
lean_inc_ref(v_type_1530_);
lean_inc_ref(v_decl_1527_);
v___x_1535_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1534_, v_decl_1527_, v_type_1530_, v_params_1529_, v_a_1533_, v_a_1493_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
lean_inc_ref(v_k_1528_);
v___x_1537_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1528_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1565_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1565_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1565_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
uint8_t v___y_1543_; size_t v___x_1559_; size_t v___x_1560_; uint8_t v___x_1561_; 
v___x_1559_ = lean_ptr_addr(v_k_1528_);
v___x_1560_ = lean_ptr_addr(v_a_1538_);
v___x_1561_ = lean_usize_dec_eq(v___x_1559_, v___x_1560_);
if (v___x_1561_ == 0)
{
v___y_1543_ = v___x_1561_;
goto v___jp_1542_;
}
else
{
size_t v___x_1562_; size_t v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = lean_ptr_addr(v_decl_1527_);
v___x_1563_ = lean_ptr_addr(v_a_1536_);
v___x_1564_ = lean_usize_dec_eq(v___x_1562_, v___x_1563_);
v___y_1543_ = v___x_1564_;
goto v___jp_1542_;
}
v___jp_1542_:
{
if (v___y_1543_ == 0)
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1553_; 
v_isSharedCheck_1553_ = !lean_is_exclusive(v_code_1488_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; lean_object* v_unused_1555_; 
v_unused_1554_ = lean_ctor_get(v_code_1488_, 1);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_code_1488_, 0);
lean_dec(v_unused_1555_);
v___x_1545_ = v_code_1488_;
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v_code_1488_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v_a_1538_);
lean_ctor_set(v___x_1545_, 0, v_a_1536_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1536_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_a_1538_);
v___x_1548_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1550_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1548_);
v___x_1550_ = v___x_1540_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v___x_1557_; 
lean_dec(v_a_1538_);
lean_dec(v_a_1536_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_code_1488_);
v___x_1557_ = v___x_1540_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_code_1488_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
else
{
lean_dec(v_a_1536_);
lean_dec_ref_known(v_code_1488_, 2);
return v___x_1537_;
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref_known(v_code_1488_, 2);
v_a_1566_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1535_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1535_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1488_, 2);
return v___x_1532_;
}
}
case 2:
{
lean_object* v_decl_1574_; lean_object* v_k_1575_; lean_object* v___x_1576_; 
v_decl_1574_ = lean_ctor_get(v_code_1488_, 0);
v_k_1575_ = lean_ctor_get(v_code_1488_, 1);
lean_inc_ref(v_k_1575_);
lean_inc_ref(v_decl_1574_);
v___x_1576_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1574_, v_k_1575_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1630_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1630_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1630_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
if (lean_obj_tag(v_a_1577_) == 1)
{
lean_object* v_val_1581_; lean_object* v___x_1583_; 
lean_dec_ref_known(v_code_1488_, 2);
v_val_1581_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v_a_1577_, 1);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_val_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_val_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
else
{
lean_object* v_params_1585_; lean_object* v_type_1586_; lean_object* v_value_1587_; lean_object* v___x_1588_; 
lean_del_object(v___x_1579_);
lean_dec(v_a_1577_);
v_params_1585_ = lean_ctor_get(v_decl_1574_, 2);
v_type_1586_ = lean_ctor_get(v_decl_1574_, 3);
v_value_1587_ = lean_ctor_get(v_decl_1574_, 4);
lean_inc_ref(v_value_1587_);
v___x_1588_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1587_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1590_ = 0;
lean_inc_ref(v_params_1585_);
lean_inc_ref(v_type_1586_);
lean_inc_ref(v_decl_1574_);
v___x_1591_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1590_, v_decl_1574_, v_type_1586_, v_params_1585_, v_a_1589_, v_a_1493_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
lean_inc_ref(v_k_1575_);
v___x_1593_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1575_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1621_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1621_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1621_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
uint8_t v___y_1599_; size_t v___x_1615_; size_t v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = lean_ptr_addr(v_k_1575_);
v___x_1616_ = lean_ptr_addr(v_a_1594_);
v___x_1617_ = lean_usize_dec_eq(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
v___y_1599_ = v___x_1617_;
goto v___jp_1598_;
}
else
{
size_t v___x_1618_; size_t v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = lean_ptr_addr(v_decl_1574_);
v___x_1619_ = lean_ptr_addr(v_a_1592_);
v___x_1620_ = lean_usize_dec_eq(v___x_1618_, v___x_1619_);
v___y_1599_ = v___x_1620_;
goto v___jp_1598_;
}
v___jp_1598_:
{
if (v___y_1599_ == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1609_; 
v_isSharedCheck_1609_ = !lean_is_exclusive(v_code_1488_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; 
v_unused_1610_ = lean_ctor_get(v_code_1488_, 1);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_code_1488_, 0);
lean_dec(v_unused_1611_);
v___x_1601_ = v_code_1488_;
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v_code_1488_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1609_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v_a_1594_);
lean_ctor_set(v___x_1601_, 0, v_a_1592_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1592_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_a_1594_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1604_);
v___x_1606_ = v___x_1596_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v___x_1613_; 
lean_dec(v_a_1594_);
lean_dec(v_a_1592_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_code_1488_);
v___x_1613_ = v___x_1596_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_code_1488_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
else
{
lean_dec(v_a_1592_);
lean_dec_ref_known(v_code_1488_, 2);
return v___x_1593_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref_known(v_code_1488_, 2);
v_a_1622_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1591_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1591_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1488_, 2);
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref_known(v_code_1488_, 2);
v_a_1631_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1576_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1576_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1639_; lean_object* v_args_1640_; lean_object* v___x_1641_; 
v_fvarId_1639_ = lean_ctor_get(v_code_1488_, 0);
v_args_1640_ = lean_ctor_get(v_code_1488_, 1);
lean_inc_ref(v_args_1640_);
v___x_1641_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1639_, v_args_1640_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1653_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1653_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1653_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
if (lean_obj_tag(v_a_1642_) == 1)
{
lean_object* v_val_1646_; lean_object* v___x_1648_; 
lean_dec_ref_known(v_code_1488_, 2);
v_val_1646_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_val_1646_);
lean_dec_ref_known(v_a_1642_, 1);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_val_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
else
{
lean_object* v___x_1651_; 
lean_dec(v_a_1642_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_code_1488_);
v___x_1651_ = v___x_1644_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_code_1488_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref_known(v_code_1488_, 2);
v_a_1654_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1641_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1641_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
case 4:
{
lean_object* v_cases_1662_; lean_object* v_typeName_1663_; lean_object* v_resultType_1664_; lean_object* v_discr_1665_; lean_object* v_alts_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1705_; 
v_cases_1662_ = lean_ctor_get(v_code_1488_, 0);
lean_inc_ref(v_cases_1662_);
v_typeName_1663_ = lean_ctor_get(v_cases_1662_, 0);
v_resultType_1664_ = lean_ctor_get(v_cases_1662_, 1);
v_discr_1665_ = lean_ctor_get(v_cases_1662_, 2);
v_alts_1666_ = lean_ctor_get(v_cases_1662_, 3);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_cases_1662_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1668_ = v_cases_1662_;
v_isShared_1669_ = v_isSharedCheck_1705_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_alts_1666_);
lean_inc(v_discr_1665_);
lean_inc(v_resultType_1664_);
lean_inc(v_typeName_1663_);
lean_dec(v_cases_1662_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1705_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1666_);
lean_inc(v_discr_1665_);
v___x_1671_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1665_, v___x_1670_, v_alts_1666_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1696_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
size_t v___x_1676_; size_t v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = lean_ptr_addr(v_alts_1666_);
lean_dec_ref(v_alts_1666_);
v___x_1677_ = lean_ptr_addr(v_a_1672_);
v___x_1678_ = lean_usize_dec_eq(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1691_; 
v_isSharedCheck_1691_ = !lean_is_exclusive(v_code_1488_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v_code_1488_, 0);
lean_dec(v_unused_1692_);
v___x_1680_ = v_code_1488_;
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v_code_1488_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 3, v_a_1672_);
v___x_1683_ = v___x_1668_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_typeName_1663_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_resultType_1664_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_discr_1665_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_a_1672_);
v___x_1683_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1683_);
v___x_1685_ = v___x_1680_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1685_);
v___x_1687_ = v___x_1674_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
else
{
lean_object* v___x_1694_; 
lean_dec(v_a_1672_);
lean_del_object(v___x_1668_);
lean_dec(v_discr_1665_);
lean_dec_ref(v_resultType_1664_);
lean_dec(v_typeName_1663_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v_code_1488_);
v___x_1694_ = v___x_1674_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_code_1488_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_del_object(v___x_1668_);
lean_dec_ref(v_alts_1666_);
lean_dec(v_discr_1665_);
lean_dec_ref(v_resultType_1664_);
lean_dec(v_typeName_1663_);
lean_dec_ref_known(v_code_1488_, 1);
v_a_1697_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1671_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1671_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
default: 
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_code_1488_);
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object* v_discr_1707_, lean_object* v_i_1708_, lean_object* v_as_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_array_get_size(v_as_1709_);
v___x_1719_ = lean_nat_dec_lt(v_i_1708_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_i_1708_);
lean_dec(v_discr_1707_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_as_1709_);
return v___x_1720_;
}
else
{
lean_object* v_a_1721_; lean_object* v_a_1723_; 
v_a_1721_ = lean_array_fget_borrowed(v_as_1709_, v_i_1708_);
if (lean_obj_tag(v_a_1721_) == 0)
{
lean_object* v_ctorName_1734_; lean_object* v_params_1735_; lean_object* v_code_1736_; lean_object* v___x_1737_; 
v_ctorName_1734_ = lean_ctor_get(v_a_1721_, 0);
v_params_1735_ = lean_ctor_get(v_a_1721_, 1);
v_code_1736_ = lean_ctor_get(v_a_1721_, 2);
lean_inc_ref(v_params_1735_);
lean_inc(v_ctorName_1734_);
lean_inc(v_discr_1707_);
v___x_1737_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1707_, v_ctorName_1734_, v_params_1735_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1739_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
lean_inc_ref(v_code_1736_);
v___x_1739_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1736_, v___y_1710_, v___y_1711_, v_a_1738_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v_a_1738_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
lean_inc_ref(v_a_1721_);
v___x_1741_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1721_, v_a_1740_);
v_a_1723_ = v___x_1741_;
goto v___jp_1722_;
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_as_1709_);
lean_dec(v_i_1708_);
lean_dec(v_discr_1707_);
v_a_1742_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1739_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1739_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v_as_1709_);
lean_dec(v_i_1708_);
lean_dec(v_discr_1707_);
v_a_1750_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1737_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1737_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_code_1758_; lean_object* v___x_1759_; 
v_code_1758_ = lean_ctor_get(v_a_1721_, 0);
lean_inc_ref(v_code_1758_);
v___x_1759_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1758_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1759_, 1);
lean_inc_ref(v_a_1721_);
v___x_1761_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1721_, v_a_1760_);
v_a_1723_ = v___x_1761_;
goto v___jp_1722_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v_as_1709_);
lean_dec(v_i_1708_);
lean_dec(v_discr_1707_);
v_a_1762_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1759_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1759_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
v___jp_1722_:
{
size_t v___x_1724_; size_t v___x_1725_; uint8_t v___x_1726_; 
v___x_1724_ = lean_ptr_addr(v_a_1721_);
v___x_1725_ = lean_ptr_addr(v_a_1723_);
v___x_1726_ = lean_usize_dec_eq(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v_i_1708_, v___x_1727_);
v___x_1729_ = lean_array_fset(v_as_1709_, v_i_1708_, v_a_1723_);
lean_dec(v_i_1708_);
v_i_1708_ = v___x_1728_;
v_as_1709_ = v___x_1729_;
goto _start;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_dec_ref(v_a_1723_);
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_add(v_i_1708_, v___x_1731_);
lean_dec(v_i_1708_);
v_i_1708_ = v___x_1732_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object* v_discr_1770_, lean_object* v_i_1771_, lean_object* v_as_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1770_, v_i_1771_, v_as_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec(v___y_1773_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object* v_decl_1782_, lean_object* v_k_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1782_, v_k_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec(v_a_1784_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object** _args){
lean_object* v_discr_1793_ = _args[0];
lean_object* v___x_1794_ = _args[1];
lean_object* v_val_1795_ = _args[2];
lean_object* v_fst_1796_ = _args[3];
lean_object* v_params_1797_ = _args[4];
lean_object* v_snd_1798_ = _args[5];
lean_object* v_as_1799_ = _args[6];
lean_object* v_sz_1800_ = _args[7];
lean_object* v_i_1801_ = _args[8];
lean_object* v_b_1802_ = _args[9];
lean_object* v___y_1803_ = _args[10];
lean_object* v___y_1804_ = _args[11];
lean_object* v___y_1805_ = _args[12];
lean_object* v___y_1806_ = _args[13];
lean_object* v___y_1807_ = _args[14];
lean_object* v___y_1808_ = _args[15];
lean_object* v___y_1809_ = _args[16];
lean_object* v___y_1810_ = _args[17];
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1793_, v___x_1794_, v_val_1795_, v_fst_1796_, v_params_1797_, v_snd_1798_, v_as_1799_, v_sz_boxed_1811_, v_i_boxed_1812_, v_b_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v_as_1799_);
lean_dec_ref(v_snd_1798_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object* v_code_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec(v_a_1815_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object* v___x_1824_, lean_object* v_a_1825_, lean_object* v_init_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1824_, v_a_1825_, v_init_1826_, v_x_1827_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object* v___x_1837_, lean_object* v_a_1838_, lean_object* v_init_1839_, lean_object* v_x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(v___x_1837_, v_a_1838_, v_init_1839_, v_x_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec(v___x_1837_);
return v_res_1849_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1);
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
lean_ctor_set(v___x_1855_, 2, v___x_1854_);
lean_ctor_set(v___x_1855_, 3, v___x_1854_);
lean_ctor_set(v___x_1855_, 4, v___x_1853_);
lean_ctor_set(v___x_1855_, 5, v___x_1853_);
lean_ctor_set(v___x_1855_, 6, v___x_1853_);
lean_ctor_set(v___x_1855_, 7, v___x_1853_);
lean_ctor_set(v___x_1855_, 8, v___x_1853_);
lean_ctor_set(v___x_1855_, 9, v___x_1853_);
lean_ctor_set(v___x_1855_, 10, v___x_1853_);
return v___x_1855_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1856_; double v___x_1857_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_float_of_nat(v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object* v_cls_1861_, lean_object* v_msg_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_options_1868_; lean_object* v_ref_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_options_1868_ = lean_ctor_get(v___y_1865_, 2);
v_ref_1869_ = lean_ctor_get(v___y_1865_, 5);
v___x_1870_ = lean_st_ref_get(v___y_1866_);
v___x_1871_ = lean_st_ref_get(v___y_1864_);
v___x_1872_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1863_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1931_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1931_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1931_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_env_1877_; lean_object* v_lctx_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1929_; 
v_env_1877_ = lean_ctor_get(v___x_1870_, 0);
lean_inc_ref(v_env_1877_);
lean_dec(v___x_1870_);
v_lctx_1878_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v___x_1871_, 1);
lean_dec(v_unused_1930_);
v___x_1880_ = v___x_1871_;
v_isShared_1881_ = v_isSharedCheck_1929_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_lctx_1878_);
lean_dec(v___x_1871_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1929_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v_traceState_1884_; lean_object* v_env_1885_; lean_object* v_nextMacroScope_1886_; lean_object* v_ngen_1887_; lean_object* v_auxDeclNGen_1888_; lean_object* v_cache_1889_; lean_object* v_messages_1890_; lean_object* v_infoState_1891_; lean_object* v_snapshotTasks_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1928_; 
v___x_1882_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2);
v___x_1883_ = lean_st_ref_take(v___y_1866_);
v_traceState_1884_ = lean_ctor_get(v___x_1883_, 4);
v_env_1885_ = lean_ctor_get(v___x_1883_, 0);
v_nextMacroScope_1886_ = lean_ctor_get(v___x_1883_, 1);
v_ngen_1887_ = lean_ctor_get(v___x_1883_, 2);
v_auxDeclNGen_1888_ = lean_ctor_get(v___x_1883_, 3);
v_cache_1889_ = lean_ctor_get(v___x_1883_, 5);
v_messages_1890_ = lean_ctor_get(v___x_1883_, 6);
v_infoState_1891_ = lean_ctor_get(v___x_1883_, 7);
v_snapshotTasks_1892_ = lean_ctor_get(v___x_1883_, 8);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1894_ = v___x_1883_;
v_isShared_1895_ = v_isSharedCheck_1928_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_snapshotTasks_1892_);
lean_inc(v_infoState_1891_);
lean_inc(v_messages_1890_);
lean_inc(v_cache_1889_);
lean_inc(v_traceState_1884_);
lean_inc(v_auxDeclNGen_1888_);
lean_inc(v_ngen_1887_);
lean_inc(v_nextMacroScope_1886_);
lean_inc(v_env_1885_);
lean_dec(v___x_1883_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1928_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
uint64_t v_tid_1896_; lean_object* v_traces_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1927_; 
v_tid_1896_ = lean_ctor_get_uint64(v_traceState_1884_, sizeof(void*)*1);
v_traces_1897_ = lean_ctor_get(v_traceState_1884_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_traceState_1884_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1899_ = v_traceState_1884_;
v_isShared_1900_ = v_isSharedCheck_1927_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_traces_1897_);
lean_dec(v_traceState_1884_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1927_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1901_ = lean_unbox(v_a_1873_);
lean_dec(v_a_1873_);
v___x_1902_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1878_, v___x_1901_);
lean_dec_ref(v_lctx_1878_);
lean_inc_ref(v_options_1868_);
v___x_1903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1903_, 0, v_env_1877_);
lean_ctor_set(v___x_1903_, 1, v___x_1882_);
lean_ctor_set(v___x_1903_, 2, v___x_1902_);
lean_ctor_set(v___x_1903_, 3, v_options_1868_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 3);
lean_ctor_set(v___x_1880_, 1, v_msg_1862_);
lean_ctor_set(v___x_1880_, 0, v___x_1903_);
v___x_1905_ = v___x_1880_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_msg_1862_);
v___x_1905_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; double v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3);
v___x_1908_ = 0;
v___x_1909_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4));
v___x_1910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1910_, 0, v_cls_1861_);
lean_ctor_set(v___x_1910_, 1, v___x_1906_);
lean_ctor_set(v___x_1910_, 2, v___x_1909_);
lean_ctor_set_float(v___x_1910_, sizeof(void*)*3, v___x_1907_);
lean_ctor_set_float(v___x_1910_, sizeof(void*)*3 + 8, v___x_1907_);
lean_ctor_set_uint8(v___x_1910_, sizeof(void*)*3 + 16, v___x_1908_);
v___x_1911_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5));
v___x_1912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1905_);
lean_ctor_set(v___x_1912_, 2, v___x_1911_);
lean_inc(v_ref_1869_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_ref_1869_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_PersistentArray_push___redArg(v_traces_1897_, v___x_1913_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1914_);
v___x_1916_ = v___x_1899_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1914_);
lean_ctor_set_uint64(v_reuseFailAlloc_1925_, sizeof(void*)*1, v_tid_1896_);
v___x_1916_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 4, v___x_1916_);
v___x_1918_ = v___x_1894_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_env_1885_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_nextMacroScope_1886_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_ngen_1887_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_auxDeclNGen_1888_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1924_, 5, v_cache_1889_);
lean_ctor_set(v_reuseFailAlloc_1924_, 6, v_messages_1890_);
lean_ctor_set(v_reuseFailAlloc_1924_, 7, v_infoState_1891_);
lean_ctor_set(v_reuseFailAlloc_1924_, 8, v_snapshotTasks_1892_);
v___x_1918_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1919_ = lean_st_ref_put(v___y_1866_, v___x_1918_);
v___x_1920_ = lean_box(0);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1920_);
v___x_1922_ = v___x_1875_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
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
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v___x_1871_);
lean_dec(v___x_1870_);
lean_dec_ref(v_msg_1862_);
lean_dec(v_cls_1861_);
v_a_1932_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1872_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1872_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object* v_cls_1940_, lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v_cls_1940_, v_msg_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object* v_init_1948_, lean_object* v_x_1949_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
lean_object* v_k_1950_; lean_object* v_v_1951_; lean_object* v_l_1952_; lean_object* v_r_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_k_1950_ = lean_ctor_get(v_x_1949_, 1);
v_v_1951_ = lean_ctor_get(v_x_1949_, 2);
v_l_1952_ = lean_ctor_get(v_x_1949_, 3);
v_r_1953_ = lean_ctor_get(v_x_1949_, 4);
v___x_1954_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_1948_, v_r_1953_);
lean_inc(v_v_1951_);
lean_inc(v_k_1950_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_k_1950_);
lean_ctor_set(v___x_1955_, 1, v_v_1951_);
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v___x_1954_);
v_init_1948_ = v___x_1956_;
v_x_1949_ = v_l_1952_;
goto _start;
}
else
{
return v_init_1948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object* v_init_1958_, lean_object* v_x_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_1958_, v_x_1959_);
lean_dec(v_x_1959_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
if (lean_obj_tag(v_a_1961_) == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = l_List_reverse___redArg(v_a_1962_);
return v___x_1963_;
}
else
{
lean_object* v_head_1964_; lean_object* v_tail_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1974_; 
v_head_1964_ = lean_ctor_get(v_a_1961_, 0);
v_tail_1965_ = lean_ctor_get(v_a_1961_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_a_1961_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1967_ = v_a_1961_;
v_isShared_1968_ = v_isSharedCheck_1974_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_tail_1965_);
lean_inc(v_head_1964_);
lean_dec(v_a_1961_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1974_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = l_Lean_MessageData_ofName(v_head_1964_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_a_1962_);
lean_ctor_set(v___x_1967_, 0, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_a_1962_);
v___x_1971_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
v_a_1961_ = v_tail_1965_;
v_a_1962_ = v___x_1971_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object* v_init_1975_, lean_object* v_x_1976_){
_start:
{
if (lean_obj_tag(v_x_1976_) == 0)
{
lean_object* v_k_1977_; lean_object* v_l_1978_; lean_object* v_r_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_k_1977_ = lean_ctor_get(v_x_1976_, 1);
v_l_1978_ = lean_ctor_get(v_x_1976_, 3);
v_r_1979_ = lean_ctor_get(v_x_1976_, 4);
v___x_1980_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_1975_, v_r_1979_);
lean_inc(v_k_1977_);
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_k_1977_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v_init_1975_ = v___x_1981_;
v_x_1976_ = v_l_1978_;
goto _start;
}
else
{
return v_init_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object* v_init_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_1983_, v_x_1984_);
lean_dec(v_x_1984_);
return v_res_1985_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0));
v___x_1988_ = l_Lean_stringToMessageData(v___x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(lean_object* v_as_x27_1989_, lean_object* v_b_1990_){
_start:
{
if (lean_obj_tag(v_as_x27_1989_) == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_b_1990_);
return v___x_1992_;
}
else
{
lean_object* v_head_1993_; lean_object* v_snd_1994_; lean_object* v_tail_1995_; lean_object* v_fst_1996_; lean_object* v_ctorNames_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_head_1993_ = lean_ctor_get(v_as_x27_1989_, 0);
v_snd_1994_ = lean_ctor_get(v_head_1993_, 1);
v_tail_1995_ = lean_ctor_get(v_as_x27_1989_, 1);
v_fst_1996_ = lean_ctor_get(v_head_1993_, 0);
v_ctorNames_1997_ = lean_ctor_get(v_snd_1994_, 1);
lean_inc(v_fst_1996_);
v___x_1998_ = l_Lean_mkFVar(v_fst_1996_);
v___x_1999_ = l_Lean_MessageData_ofExpr(v___x_1998_);
v___x_2000_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_box(0);
v___x_2003_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v___x_2002_, v_ctorNames_1997_);
v___x_2004_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(v___x_2003_, v___x_2002_);
v___x_2005_ = l_Lean_MessageData_ofList(v___x_2004_);
v___x_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2001_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = l_Lean_indentD(v___x_2006_);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_b_1990_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v_as_x27_1989_ = v_tail_1995_;
v_b_1990_ = v___x_2008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___boxed(lean_object* v_as_x27_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2010_, v_b_2011_);
lean_dec(v_as_x27_2010_);
return v_res_2013_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2025_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5));
v___x_2026_ = l_Lean_Name_append(v___x_2025_, v___x_2024_);
return v___x_2026_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8));
v___x_2031_ = l_Lean_MessageData_ofFormat(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object* v_code_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; 
lean_inc_ref(v_code_2032_);
v___x_2038_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2091_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2091_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2091_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_a_2039_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
lean_dec(v_a_2039_);
lean_dec_ref(v_code_2032_);
v___x_2067_ = lean_box(0);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2067_);
v___x_2069_ = v___x_2041_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
else
{
lean_object* v_options_2071_; uint8_t v_hasTrace_2072_; 
lean_del_object(v___x_2041_);
v_options_2071_ = lean_ctor_get(v_a_2035_, 2);
v_hasTrace_2072_ = lean_ctor_get_uint8(v_options_2071_, sizeof(void*)*1);
if (v_hasTrace_2072_ == 0)
{
goto v___jp_2043_;
}
else
{
lean_object* v_inheritedTraceOptions_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_inheritedTraceOptions_2073_ = lean_ctor_get(v_a_2035_, 13);
v___x_2074_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2075_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6);
v___x_2076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2073_, v_options_2071_, v___x_2075_);
if (v___x_2076_ == 0)
{
goto v___jp_2043_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_a_2081_; lean_object* v___x_2082_; 
v___x_2077_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9);
v___x_2078_ = lean_box(0);
v___x_2079_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v___x_2078_, v_a_2039_);
v___x_2080_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v___x_2079_, v___x_2077_);
lean_dec(v___x_2079_);
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v___x_2074_, v_a_2081_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_dec_ref_known(v___x_2082_, 1);
goto v___jp_2043_;
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_a_2039_);
lean_dec_ref(v_code_2032_);
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
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
v___jp_2043_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2044_ = lean_box(1);
v___x_2045_ = lean_st_mk_ref(v___x_2044_);
v___x_2046_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_2047_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_2032_, v_a_2039_, v___x_2045_, v___x_2046_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
lean_dec(v_a_2039_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2057_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2057_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2057_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2052_ = lean_st_ref_get(v___x_2045_);
lean_dec(v___x_2045_);
lean_dec(v___x_2052_);
v___x_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_a_2048_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2053_);
v___x_2055_ = v___x_2050_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v___x_2045_);
v_a_2058_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2047_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2047_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_code_2032_);
v_a_2092_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2038_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2038_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object* v_code_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v_code_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object* v_as_2107_, lean_object* v_as_x27_2108_, lean_object* v_b_2109_, lean_object* v_a_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2108_, v_b_2109_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object* v_as_2117_, lean_object* v_as_x27_2118_, lean_object* v_b_2119_, lean_object* v_a_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v_as_2117_, v_as_x27_2118_, v_b_2119_, v_a_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v_as_x27_2118_);
lean_dec(v_as_2117_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2201_ = 0;
v___x_2202_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_));
v___x_2203_ = l_Lean_registerTraceClass(v___x_2200_, v___x_2201_, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
return v_res_2205_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
