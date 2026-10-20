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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1___redArg();
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instSingletonFVarIdFVarIdSet___lam__0(lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4_value;
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
lean_object* v_val_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v_val_214_ = lean_ctor_get(v_a_210_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v_a_210_, 1);
v___x_215_ = lean_st_ref_take(v_a_144_);
v___x_216_ = lean_box(0);
v___x_217_ = l_Lean_NameSet_insert(v_ctorNames_202_, v_val_214_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_217_);
v___x_219_ = v___x_204_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_paramIdx_201_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_225_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_220_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_193_, v___x_219_, v___x_215_);
v___x_221_ = lean_st_ref_put(v_a_144_, v___x_220_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_216_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_216_);
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
lean_object* v_cases_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_263_; 
v_cases_247_ = lean_ctor_get(v_code_143_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v_code_143_);
if (v_isSharedCheck_263_ == 0)
{
v___x_249_ = v_code_143_;
v_isShared_250_ = v_isSharedCheck_263_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_cases_247_);
lean_dec(v_code_143_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_263_;
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
size_t v___x_260_; size_t v___x_261_; lean_object* v___x_262_; 
lean_del_object(v___x_249_);
v___x_260_ = ((size_t)0ULL);
v___x_261_ = lean_usize_of_nat(v___x_254_);
v___x_262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_251_, v_alts_252_, v___x_260_, v___x_261_, v___x_255_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec_ref(v_alts_252_);
return v___x_262_;
}
}
}
default: 
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_271_; 
v_isSharedCheck_271_ = !lean_is_exclusive(v_code_143_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_code_143_, 0);
lean_dec(v_unused_272_);
v___x_265_ = v_code_143_;
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
else
{
lean_dec(v_code_143_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 0);
lean_ctor_set(v___x_265_, 0, v___x_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object* v_discr_273_, lean_object* v_as_274_, size_t v_i_275_, size_t v_stop_276_, lean_object* v_b_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___y_286_; uint8_t v___x_291_; 
v___x_291_ = lean_usize_dec_eq(v_i_275_, v_stop_276_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = lean_array_uget_borrowed(v_as_274_, v_i_275_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_ctorName_293_; lean_object* v_params_294_; lean_object* v_code_295_; lean_object* v___x_296_; 
v_ctorName_293_ = lean_ctor_get(v___x_292_, 0);
v_params_294_ = lean_ctor_get(v___x_292_, 1);
v_code_295_ = lean_ctor_get(v___x_292_, 2);
lean_inc_ref(v_params_294_);
lean_inc(v_ctorName_293_);
lean_inc(v_discr_273_);
v___x_296_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_273_, v_ctorName_293_, v_params_294_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
lean_inc_ref(v_code_295_);
v___x_298_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_295_, v___y_278_, v_a_297_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v_a_297_);
v___y_286_ = v___x_298_;
goto v___jp_285_;
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_discr_273_);
v_a_299_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_296_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_296_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_code_307_; lean_object* v___x_308_; 
v_code_307_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_code_307_);
v___x_308_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_307_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
v___y_286_ = v___x_308_;
goto v___jp_285_;
}
}
else
{
lean_object* v___x_309_; 
lean_dec(v_discr_273_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v_b_277_);
return v___x_309_;
}
v___jp_285_:
{
if (lean_obj_tag(v___y_286_) == 0)
{
lean_object* v_a_287_; size_t v___x_288_; size_t v___x_289_; 
v_a_287_ = lean_ctor_get(v___y_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___y_286_, 1);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_add(v_i_275_, v___x_288_);
v_i_275_ = v___x_289_;
v_b_277_ = v_a_287_;
goto _start;
}
else
{
lean_dec(v_discr_273_);
return v___y_286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object* v_discr_310_, lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_stop_313_, lean_object* v_b_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
size_t v_i_boxed_322_; size_t v_stop_boxed_323_; lean_object* v_res_324_; 
v_i_boxed_322_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_stop_boxed_323_ = lean_unbox_usize(v_stop_313_);
lean_dec(v_stop_313_);
v_res_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_310_, v_as_311_, v_i_boxed_322_, v_stop_boxed_323_, v_b_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v_as_311_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object* v_code_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object* v_00_u03b4_334_, lean_object* v_t_335_, lean_object* v_k_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_335_, v_k_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object* v_00_u03b4_338_, lean_object* v_t_339_, lean_object* v_k_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(v_00_u03b4_338_, v_t_339_, v_k_340_);
lean_dec(v_k_340_);
lean_dec(v_t_339_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0(void){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1);
v___x_346_ = lean_box(1);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object* v_code_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_box(1);
v___x_355_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_356_ = lean_st_mk_ref(v___x_354_);
v___x_357_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_348_, v___x_356_, v___x_355_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_366_);
v___x_359_ = v___x_357_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_dec(v___x_357_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_st_ref_get(v___x_356_);
lean_dec(v___x_356_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v___x_356_);
v_a_367_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_357_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object* v_code_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_381_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Array_instInhabited___redArg();
return v___x_382_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1(void){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Compiler_LCNF_instInhabitedCases_default__1___redArg();
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(lean_object* v_msg_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0);
v___x_386_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_panic_fn_borrowed(v___x_387_, v_msg_384_);
lean_dec_ref_known(v___x_387_, 2);
return v___x_388_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2));
v___x_393_ = lean_unsigned_to_nat(11u);
v___x_394_ = lean_unsigned_to_nat(100u);
v___x_395_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1));
v___x_396_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0));
v___x_397_ = l_mkPanicMessageWithDecl(v___x_396_, v___x_395_, v___x_394_, v___x_393_, v___x_392_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(lean_object* v_code_398_, lean_object* v_decls_399_){
_start:
{
switch(lean_obj_tag(v_code_398_))
{
case 0:
{
lean_object* v_decl_400_; lean_object* v_k_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_decl_400_ = lean_ctor_get(v_code_398_, 0);
v_k_401_ = lean_ctor_get(v_code_398_, 1);
lean_inc_ref(v_decl_400_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v_decl_400_);
v___x_403_ = lean_array_push(v_decls_399_, v___x_402_);
v_code_398_ = v_k_401_;
v_decls_399_ = v___x_403_;
goto _start;
}
case 4:
{
lean_object* v_cases_405_; lean_object* v___x_406_; 
v_cases_405_ = lean_ctor_get(v_code_398_, 0);
lean_inc_ref(v_cases_405_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_decls_399_);
lean_ctor_set(v___x_406_, 1, v_cases_405_);
return v___x_406_;
}
default: 
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref(v_decls_399_);
v___x_407_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3);
v___x_408_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(v___x_407_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(lean_object* v_code_409_, lean_object* v_decls_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_409_, v_decls_410_);
lean_dec_ref(v_code_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(lean_object* v_code_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0));
v___x_416_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_414_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(lean_object* v_code_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_code_417_);
lean_dec_ref(v_code_417_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object* v_singleton_419_, lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = lean_usize_dec_eq(v_i_421_, v_stop_422_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_424_ = 0;
v___x_425_ = lean_array_uget_borrowed(v_as_420_, v_i_421_);
v___x_426_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_424_, v___x_425_, v_singleton_419_);
if (v___x_426_ == 0)
{
size_t v___x_427_; size_t v___x_428_; 
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_421_, v___x_427_);
v_i_421_ = v___x_428_;
goto _start;
}
else
{
return v___x_426_;
}
}
else
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object* v_singleton_431_, lean_object* v_as_432_, lean_object* v_i_433_, lean_object* v_stop_434_){
_start:
{
size_t v_i_boxed_435_; size_t v_stop_boxed_436_; uint8_t v_res_437_; lean_object* v_r_438_; 
v_i_boxed_435_ = lean_unbox_usize(v_i_433_);
lean_dec(v_i_433_);
v_stop_boxed_436_ = lean_unbox_usize(v_stop_434_);
lean_dec(v_stop_434_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_431_, v_as_432_, v_i_boxed_435_, v_stop_boxed_436_);
lean_dec_ref(v_as_432_);
lean_dec(v_singleton_431_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t v_sz_439_, size_t v_i_440_, lean_object* v_bs_441_, uint8_t v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_bs_441_);
return v___x_450_;
}
else
{
uint8_t v___x_451_; lean_object* v_v_452_; lean_object* v___x_453_; lean_object* v_bs_x27_454_; lean_object* v___x_455_; 
v___x_451_ = 0;
v_v_452_ = lean_array_uget(v_bs_441_, v_i_440_);
v___x_453_ = lean_unsigned_to_nat(0u);
v_bs_x27_454_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_453_);
v___x_455_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_451_, v_v_452_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_add(v_i_440_, v___x_457_);
v___x_459_ = lean_array_uset(v_bs_x27_454_, v_i_440_, v_a_456_);
v_i_440_ = v___x_458_;
v_bs_441_ = v___x_459_;
goto _start;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v_bs_x27_454_);
v_a_461_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_455_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_455_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object* v_sz_469_, lean_object* v_i_470_, lean_object* v_bs_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; uint8_t v___y_5212__boxed_481_; lean_object* v_res_482_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_469_);
lean_dec(v_sz_469_);
v_i_boxed_480_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v___y_5212__boxed_481_ = lean_unbox(v___y_472_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_boxed_479_, v_i_boxed_480_, v_bs_471_, v___y_5212__boxed_481_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object* v_fields_483_, lean_object* v_____r_484_, lean_object* v_paramsNew_485_, uint8_t v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
size_t v_sz_493_; size_t v___x_494_; lean_object* v___x_495_; 
v_sz_493_ = lean_array_size(v_fields_483_);
v___x_494_ = ((size_t)0ULL);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_493_, v___x_494_, v_fields_483_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_505_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_500_ = l_Array_append___redArg(v_paramsNew_485_, v_a_496_);
lean_dec(v_a_496_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_501_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v_paramsNew_485_);
v_a_506_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_495_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_495_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object* v_fields_514_, lean_object* v_____r_515_, lean_object* v_paramsNew_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v___y_5270__boxed_524_; lean_object* v_res_525_; 
v___y_5270__boxed_524_ = lean_unbox(v___y_517_);
v_res_525_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_514_, v_____r_515_, v_paramsNew_516_, v___y_5270__boxed_524_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object* v_upperBound_526_, lean_object* v_params_527_, lean_object* v_targetParamIdx_528_, uint8_t v___y_529_, lean_object* v_fields_530_, lean_object* v_a_531_, lean_object* v_b_532_, uint8_t v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_a_541_; lean_object* v___y_546_; uint8_t v___x_565_; 
v___x_565_ = lean_nat_dec_lt(v_a_531_, v_upperBound_526_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_a_531_);
lean_dec_ref(v_fields_530_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_b_532_);
return v___x_566_;
}
else
{
uint8_t v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = 0;
v___x_568_ = lean_array_fget_borrowed(v_params_527_, v_a_531_);
v___x_569_ = lean_nat_dec_eq(v_targetParamIdx_528_, v_a_531_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_inc(v___x_568_);
v___x_570_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_567_, v___x_568_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = lean_array_push(v_b_532_, v_a_571_);
v_a_541_ = v___x_572_;
goto v___jp_540_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v_b_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_fields_530_);
v_a_573_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_570_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_570_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
if (v___y_529_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_box(0);
lean_inc_ref(v_fields_530_);
v___x_582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_530_, v___x_581_, v_b_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v___y_546_ = v___x_582_;
goto v___jp_545_;
}
else
{
lean_object* v___x_583_; 
lean_inc(v___x_568_);
v___x_583_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_567_, v___x_568_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = lean_array_push(v_b_532_, v_a_584_);
v___x_586_ = lean_box(0);
lean_inc_ref(v_fields_530_);
v___x_587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_530_, v___x_586_, v___x_585_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v___y_546_ = v___x_587_;
goto v___jp_545_;
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_b_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_fields_530_);
v_a_588_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_583_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_583_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_a_531_, v___x_542_);
lean_dec(v_a_531_);
v_a_531_ = v___x_543_;
v_b_532_ = v_a_541_;
goto _start;
}
v___jp_545_:
{
if (lean_obj_tag(v___y_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_556_; 
v_a_547_ = lean_ctor_get(v___y_546_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___y_546_);
if (v_isSharedCheck_556_ == 0)
{
v___x_549_ = v___y_546_;
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___y_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
if (lean_obj_tag(v_a_547_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; 
lean_dec(v_a_531_);
lean_dec_ref(v_fields_530_);
v_a_551_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_a_547_, 1);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_a_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v_a_555_; 
lean_del_object(v___x_549_);
v_a_555_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v_a_547_, 1);
v_a_541_ = v_a_555_;
goto v___jp_540_;
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_a_531_);
lean_dec_ref(v_fields_530_);
v_a_557_ = lean_ctor_get(v___y_546_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___y_546_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___y_546_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___y_546_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object* v_upperBound_596_, lean_object* v_params_597_, lean_object* v_targetParamIdx_598_, lean_object* v___y_599_, lean_object* v_fields_600_, lean_object* v_a_601_, lean_object* v_b_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
uint8_t v___y_5334__boxed_610_; uint8_t v___y_5335__boxed_611_; lean_object* v_res_612_; 
v___y_5334__boxed_610_ = lean_unbox(v___y_599_);
v___y_5335__boxed_611_ = lean_unbox(v___y_603_);
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_596_, v_params_597_, v_targetParamIdx_598_, v___y_5334__boxed_610_, v_fields_600_, v_a_601_, v_b_602_, v___y_5335__boxed_611_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec(v_targetParamIdx_598_);
lean_dec_ref(v_params_597_);
lean_dec(v_upperBound_596_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(size_t v_sz_613_, size_t v_i_614_, lean_object* v_bs_615_, uint8_t v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_bs_615_);
return v___x_624_;
}
else
{
uint8_t v___x_625_; lean_object* v_v_626_; lean_object* v___x_627_; lean_object* v_bs_x27_628_; lean_object* v___x_629_; 
v___x_625_ = 0;
v_v_626_ = lean_array_uget(v_bs_615_, v_i_614_);
v___x_627_ = lean_unsigned_to_nat(0u);
v_bs_x27_628_ = lean_array_uset(v_bs_615_, v_i_614_, v___x_627_);
v___x_629_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_625_, v_v_626_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_614_, v___x_631_);
v___x_633_ = lean_array_uset(v_bs_x27_628_, v_i_614_, v_a_630_);
v_i_614_ = v___x_632_;
v_bs_615_ = v___x_633_;
goto _start;
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_bs_x27_628_);
v_a_635_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_629_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_629_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(lean_object* v_sz_643_, lean_object* v_i_644_, lean_object* v_bs_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
size_t v_sz_boxed_653_; size_t v_i_boxed_654_; uint8_t v___y_5472__boxed_655_; lean_object* v_res_656_; 
v_sz_boxed_653_ = lean_unbox_usize(v_sz_643_);
lean_dec(v_sz_643_);
v_i_boxed_654_ = lean_unbox_usize(v_i_644_);
lean_dec(v_i_644_);
v___y_5472__boxed_655_ = lean_unbox(v___y_646_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_boxed_653_, v_i_boxed_654_, v_bs_645_, v___y_5472__boxed_655_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
return v_res_656_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object* v_decls_663_, lean_object* v_params_664_, lean_object* v_targetParamIdx_665_, lean_object* v_fields_666_, lean_object* v_k_667_, uint8_t v_default_668_, uint8_t v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_fvarId_678_; lean_object* v___x_679_; lean_object* v_paramsNew_680_; uint8_t v___x_681_; uint8_t v___y_683_; lean_object* v_singleton_737_; uint8_t v___x_738_; 
v___x_676_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0);
v___x_677_ = lean_array_get_borrowed(v___x_676_, v_params_664_, v_targetParamIdx_665_);
v_fvarId_678_ = lean_ctor_get(v___x_677_, 0);
v___x_679_ = lean_unsigned_to_nat(0u);
v_paramsNew_680_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
v___x_681_ = 0;
lean_inc(v_fvarId_678_);
v_singleton_737_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_678_);
v___x_738_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_681_, v_k_667_, v_singleton_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_array_get_size(v_decls_663_);
v___x_740_ = lean_nat_dec_lt(v___x_679_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v_singleton_737_);
v___y_683_ = v___x_740_;
goto v___jp_682_;
}
else
{
if (v___x_740_ == 0)
{
lean_dec(v_singleton_737_);
v___y_683_ = v___x_740_;
goto v___jp_682_;
}
else
{
size_t v___x_741_; size_t v___x_742_; uint8_t v___x_743_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_739_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_737_, v_decls_663_, v___x_741_, v___x_742_);
lean_dec(v_singleton_737_);
v___y_683_ = v___x_743_;
goto v___jp_682_;
}
}
}
else
{
lean_dec(v_singleton_737_);
v___y_683_ = v___x_738_;
goto v___jp_682_;
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_array_get_size(v_params_664_);
v___x_685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v___x_684_, v_params_664_, v_targetParamIdx_665_, v___y_683_, v_fields_666_, v___x_679_, v_paramsNew_680_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; size_t v_sz_687_; size_t v___x_688_; lean_object* v___x_689_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v_sz_687_ = lean_array_size(v_decls_663_);
v___x_688_ = ((size_t)0ULL);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_687_, v___x_688_, v_decls_663_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_681_, v_k_667_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_690_, v_a_692_);
lean_dec(v_a_690_);
v___x_694_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3));
v___x_695_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___x_681_, v_a_686_, v___x_693_, v___x_694_, v_a_671_, v_a_672_, v_a_673_, v_a_674_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_700_, 0, v_a_696_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*1, v_default_668_);
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*1 + 1, v___y_683_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
v_a_705_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_695_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_695_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_690_);
lean_dec(v_a_686_);
v_a_713_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_691_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_691_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_a_686_);
lean_dec_ref(v_k_667_);
v_a_721_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_689_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_689_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_k_667_);
lean_dec_ref(v_decls_663_);
v_a_729_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_685_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_685_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object* v_decls_744_, lean_object* v_params_745_, lean_object* v_targetParamIdx_746_, lean_object* v_fields_747_, lean_object* v_k_748_, lean_object* v_default_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
uint8_t v_default_boxed_757_; uint8_t v_a_boxed_758_; lean_object* v_res_759_; 
v_default_boxed_757_ = lean_unbox(v_default_749_);
v_a_boxed_758_ = lean_unbox(v_a_750_);
v_res_759_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_744_, v_params_745_, v_targetParamIdx_746_, v_fields_747_, v_k_748_, v_default_boxed_757_, v_a_boxed_758_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec(v_targetParamIdx_746_);
lean_dec_ref(v_params_745_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object* v_upperBound_760_, lean_object* v_params_761_, lean_object* v_targetParamIdx_762_, uint8_t v___y_763_, lean_object* v_fields_764_, lean_object* v_inst_765_, lean_object* v_R_766_, lean_object* v_a_767_, lean_object* v_b_768_, lean_object* v_c_769_, uint8_t v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_760_, v_params_761_, v_targetParamIdx_762_, v___y_763_, v_fields_764_, v_a_767_, v_b_768_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_778_ = _args[0];
lean_object* v_params_779_ = _args[1];
lean_object* v_targetParamIdx_780_ = _args[2];
lean_object* v___y_781_ = _args[3];
lean_object* v_fields_782_ = _args[4];
lean_object* v_inst_783_ = _args[5];
lean_object* v_R_784_ = _args[6];
lean_object* v_a_785_ = _args[7];
lean_object* v_b_786_ = _args[8];
lean_object* v_c_787_ = _args[9];
lean_object* v___y_788_ = _args[10];
lean_object* v___y_789_ = _args[11];
lean_object* v___y_790_ = _args[12];
lean_object* v___y_791_ = _args[13];
lean_object* v___y_792_ = _args[14];
lean_object* v___y_793_ = _args[15];
lean_object* v___y_794_ = _args[16];
_start:
{
uint8_t v___y_5676__boxed_795_; uint8_t v___y_5678__boxed_796_; lean_object* v_res_797_; 
v___y_5676__boxed_795_ = lean_unbox(v___y_781_);
v___y_5678__boxed_796_ = lean_unbox(v___y_788_);
v_res_797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(v_upperBound_778_, v_params_779_, v_targetParamIdx_780_, v___y_5676__boxed_795_, v_fields_782_, v_inst_783_, v_R_784_, v_a_785_, v_b_786_, v_c_787_, v___y_5678__boxed_796_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec(v_targetParamIdx_780_);
lean_dec_ref(v_params_779_);
lean_dec(v_upperBound_778_);
return v_res_797_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_box(0);
v___x_799_ = lean_unsigned_to_nat(16u);
v___x_800_ = lean_mk_array(v___x_799_, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object* v_decls_804_, lean_object* v_params_805_, lean_object* v_targetParamIdx_806_, lean_object* v_fields_807_, lean_object* v_k_808_, uint8_t v_default_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_815_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1);
v___x_816_ = 0;
v___x_817_ = lean_st_mk_ref(v___x_815_);
v___x_818_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_804_, v_params_805_, v_targetParamIdx_806_, v_fields_807_, v_k_808_, v_default_809_, v___x_816_, v___x_817_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_st_ref_get(v___x_817_);
lean_dec(v___x_817_);
lean_dec(v___x_823_);
if (v_isShared_822_ == 0)
{
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_819_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_dec(v___x_817_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object* v_decls_828_, lean_object* v_params_829_, lean_object* v_targetParamIdx_830_, lean_object* v_fields_831_, lean_object* v_k_832_, lean_object* v_default_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
uint8_t v_default_boxed_839_; lean_object* v_res_840_; 
v_default_boxed_839_ = lean_unbox(v_default_833_);
v_res_840_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_decls_828_, v_params_829_, v_targetParamIdx_830_, v_fields_831_, v_k_832_, v_default_boxed_839_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_targetParamIdx_830_);
lean_dec_ref(v_params_829_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object* v_args_841_, lean_object* v_targetParamIdx_842_, lean_object* v_fields_843_, uint8_t v_dependsOnTarget_844_){
_start:
{
if (v_dependsOnTarget_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_lower_850_; lean_object* v_upper_851_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_845_ = lean_unsigned_to_nat(0u);
lean_inc(v_targetParamIdx_842_);
lean_inc_ref(v_args_841_);
v___x_846_ = l_Array_toSubarray___redArg(v_args_841_, v___x_845_, v_targetParamIdx_842_);
v___x_847_ = l_Subarray_copy___redArg(v___x_846_);
v___x_848_ = l_Array_append___redArg(v___x_847_, v_fields_843_);
v___x_855_ = lean_array_get_size(v_args_841_);
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_nat_add(v_targetParamIdx_842_, v___x_856_);
lean_dec(v_targetParamIdx_842_);
v___x_858_ = lean_nat_dec_le(v___x_857_, v___x_845_);
if (v___x_858_ == 0)
{
v_lower_850_ = v___x_857_;
v_upper_851_ = v___x_855_;
goto v___jp_849_;
}
else
{
lean_dec(v___x_857_);
v_lower_850_ = v___x_845_;
v_upper_851_ = v___x_855_;
goto v___jp_849_;
}
v___jp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = l_Array_toSubarray___redArg(v_args_841_, v_lower_850_, v_upper_851_);
v___x_853_ = l_Subarray_copy___redArg(v___x_852_);
v___x_854_ = l_Array_append___redArg(v___x_848_, v___x_853_);
lean_dec_ref(v___x_853_);
return v___x_854_;
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_lower_866_; lean_object* v_upper_867_; lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_add(v_targetParamIdx_842_, v___x_860_);
lean_dec(v_targetParamIdx_842_);
lean_inc(v___x_861_);
lean_inc_ref(v_args_841_);
v___x_862_ = l_Array_toSubarray___redArg(v_args_841_, v___x_859_, v___x_861_);
v___x_863_ = l_Subarray_copy___redArg(v___x_862_);
v___x_864_ = l_Array_append___redArg(v___x_863_, v_fields_843_);
v___x_871_ = lean_array_get_size(v_args_841_);
v___x_872_ = lean_nat_dec_le(v___x_861_, v___x_859_);
if (v___x_872_ == 0)
{
v_lower_866_ = v___x_861_;
v_upper_867_ = v___x_871_;
goto v___jp_865_;
}
else
{
lean_dec(v___x_861_);
v_lower_866_ = v___x_859_;
v_upper_867_ = v___x_871_;
goto v___jp_865_;
}
v___jp_865_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = l_Array_toSubarray___redArg(v_args_841_, v_lower_866_, v_upper_867_);
v___x_869_ = l_Subarray_copy___redArg(v___x_868_);
v___x_870_ = l_Array_append___redArg(v___x_864_, v___x_869_);
lean_dec_ref(v___x_869_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object* v_args_873_, lean_object* v_targetParamIdx_874_, lean_object* v_fields_875_, lean_object* v_dependsOnTarget_876_){
_start:
{
uint8_t v_dependsOnTarget_boxed_877_; lean_object* v_res_878_; 
v_dependsOnTarget_boxed_877_ = lean_unbox(v_dependsOnTarget_876_);
v_res_878_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_873_, v_targetParamIdx_874_, v_fields_875_, v_dependsOnTarget_boxed_877_);
lean_dec_ref(v_fields_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t v_sz_879_, size_t v_i_880_, lean_object* v_bs_881_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_lt(v_i_880_, v_sz_879_);
if (v___x_882_ == 0)
{
return v_bs_881_;
}
else
{
lean_object* v_v_883_; lean_object* v_fvarId_884_; lean_object* v___x_885_; lean_object* v_bs_x27_886_; lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; 
v_v_883_ = lean_array_uget_borrowed(v_bs_881_, v_i_880_);
v_fvarId_884_ = lean_ctor_get(v_v_883_, 0);
lean_inc(v_fvarId_884_);
v___x_885_ = lean_unsigned_to_nat(0u);
v_bs_x27_886_ = lean_array_uset(v_bs_881_, v_i_880_, v___x_885_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_fvarId_884_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_add(v_i_880_, v___x_888_);
v___x_890_ = lean_array_uset(v_bs_x27_886_, v_i_880_, v___x_887_);
v_i_880_ = v___x_889_;
v_bs_881_ = v___x_890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_bs_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_896_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_boxed_895_, v_i_boxed_896_, v_bs_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t v_sz_898_, size_t v_i_899_, lean_object* v_bs_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_lt(v_i_899_, v_sz_898_);
if (v___x_901_ == 0)
{
return v_bs_900_;
}
else
{
lean_object* v_v_902_; lean_object* v_fvarId_903_; lean_object* v___x_904_; lean_object* v_bs_x27_905_; lean_object* v___x_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_v_902_ = lean_array_uget_borrowed(v_bs_900_, v_i_899_);
v_fvarId_903_ = lean_ctor_get(v_v_902_, 0);
lean_inc(v_fvarId_903_);
v___x_904_ = lean_unsigned_to_nat(0u);
v_bs_x27_905_ = lean_array_uset(v_bs_900_, v_i_899_, v___x_904_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_fvarId_903_);
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_add(v_i_899_, v___x_907_);
v___x_909_ = lean_array_uset(v_bs_x27_905_, v_i_899_, v___x_906_);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_898_, v___x_908_, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(lean_object* v_sz_911_, lean_object* v_i_912_, lean_object* v_bs_913_){
_start:
{
size_t v_sz_boxed_914_; size_t v_i_boxed_915_; lean_object* v_res_916_; 
v_sz_boxed_914_ = lean_unbox_usize(v_sz_911_);
lean_dec(v_sz_911_);
v_i_boxed_915_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_boxed_914_, v_i_boxed_915_, v_bs_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object* v_params_917_, lean_object* v_targetParamIdx_918_, lean_object* v_fields_919_, uint8_t v_dependsOnTarget_920_){
_start:
{
size_t v_sz_921_; size_t v___x_922_; lean_object* v___x_923_; size_t v_sz_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_sz_921_ = lean_array_size(v_params_917_);
v___x_922_ = ((size_t)0ULL);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_921_, v___x_922_, v_params_917_);
v_sz_924_ = lean_array_size(v_fields_919_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_924_, v___x_922_, v_fields_919_);
v___x_926_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v___x_923_, v_targetParamIdx_918_, v___x_925_, v_dependsOnTarget_920_);
lean_dec_ref(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object* v_params_927_, lean_object* v_targetParamIdx_928_, lean_object* v_fields_929_, lean_object* v_dependsOnTarget_930_){
_start:
{
uint8_t v_dependsOnTarget_boxed_931_; lean_object* v_res_932_; 
v_dependsOnTarget_boxed_931_ = lean_unbox(v_dependsOnTarget_930_);
v_res_932_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_927_, v_targetParamIdx_928_, v_fields_929_, v_dependsOnTarget_boxed_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object* v_fvarId_938_, lean_object* v_args_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_st_ref_get(v_a_941_);
v___x_949_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_948_, v_fvarId_938_);
lean_dec(v___x_948_);
if (lean_obj_tag(v___x_949_) == 1)
{
lean_object* v_val_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1132_; 
v_val_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_1132_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_val_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1132_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_940_, v_fvarId_938_);
if (lean_obj_tag(v___x_954_) == 1)
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1127_; 
lean_del_object(v___x_952_);
v_val_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_1127_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1127_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_paramIdx_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1125_; 
v_paramIdx_959_ = lean_ctor_get(v_val_955_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_val_955_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_val_955_, 1);
lean_dec(v_unused_1126_);
v___x_961_ = v_val_955_;
v_isShared_962_ = v_isSharedCheck_1125_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_paramIdx_959_);
lean_dec(v_val_955_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1125_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_box(0);
v___x_964_ = lean_array_get(v___x_963_, v_args_939_, v_paramIdx_959_);
if (lean_obj_tag(v___x_964_) == 1)
{
lean_object* v_fvarId_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1120_; 
lean_del_object(v___x_957_);
v_fvarId_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_1120_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_fvarId_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1120_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint8_t v___x_969_; lean_object* v___x_970_; 
v___x_969_ = 0;
v___x_970_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_965_, v_a_942_, v_a_944_, v_a_946_);
lean_dec(v_fvarId_965_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1111_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_1111_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1111_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
if (lean_obj_tag(v_a_971_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1106_; 
v_val_975_ = lean_ctor_get(v_a_971_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_a_971_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_977_ = v_a_971_;
v_isShared_978_ = v_isSharedCheck_1106_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v_a_971_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1106_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_975_);
v___x_980_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_950_, v___x_979_);
lean_dec(v___x_979_);
lean_dec(v_val_950_);
if (lean_obj_tag(v___x_980_) == 1)
{
lean_object* v_val_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1101_; 
v_val_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1101_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_val_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1101_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v_default_985_; 
v_default_985_ = lean_ctor_get_uint8(v_val_981_, sizeof(void*)*1);
if (v_default_985_ == 0)
{
if (lean_obj_tag(v_val_975_) == 0)
{
lean_object* v_decl_986_; uint8_t v_dependsOnDiscr_987_; lean_object* v_val_988_; lean_object* v_args_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1024_; 
lean_del_object(v___x_977_);
lean_del_object(v___x_967_);
lean_del_object(v___x_961_);
v_decl_986_ = lean_ctor_get(v_val_981_, 0);
lean_inc_ref(v_decl_986_);
v_dependsOnDiscr_987_ = lean_ctor_get_uint8(v_val_981_, sizeof(void*)*1 + 1);
lean_dec(v_val_981_);
v_val_988_ = lean_ctor_get(v_val_975_, 0);
v_args_989_ = lean_ctor_get(v_val_975_, 1);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_val_975_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_991_ = v_val_975_;
v_isShared_992_ = v_isSharedCheck_1024_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_args_989_);
lean_inc(v_val_988_);
lean_dec(v_val_975_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1024_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___y_994_; lean_object* v_numParams_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_numParams_1014_ = lean_ctor_get(v_val_988_, 3);
lean_inc(v_numParams_1014_);
lean_dec_ref(v_val_988_);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_array_get_size(v_args_989_);
v___x_1017_ = lean_nat_dec_le(v_numParams_1014_, v___x_1015_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1019_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_1016_);
lean_ctor_set(v___x_991_, 0, v_numParams_1014_);
v___x_1019_ = v___x_991_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_numParams_1014_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___x_1016_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
v___y_994_ = v___x_1019_;
goto v___jp_993_;
}
}
else
{
lean_object* v___x_1022_; 
lean_dec(v_numParams_1014_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_1016_);
lean_ctor_set(v___x_991_, 0, v___x_1015_);
v___x_1022_ = v___x_991_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1016_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
v___y_994_ = v___x_1022_;
goto v___jp_993_;
}
}
v___jp_993_:
{
lean_object* v_fvarId_995_; lean_object* v_lower_996_; lean_object* v_upper_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1013_; 
v_fvarId_995_ = lean_ctor_get(v_decl_986_, 0);
lean_inc(v_fvarId_995_);
lean_dec_ref(v_decl_986_);
v_lower_996_ = lean_ctor_get(v___y_994_, 0);
v_upper_997_ = lean_ctor_get(v___y_994_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___y_994_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_999_ = v___y_994_;
v_isShared_1000_ = v_isSharedCheck_1013_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_upper_997_);
lean_inc(v_lower_996_);
lean_dec(v___y_994_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1013_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1001_ = l_Array_toSubarray___redArg(v_args_989_, v_lower_996_, v_upper_997_);
v___x_1002_ = l_Subarray_copy___redArg(v___x_1001_);
v___x_1003_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_939_, v_paramIdx_959_, v___x_1002_, v_dependsOnDiscr_987_);
lean_dec_ref(v___x_1002_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 3);
lean_ctor_set(v___x_999_, 1, v___x_1003_);
lean_ctor_set(v___x_999_, 0, v_fvarId_995_);
v___x_1005_ = v___x_999_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_fvarId_995_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1005_);
v___x_1007_ = v___x_983_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_1007_);
v___x_1009_ = v___x_973_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
}
else
{
lean_object* v_decl_1025_; uint8_t v_dependsOnDiscr_1026_; lean_object* v_n_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1086_; 
v_decl_1025_ = lean_ctor_get(v_val_981_, 0);
lean_inc_ref(v_decl_1025_);
v_dependsOnDiscr_1026_ = lean_ctor_get_uint8(v_val_981_, sizeof(void*)*1 + 1);
lean_dec(v_val_981_);
v_n_1027_ = lean_ctor_get(v_val_975_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_val_975_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1029_ = v_val_975_;
v_isShared_1030_ = v_isSharedCheck_1086_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_n_1027_);
lean_dec(v_val_975_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1086_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_zero_1031_; uint8_t v_isZero_1032_; 
v_zero_1031_ = lean_unsigned_to_nat(0u);
v_isZero_1032_ = lean_nat_dec_eq(v_n_1027_, v_zero_1031_);
if (v_isZero_1032_ == 1)
{
lean_object* v_fvarId_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_del_object(v___x_1029_);
lean_dec(v_n_1027_);
lean_del_object(v___x_977_);
lean_del_object(v___x_967_);
v_fvarId_1033_ = lean_ctor_get(v_decl_1025_, 0);
lean_inc(v_fvarId_1033_);
lean_dec_ref(v_decl_1025_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1035_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_939_, v_paramIdx_959_, v___x_1034_, v_dependsOnDiscr_1026_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 3);
lean_ctor_set(v___x_961_, 1, v___x_1035_);
lean_ctor_set(v___x_961_, 0, v_fvarId_1033_);
v___x_1037_ = v___x_961_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_fvarId_1033_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1037_);
v___x_1039_ = v___x_983_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_1039_);
v___x_1041_ = v___x_973_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_one_1045_; lean_object* v_n_1046_; lean_object* v___x_1048_; 
lean_del_object(v___x_973_);
v_one_1045_ = lean_unsigned_to_nat(1u);
v_n_1046_ = lean_nat_sub(v_n_1027_, v_one_1045_);
lean_dec(v_n_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 0);
lean_ctor_set(v___x_1029_, 0, v_n_1046_);
v___x_1048_ = v___x_1029_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_n_1046_);
v___x_1048_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 0);
lean_ctor_set(v___x_977_, 0, v___x_1048_);
v___x_1050_ = v___x_977_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
v___x_1052_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_969_, v___x_1050_, v___x_1051_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1075_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1075_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_fvarId_1057_; lean_object* v_fvarId_1058_; lean_object* v___x_1060_; 
v_fvarId_1057_ = lean_ctor_get(v_decl_1025_, 0);
lean_inc(v_fvarId_1057_);
lean_dec_ref(v_decl_1025_);
v_fvarId_1058_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_fvarId_1058_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_fvarId_1058_);
v___x_1060_ = v___x_967_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_fvarId_1058_);
v___x_1060_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1061_ = lean_mk_empty_array_with_capacity(v_one_1045_);
v___x_1062_ = lean_array_push(v___x_1061_, v___x_1060_);
v___x_1063_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_939_, v_paramIdx_959_, v___x_1062_, v_dependsOnDiscr_1026_);
lean_dec_ref(v___x_1062_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 3);
lean_ctor_set(v___x_961_, 1, v___x_1063_);
lean_ctor_set(v___x_961_, 0, v_fvarId_1057_);
v___x_1065_ = v___x_961_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_fvarId_1057_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1053_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1066_);
v___x_1068_ = v___x_983_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1068_);
v___x_1070_ = v___x_1055_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
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
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_decl_1025_);
lean_del_object(v___x_983_);
lean_del_object(v___x_967_);
lean_del_object(v___x_961_);
lean_dec(v_paramIdx_959_);
lean_dec_ref(v_args_939_);
v_a_1076_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1052_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1052_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
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
}
}
}
else
{
lean_object* v_decl_1087_; uint8_t v_dependsOnDiscr_1088_; lean_object* v_fvarId_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
lean_del_object(v___x_977_);
lean_dec(v_val_975_);
lean_del_object(v___x_967_);
v_decl_1087_ = lean_ctor_get(v_val_981_, 0);
lean_inc_ref(v_decl_1087_);
v_dependsOnDiscr_1088_ = lean_ctor_get_uint8(v_val_981_, sizeof(void*)*1 + 1);
lean_dec(v_val_981_);
v_fvarId_1089_ = lean_ctor_get(v_decl_1087_, 0);
lean_inc(v_fvarId_1089_);
lean_dec_ref(v_decl_1087_);
v___x_1090_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1091_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_939_, v_paramIdx_959_, v___x_1090_, v_dependsOnDiscr_1088_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 3);
lean_ctor_set(v___x_961_, 1, v___x_1091_);
lean_ctor_set(v___x_961_, 0, v_fvarId_1089_);
v___x_1093_ = v___x_961_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_fvarId_1089_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_1093_);
v___x_1095_ = v___x_983_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_1095_);
v___x_1097_ = v___x_973_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec(v___x_980_);
lean_del_object(v___x_977_);
lean_dec(v_val_975_);
lean_del_object(v___x_967_);
lean_del_object(v___x_961_);
lean_dec(v_paramIdx_959_);
lean_dec_ref(v_args_939_);
v___x_1102_ = lean_box(0);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_1102_);
v___x_1104_ = v___x_973_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_dec(v_a_971_);
lean_del_object(v___x_967_);
lean_del_object(v___x_961_);
lean_dec(v_paramIdx_959_);
lean_dec(v_val_950_);
lean_dec_ref(v_args_939_);
v___x_1107_ = lean_box(0);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_1107_);
v___x_1109_ = v___x_973_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_del_object(v___x_967_);
lean_del_object(v___x_961_);
lean_dec(v_paramIdx_959_);
lean_dec(v_val_950_);
lean_dec_ref(v_args_939_);
v_a_1112_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_970_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_970_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_dec(v___x_964_);
lean_del_object(v___x_961_);
lean_dec(v_paramIdx_959_);
lean_dec(v_val_950_);
lean_dec_ref(v_args_939_);
v___x_1121_ = lean_box(0);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 0);
lean_ctor_set(v___x_957_, 0, v___x_1121_);
v___x_1123_ = v___x_957_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_dec(v___x_954_);
lean_dec(v_val_950_);
lean_dec_ref(v_args_939_);
v___x_1128_ = lean_box(0);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 0);
lean_ctor_set(v___x_952_, 0, v___x_1128_);
v___x_1130_ = v___x_952_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v___x_949_);
lean_dec_ref(v_args_939_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object* v_fvarId_1135_, lean_object* v_args_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1135_, v_args_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec(v_fvarId_1135_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object* v___x_1146_, lean_object* v_init_1147_, lean_object* v_x_1148_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v_k_1149_; lean_object* v_l_1150_; lean_object* v_r_1151_; lean_object* v___x_1152_; 
v_k_1149_ = lean_ctor_get(v_x_1148_, 1);
v_l_1150_ = lean_ctor_get(v_x_1148_, 3);
v_r_1151_ = lean_ctor_get(v_x_1148_, 4);
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1146_, v_init_1147_, v_l_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
return v___x_1152_;
}
else
{
uint8_t v___x_1153_; 
lean_dec_ref_known(v___x_1152_, 1);
v___x_1153_ = l_Lean_NameSet_contains(v___x_1146_, v_k_1149_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2));
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v_init_1147_ = v___x_1155_;
v_x_1148_ = v_r_1151_;
goto _start;
}
}
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_init_1147_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object* v___x_1158_, lean_object* v_init_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1158_, v_init_1159_, v_x_1160_);
lean_dec(v_x_1160_);
lean_dec(v___x_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object* v___x_1162_, lean_object* v_a_1163_, lean_object* v_init_1164_, lean_object* v_x_1165_){
_start:
{
if (lean_obj_tag(v_x_1165_) == 0)
{
lean_object* v_k_1167_; lean_object* v_l_1168_; lean_object* v_r_1169_; lean_object* v___x_1170_; lean_object* v_a_1171_; lean_object* v_a_1172_; uint8_t v___x_1173_; 
v_k_1167_ = lean_ctor_get(v_x_1165_, 1);
lean_inc(v_k_1167_);
v_l_1168_ = lean_ctor_get(v_x_1165_, 3);
lean_inc(v_l_1168_);
v_r_1169_ = lean_ctor_get(v_x_1165_, 4);
lean_inc(v_r_1169_);
lean_dec_ref_known(v_x_1165_, 5);
lean_inc_ref(v_a_1163_);
v___x_1170_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1162_, v_a_1163_, v_init_1164_, v_l_1168_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref(v___x_1170_);
v_a_1172_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_a_1172_);
lean_dec(v_a_1171_);
v___x_1173_ = l_Lean_NameSet_contains(v___x_1162_, v_k_1167_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_inc_ref(v_a_1163_);
v___x_1174_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1167_, v_a_1163_, v_a_1172_);
v_init_1164_ = v___x_1174_;
v_x_1165_ = v_r_1169_;
goto _start;
}
else
{
lean_dec(v_k_1167_);
v_init_1164_ = v_a_1172_;
v_x_1165_ = v_r_1169_;
goto _start;
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_a_1163_);
v___x_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_init_1164_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object* v___x_1179_, lean_object* v_a_1180_, lean_object* v_init_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1179_, v_a_1180_, v_init_1181_, v_x_1182_);
lean_dec(v___x_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object* v_discr_1190_, lean_object* v___x_1191_, lean_object* v_val_1192_, lean_object* v_fst_1193_, lean_object* v_params_1194_, lean_object* v_snd_1195_, lean_object* v_as_1196_, size_t v_sz_1197_, size_t v_i_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_a_1209_; uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_lt(v_i_1198_, v_sz_1197_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_b_1199_);
return v___x_1214_;
}
else
{
lean_object* v_snd_1215_; lean_object* v_fst_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1374_; 
v_snd_1215_ = lean_ctor_get(v_b_1199_, 1);
v_fst_1216_ = lean_ctor_get(v_b_1199_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_b_1199_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1218_ = v_b_1199_;
v_isShared_1219_ = v_isSharedCheck_1374_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snd_1215_);
lean_inc(v_fst_1216_);
lean_dec(v_b_1199_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1374_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v_fst_1220_; lean_object* v_snd_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1373_; 
v_fst_1220_ = lean_ctor_get(v_snd_1215_, 0);
v_snd_1221_ = lean_ctor_get(v_snd_1215_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_snd_1215_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1223_ = v_snd_1215_;
v_isShared_1224_ = v_isSharedCheck_1373_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_snd_1221_);
lean_inc(v_fst_1220_);
lean_dec(v_snd_1215_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1373_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
uint8_t v___x_1225_; lean_object* v_a_1226_; lean_object* v___y_1228_; lean_object* v___y_1229_; uint8_t v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v_a_1233_; 
v___x_1225_ = 0;
v_a_1226_ = lean_array_uget_borrowed(v_as_1196_, v_i_1198_);
if (lean_obj_tag(v_a_1226_) == 0)
{
lean_object* v_ctorName_1245_; lean_object* v_params_1246_; lean_object* v_code_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
lean_del_object(v___x_1223_);
lean_del_object(v___x_1218_);
v_ctorName_1245_ = lean_ctor_get(v_a_1226_, 0);
v_params_1246_ = lean_ctor_get(v_a_1226_, 1);
v_code_1247_ = lean_ctor_get(v_a_1226_, 2);
v___x_1248_ = 0;
lean_inc_ref(v_params_1246_);
lean_inc(v_ctorName_1245_);
lean_inc(v_discr_1190_);
v___x_1249_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1190_, v_ctorName_1245_, v_params_1246_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
lean_inc_ref(v_code_1247_);
v___x_1251_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1247_, v___y_1200_, v___y_1201_, v_a_1250_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v_a_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; uint8_t v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = l_Lean_NameSet_contains(v___x_1191_, v_ctorName_1245_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc_ref(v_a_1226_);
v___x_1254_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1226_, v_a_1252_);
v___x_1255_ = lean_array_push(v_snd_1221_, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_fst_1220_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_fst_1216_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v_a_1209_ = v___x_1257_;
goto v___jp_1208_;
}
else
{
lean_object* v_paramIdx_1258_; lean_object* v___x_1259_; 
v_paramIdx_1258_ = lean_ctor_get(v_val_1192_, 0);
lean_inc(v_a_1252_);
lean_inc_ref(v_params_1246_);
lean_inc_ref(v_fst_1193_);
v___x_1259_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1193_, v_params_1194_, v_paramIdx_1258_, v_params_1246_, v_a_1252_, v___x_1248_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v_decl_1261_; uint8_t v_dependsOnDiscr_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v_decl_1261_ = lean_ctor_get(v_a_1260_, 0);
lean_inc_ref_n(v_decl_1261_, 2);
v_dependsOnDiscr_1262_ = lean_ctor_get_uint8(v_a_1260_, sizeof(void*)*1 + 1);
v___x_1263_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_decl_1261_);
v___x_1264_ = lean_array_push(v_fst_1220_, v___x_1263_);
lean_inc(v_ctorName_1245_);
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_ctorName_1245_, v_a_1260_, v_fst_1216_);
lean_inc_ref(v_params_1246_);
lean_inc(v_paramIdx_1258_);
lean_inc_ref(v_params_1194_);
v___x_1266_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1194_, v_paramIdx_1258_, v_params_1246_, v_dependsOnDiscr_1262_);
v___x_1267_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1225_, v_a_1252_, v___y_1204_);
lean_dec(v_a_1252_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_fvarId_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref_known(v___x_1267_, 1);
v_fvarId_1268_ = lean_ctor_get(v_decl_1261_, 0);
lean_inc(v_fvarId_1268_);
lean_dec_ref(v_decl_1261_);
v___x_1269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_fvarId_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1266_);
lean_inc_ref(v_a_1226_);
v___x_1270_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1226_, v___x_1269_);
v___x_1271_ = lean_array_push(v_snd_1221_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1264_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1265_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v_a_1209_ = v___x_1273_;
goto v___jp_1208_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___x_1266_);
lean_dec(v___x_1265_);
lean_dec_ref(v___x_1264_);
lean_dec_ref(v_decl_1261_);
lean_dec(v_snd_1221_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1274_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1267_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1267_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_a_1252_);
lean_dec(v_snd_1221_);
lean_dec(v_fst_1220_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1282_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1259_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1259_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_snd_1221_);
lean_dec(v_fst_1220_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1290_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1251_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1251_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_snd_1221_);
lean_dec(v_fst_1220_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1298_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1249_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1249_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_code_1306_; lean_object* v___x_1307_; 
v_code_1306_ = lean_ctor_get(v_a_1226_, 0);
lean_inc_ref(v_code_1306_);
v___x_1307_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1306_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1314_; lean_object* v___y_1316_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_a_1364_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1314_ = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(v_snd_1195_);
v___x_1362_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1314_, v___x_1362_, v___x_1191_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___y_1316_ = v_a_1364_;
goto v___jp_1315_;
v___jp_1309_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_inc_ref(v_a_1226_);
v___x_1310_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1226_, v_a_1308_);
v___x_1311_ = lean_array_push(v_snd_1221_, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v_fst_1220_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_fst_1216_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v_a_1209_ = v___x_1313_;
goto v___jp_1208_;
}
v___jp_1315_:
{
lean_object* v_fst_1317_; 
v_fst_1317_ = lean_ctor_get(v___y_1316_, 0);
lean_inc(v_fst_1317_);
lean_dec_ref(v___y_1316_);
if (lean_obj_tag(v_fst_1317_) == 0)
{
lean_dec(v___x_1314_);
lean_del_object(v___x_1223_);
lean_del_object(v___x_1218_);
goto v___jp_1309_;
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1361_; 
v_val_1318_ = lean_ctor_get(v_fst_1317_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_fst_1317_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1320_ = v_fst_1317_;
v_isShared_1321_ = v_isSharedCheck_1361_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_val_1318_);
lean_dec(v_fst_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1361_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_unbox(v_val_1318_);
lean_dec(v_val_1318_);
if (v___x_1322_ == 0)
{
lean_del_object(v___x_1320_);
lean_dec(v___x_1314_);
lean_del_object(v___x_1223_);
lean_del_object(v___x_1218_);
goto v___jp_1309_;
}
else
{
lean_object* v_paramIdx_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_paramIdx_1323_ = lean_ctor_get(v_val_1192_, 0);
v___x_1324_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
lean_inc(v_a_1308_);
lean_inc_ref(v_fst_1193_);
v___x_1325_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1193_, v_params_1194_, v_paramIdx_1323_, v___x_1324_, v_a_1308_, v___x_1213_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v_decl_1327_; uint8_t v_dependsOnDiscr_1328_; lean_object* v___x_1330_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v_decl_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc_ref_n(v_decl_1327_, 2);
v_dependsOnDiscr_1328_ = lean_ctor_get_uint8(v_a_1326_, sizeof(void*)*1 + 1);
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 2);
lean_ctor_set(v___x_1320_, 0, v_decl_1327_);
v___x_1330_ = v___x_1320_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_decl_1327_);
v___x_1330_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_array_push(v_fst_1220_, v___x_1330_);
v___x_1332_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1225_, v_a_1308_, v___y_1204_);
lean_dec(v_a_1308_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref_known(v___x_1332_, 1);
lean_inc(v___x_1191_);
v___x_1333_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1314_, v_a_1326_, v_fst_1216_, v___x_1191_);
lean_dec(v___x_1314_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_a_1335_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v_a_1335_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_a_1335_);
lean_dec(v_a_1334_);
lean_inc(v_paramIdx_1323_);
v___y_1228_ = v___x_1324_;
v___y_1229_ = v_paramIdx_1323_;
v___y_1230_ = v_dependsOnDiscr_1328_;
v___y_1231_ = v_decl_1327_;
v___y_1232_ = v___x_1331_;
v_a_1233_ = v_a_1335_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_decl_1327_);
lean_del_object(v___x_1223_);
lean_dec(v_snd_1221_);
lean_del_object(v___x_1218_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1336_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1333_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1333_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v___x_1331_);
lean_dec_ref(v_decl_1327_);
lean_dec(v_a_1326_);
lean_dec(v___x_1314_);
lean_del_object(v___x_1223_);
lean_dec(v_snd_1221_);
lean_del_object(v___x_1218_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1344_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1332_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1332_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_del_object(v___x_1320_);
lean_dec(v___x_1314_);
lean_dec(v_a_1308_);
lean_del_object(v___x_1223_);
lean_dec(v_snd_1221_);
lean_dec(v_fst_1220_);
lean_del_object(v___x_1218_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1353_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1325_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1325_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
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
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_del_object(v___x_1223_);
lean_dec(v_snd_1221_);
lean_dec(v_fst_1220_);
lean_del_object(v___x_1218_);
lean_dec(v_fst_1216_);
lean_dec_ref(v_params_1194_);
lean_dec_ref(v_fst_1193_);
lean_dec_ref(v_val_1192_);
lean_dec(v___x_1191_);
lean_dec(v_discr_1190_);
v_a_1365_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1307_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1307_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
v___jp_1227_:
{
lean_object* v_fvarId_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v_fvarId_1234_ = lean_ctor_get(v___y_1231_, 0);
lean_inc(v_fvarId_1234_);
lean_dec_ref(v___y_1231_);
lean_inc_ref(v_params_1194_);
v___x_1235_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1194_, v___y_1229_, v___y_1228_, v___y_1230_);
v___x_1236_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_fvarId_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_inc(v_a_1226_);
v___x_1237_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1226_, v___x_1236_);
v___x_1238_ = lean_array_push(v_snd_1221_, v___x_1237_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1238_);
lean_ctor_set(v___x_1223_, 0, v___y_1232_);
v___x_1240_ = v___x_1223_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___y_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1242_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___x_1240_);
lean_ctor_set(v___x_1218_, 0, v_a_1233_);
v___x_1242_ = v___x_1218_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1233_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
v_a_1209_ = v___x_1242_;
goto v___jp_1208_;
}
}
}
}
}
}
v___jp_1208_:
{
size_t v___x_1210_; size_t v___x_1211_; 
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_add(v_i_1198_, v___x_1210_);
v_i_1198_ = v___x_1211_;
v_b_1199_ = v_a_1209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object* v_decl_1375_, lean_object* v_k_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_fvarId_1385_; lean_object* v_params_1386_; lean_object* v_type_1387_; lean_object* v_value_1388_; lean_object* v___x_1389_; 
v_fvarId_1385_ = lean_ctor_get(v_decl_1375_, 0);
v_params_1386_ = lean_ctor_get(v_decl_1375_, 2);
lean_inc_ref(v_params_1386_);
v_type_1387_ = lean_ctor_get(v_decl_1375_, 3);
lean_inc_ref(v_type_1387_);
v_value_1388_ = lean_ctor_get(v_decl_1375_, 4);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_1377_, v_fvarId_1385_);
if (lean_obj_tag(v___x_1389_) == 1)
{
lean_object* v_val_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1466_; 
v_val_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1466_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_val_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1466_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_ctorNames_1394_; 
v_ctorNames_1394_ = lean_ctor_get(v_val_1390_, 1);
lean_inc(v_ctorNames_1394_);
if (lean_obj_tag(v_ctorNames_1394_) == 0)
{
lean_object* v___x_1395_; lean_object* v_snd_1396_; lean_object* v_fst_1397_; lean_object* v_typeName_1398_; lean_object* v_resultType_1399_; lean_object* v_discr_1400_; lean_object* v_alts_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; size_t v_sz_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1395_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_value_1388_);
v_snd_1396_ = lean_ctor_get(v___x_1395_, 1);
lean_inc(v_snd_1396_);
v_fst_1397_ = lean_ctor_get(v___x_1395_, 0);
lean_inc_n(v_fst_1397_, 2);
lean_dec_ref(v___x_1395_);
v_typeName_1398_ = lean_ctor_get(v_snd_1396_, 0);
lean_inc(v_typeName_1398_);
v_resultType_1399_ = lean_ctor_get(v_snd_1396_, 1);
lean_inc_ref(v_resultType_1399_);
v_discr_1400_ = lean_ctor_get(v_snd_1396_, 2);
lean_inc_n(v_discr_1400_, 2);
v_alts_1401_ = lean_ctor_get(v_snd_1396_, 3);
lean_inc_ref(v_alts_1401_);
v___x_1402_ = 0;
v___x_1403_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1));
v_sz_1404_ = lean_array_size(v_alts_1401_);
v___x_1405_ = ((size_t)0ULL);
lean_inc_ref(v_params_1386_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1400_, v_ctorNames_1394_, v_val_1390_, v_fst_1397_, v_params_1386_, v_snd_1396_, v_alts_1401_, v_sz_1404_, v___x_1405_, v___x_1403_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
lean_dec_ref(v_alts_1401_);
lean_dec(v_snd_1396_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_snd_1408_; lean_object* v_fst_1409_; lean_object* v_fst_1410_; lean_object* v_snd_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1455_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v_snd_1408_ = lean_ctor_get(v_a_1407_, 1);
lean_inc(v_snd_1408_);
v_fst_1409_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_fst_1409_);
lean_dec(v_a_1407_);
v_fst_1410_ = lean_ctor_get(v_snd_1408_, 0);
v_snd_1411_ = lean_ctor_get(v_snd_1408_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_snd_1408_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1413_ = v_snd_1408_;
v_isShared_1414_ = v_isSharedCheck_1455_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_snd_1411_);
lean_inc(v_fst_1410_);
lean_dec(v_snd_1408_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1455_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1415_ = lean_st_ref_take(v_a_1378_);
lean_inc(v_fvarId_1385_);
v___x_1416_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1385_, v_fst_1409_, v___x_1415_);
v___x_1417_ = lean_st_ref_put(v_a_1378_, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1418_, 0, v_typeName_1398_);
lean_ctor_set(v___x_1418_, 1, v_resultType_1399_);
lean_ctor_set(v___x_1418_, 2, v_discr_1400_);
lean_ctor_set(v___x_1418_, 3, v_snd_1411_);
v___x_1419_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
v___x_1420_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_1397_, v___x_1419_);
lean_dec(v_fst_1397_);
v___x_1421_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1402_, v_decl_1375_, v_type_1387_, v_params_1386_, v___x_1420_, v_a_1381_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1438_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1438_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 2);
lean_ctor_set(v___x_1413_, 1, v_a_1424_);
lean_ctor_set(v___x_1413_, 0, v_a_1422_);
v___x_1429_ = v___x_1413_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1422_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_1410_, v___x_1429_);
lean_dec(v_fst_1410_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1430_);
v___x_1432_ = v___x_1392_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1432_);
v___x_1434_ = v___x_1426_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_a_1422_);
lean_del_object(v___x_1413_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1392_);
v_a_1439_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1423_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1423_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_del_object(v___x_1413_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1392_);
lean_dec_ref(v_k_1376_);
v_a_1447_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1421_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1421_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_discr_1400_);
lean_dec_ref(v_resultType_1399_);
lean_dec(v_typeName_1398_);
lean_dec(v_fst_1397_);
lean_del_object(v___x_1392_);
lean_dec_ref(v_type_1387_);
lean_dec_ref(v_params_1386_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_decl_1375_);
v_a_1456_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1406_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1406_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_del_object(v___x_1392_);
lean_dec(v_val_1390_);
lean_dec_ref(v_type_1387_);
lean_dec_ref(v_params_1386_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_decl_1375_);
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec(v___x_1389_);
lean_dec_ref(v_type_1387_);
lean_dec_ref(v_params_1386_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_decl_1375_);
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object* v_code_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
switch(lean_obj_tag(v_code_1469_))
{
case 0:
{
lean_object* v_decl_1478_; lean_object* v_k_1479_; lean_object* v___x_1480_; 
v_decl_1478_ = lean_ctor_get(v_code_1469_, 0);
v_k_1479_ = lean_ctor_get(v_code_1469_, 1);
lean_inc_ref(v_k_1479_);
v___x_1480_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1479_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1517_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1517_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1517_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
size_t v___x_1485_; size_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1485_ = lean_ptr_addr(v_k_1479_);
v___x_1486_ = lean_ptr_addr(v_a_1481_);
v___x_1487_ = lean_usize_dec_eq(v___x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1497_; 
lean_inc_ref(v_decl_1478_);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_code_1469_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; lean_object* v_unused_1499_; 
v_unused_1498_ = lean_ctor_get(v_code_1469_, 1);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_code_1469_, 0);
lean_dec(v_unused_1499_);
v___x_1489_ = v_code_1469_;
v_isShared_1490_ = v_isSharedCheck_1497_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_code_1469_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1497_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v_a_1481_);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_decl_1478_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_a_1481_);
v___x_1492_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1494_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1492_);
v___x_1494_ = v___x_1483_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
size_t v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = lean_ptr_addr(v_decl_1478_);
v___x_1501_ = lean_usize_dec_eq(v___x_1500_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1511_; 
lean_inc_ref(v_decl_1478_);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_code_1469_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; lean_object* v_unused_1513_; 
v_unused_1512_ = lean_ctor_get(v_code_1469_, 1);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_code_1469_, 0);
lean_dec(v_unused_1513_);
v___x_1503_ = v_code_1469_;
v_isShared_1504_ = v_isSharedCheck_1511_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v_code_1469_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1511_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v_a_1481_);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_decl_1478_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_a_1481_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1506_);
v___x_1508_ = v___x_1483_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v___x_1515_; 
lean_dec(v_a_1481_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_code_1469_);
v___x_1515_ = v___x_1483_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_code_1469_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1469_, 2);
return v___x_1480_;
}
}
case 1:
{
lean_object* v_decl_1518_; lean_object* v_k_1519_; lean_object* v_params_1520_; lean_object* v_type_1521_; lean_object* v_value_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; 
v_decl_1518_ = lean_ctor_get(v_code_1469_, 0);
v_k_1519_ = lean_ctor_get(v_code_1469_, 1);
v_params_1520_ = lean_ctor_get(v_decl_1518_, 2);
v_type_1521_ = lean_ctor_get(v_decl_1518_, 3);
v_value_1522_ = lean_ctor_get(v_decl_1518_, 4);
v___x_1523_ = 0;
lean_inc_ref(v_value_1522_);
v___x_1524_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1522_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
lean_inc_ref(v_params_1520_);
lean_inc_ref(v_type_1521_);
lean_inc_ref(v_decl_1518_);
v___x_1526_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1523_, v_decl_1518_, v_type_1521_, v_params_1520_, v_a_1525_, v_a_1474_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
lean_inc_ref(v_k_1519_);
v___x_1528_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1519_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1566_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1566_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1566_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
size_t v___x_1533_; size_t v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_ptr_addr(v_k_1519_);
v___x_1534_ = lean_ptr_addr(v_a_1529_);
v___x_1535_ = lean_usize_dec_eq(v___x_1533_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v_code_1469_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; lean_object* v_unused_1547_; 
v_unused_1546_ = lean_ctor_get(v_code_1469_, 1);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_code_1469_, 0);
lean_dec(v_unused_1547_);
v___x_1537_ = v_code_1469_;
v_isShared_1538_ = v_isSharedCheck_1545_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v_code_1469_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1545_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v_a_1529_);
lean_ctor_set(v___x_1537_, 0, v_a_1527_);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1527_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_a_1529_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1540_);
v___x_1542_ = v___x_1531_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
size_t v___x_1548_; size_t v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = lean_ptr_addr(v_decl_1518_);
v___x_1549_ = lean_ptr_addr(v_a_1527_);
v___x_1550_ = lean_usize_dec_eq(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1560_; 
v_isSharedCheck_1560_ = !lean_is_exclusive(v_code_1469_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1561_ = lean_ctor_get(v_code_1469_, 1);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_code_1469_, 0);
lean_dec(v_unused_1562_);
v___x_1552_ = v_code_1469_;
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v_code_1469_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v_a_1529_);
lean_ctor_set(v___x_1552_, 0, v_a_1527_);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1527_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1529_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1555_);
v___x_1557_ = v___x_1531_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
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
else
{
lean_object* v___x_1564_; 
lean_dec(v_a_1529_);
lean_dec(v_a_1527_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_code_1469_);
v___x_1564_ = v___x_1531_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_code_1469_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_dec(v_a_1527_);
lean_dec_ref_known(v_code_1469_, 2);
return v___x_1528_;
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref_known(v_code_1469_, 2);
v_a_1567_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1526_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1526_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1469_, 2);
return v___x_1524_;
}
}
case 2:
{
lean_object* v_decl_1575_; lean_object* v_k_1576_; lean_object* v___x_1577_; 
v_decl_1575_ = lean_ctor_get(v_code_1469_, 0);
v_k_1576_ = lean_ctor_get(v_code_1469_, 1);
lean_inc_ref(v_k_1576_);
lean_inc_ref(v_decl_1575_);
v___x_1577_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1575_, v_k_1576_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1641_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1641_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1641_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
if (lean_obj_tag(v_a_1578_) == 1)
{
lean_object* v_val_1582_; lean_object* v___x_1584_; 
lean_dec_ref_known(v_code_1469_, 2);
v_val_1582_ = lean_ctor_get(v_a_1578_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_a_1578_, 1);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_val_1582_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_val_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
else
{
lean_object* v_params_1586_; lean_object* v_type_1587_; lean_object* v_value_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; 
lean_del_object(v___x_1580_);
lean_dec(v_a_1578_);
v_params_1586_ = lean_ctor_get(v_decl_1575_, 2);
v_type_1587_ = lean_ctor_get(v_decl_1575_, 3);
v_value_1588_ = lean_ctor_get(v_decl_1575_, 4);
v___x_1589_ = 0;
lean_inc_ref(v_value_1588_);
v___x_1590_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1588_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
lean_inc_ref(v_params_1586_);
lean_inc_ref(v_type_1587_);
lean_inc_ref(v_decl_1575_);
v___x_1592_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1589_, v_decl_1575_, v_type_1587_, v_params_1586_, v_a_1591_, v_a_1474_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
lean_inc_ref(v_k_1576_);
v___x_1594_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1576_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1632_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1632_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1632_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
size_t v___x_1599_; size_t v___x_1600_; uint8_t v___x_1601_; 
v___x_1599_ = lean_ptr_addr(v_k_1576_);
v___x_1600_ = lean_ptr_addr(v_a_1595_);
v___x_1601_ = lean_usize_dec_eq(v___x_1599_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1611_; 
v_isSharedCheck_1611_ = !lean_is_exclusive(v_code_1469_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; lean_object* v_unused_1613_; 
v_unused_1612_ = lean_ctor_get(v_code_1469_, 1);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_code_1469_, 0);
lean_dec(v_unused_1613_);
v___x_1603_ = v_code_1469_;
v_isShared_1604_ = v_isSharedCheck_1611_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v_code_1469_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1611_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v_a_1595_);
lean_ctor_set(v___x_1603_, 0, v_a_1593_);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1593_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_a_1595_);
v___x_1606_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1606_);
v___x_1608_ = v___x_1597_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
size_t v___x_1614_; size_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1614_ = lean_ptr_addr(v_decl_1575_);
v___x_1615_ = lean_ptr_addr(v_a_1593_);
v___x_1616_ = lean_usize_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1626_; 
v_isSharedCheck_1626_ = !lean_is_exclusive(v_code_1469_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; lean_object* v_unused_1628_; 
v_unused_1627_ = lean_ctor_get(v_code_1469_, 1);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_code_1469_, 0);
lean_dec(v_unused_1628_);
v___x_1618_ = v_code_1469_;
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v_code_1469_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v_a_1595_);
lean_ctor_set(v___x_1618_, 0, v_a_1593_);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1593_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_a_1595_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1621_);
v___x_1623_ = v___x_1597_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v___x_1630_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1593_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_code_1469_);
v___x_1630_ = v___x_1597_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_code_1469_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
else
{
lean_dec(v_a_1593_);
lean_dec_ref_known(v_code_1469_, 2);
return v___x_1594_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref_known(v_code_1469_, 2);
v_a_1633_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1592_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1592_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
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
else
{
lean_dec_ref_known(v_code_1469_, 2);
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref_known(v_code_1469_, 2);
v_a_1642_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1577_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1577_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_1650_; lean_object* v_args_1651_; lean_object* v___x_1652_; 
v_fvarId_1650_ = lean_ctor_get(v_code_1469_, 0);
v_args_1651_ = lean_ctor_get(v_code_1469_, 1);
lean_inc_ref(v_args_1651_);
v___x_1652_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1650_, v_args_1651_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1664_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
if (lean_obj_tag(v_a_1653_) == 1)
{
lean_object* v_val_1657_; lean_object* v___x_1659_; 
lean_dec_ref_known(v_code_1469_, 2);
v_val_1657_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v_a_1653_, 1);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_val_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_val_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
else
{
lean_object* v___x_1662_; 
lean_dec(v_a_1653_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_code_1469_);
v___x_1662_ = v___x_1655_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_code_1469_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref_known(v_code_1469_, 2);
v_a_1665_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1652_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1652_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
case 4:
{
lean_object* v_cases_1673_; lean_object* v_typeName_1674_; lean_object* v_resultType_1675_; lean_object* v_discr_1676_; lean_object* v_alts_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1716_; 
v_cases_1673_ = lean_ctor_get(v_code_1469_, 0);
lean_inc_ref(v_cases_1673_);
v_typeName_1674_ = lean_ctor_get(v_cases_1673_, 0);
v_resultType_1675_ = lean_ctor_get(v_cases_1673_, 1);
v_discr_1676_ = lean_ctor_get(v_cases_1673_, 2);
v_alts_1677_ = lean_ctor_get(v_cases_1673_, 3);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_cases_1673_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1679_ = v_cases_1673_;
v_isShared_1680_ = v_isSharedCheck_1716_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_alts_1677_);
lean_inc(v_discr_1676_);
lean_inc(v_resultType_1675_);
lean_inc(v_typeName_1674_);
lean_dec(v_cases_1673_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1716_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1677_);
lean_inc(v_discr_1676_);
v___x_1682_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1676_, v___x_1681_, v_alts_1677_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1707_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1707_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1707_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
size_t v___x_1687_; size_t v___x_1688_; uint8_t v___x_1689_; 
v___x_1687_ = lean_ptr_addr(v_alts_1677_);
lean_dec_ref(v_alts_1677_);
v___x_1688_ = lean_ptr_addr(v_a_1683_);
v___x_1689_ = lean_usize_dec_eq(v___x_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1702_; 
v_isSharedCheck_1702_ = !lean_is_exclusive(v_code_1469_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v_code_1469_, 0);
lean_dec(v_unused_1703_);
v___x_1691_ = v_code_1469_;
v_isShared_1692_ = v_isSharedCheck_1702_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v_code_1469_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1702_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 3, v_a_1683_);
v___x_1694_ = v___x_1679_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_typeName_1674_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_resultType_1675_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_discr_1676_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_a_1683_);
v___x_1694_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1694_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1698_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1696_);
v___x_1698_ = v___x_1685_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
else
{
lean_object* v___x_1705_; 
lean_dec(v_a_1683_);
lean_del_object(v___x_1679_);
lean_dec(v_discr_1676_);
lean_dec_ref(v_resultType_1675_);
lean_dec(v_typeName_1674_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v_code_1469_);
v___x_1705_ = v___x_1685_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_code_1469_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_del_object(v___x_1679_);
lean_dec_ref(v_alts_1677_);
lean_dec(v_discr_1676_);
lean_dec_ref(v_resultType_1675_);
lean_dec(v_typeName_1674_);
lean_dec_ref_known(v_code_1469_, 1);
v_a_1708_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1682_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1682_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
default: 
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_code_1469_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object* v_discr_1718_, lean_object* v_i_1719_, lean_object* v_as_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1729_ = lean_array_get_size(v_as_1720_);
v___x_1730_ = lean_nat_dec_lt(v_i_1719_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
lean_dec(v_i_1719_);
lean_dec(v_discr_1718_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_as_1720_);
return v___x_1731_;
}
else
{
lean_object* v_a_1732_; lean_object* v_a_1734_; 
v_a_1732_ = lean_array_fget_borrowed(v_as_1720_, v_i_1719_);
if (lean_obj_tag(v_a_1732_) == 0)
{
lean_object* v_ctorName_1745_; lean_object* v_params_1746_; lean_object* v_code_1747_; lean_object* v___x_1748_; 
v_ctorName_1745_ = lean_ctor_get(v_a_1732_, 0);
v_params_1746_ = lean_ctor_get(v_a_1732_, 1);
v_code_1747_ = lean_ctor_get(v_a_1732_, 2);
lean_inc_ref(v_params_1746_);
lean_inc(v_ctorName_1745_);
lean_inc(v_discr_1718_);
v___x_1748_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1718_, v_ctorName_1745_, v_params_1746_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
lean_inc_ref(v_code_1747_);
v___x_1750_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1747_, v___y_1721_, v___y_1722_, v_a_1749_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v_a_1749_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
lean_inc_ref(v_a_1732_);
v___x_1752_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1732_, v_a_1751_);
v_a_1734_ = v___x_1752_;
goto v___jp_1733_;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_as_1720_);
lean_dec(v_i_1719_);
lean_dec(v_discr_1718_);
v_a_1753_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1750_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1750_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v_as_1720_);
lean_dec(v_i_1719_);
lean_dec(v_discr_1718_);
v_a_1761_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1748_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1748_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_code_1769_; lean_object* v___x_1770_; 
v_code_1769_ = lean_ctor_get(v_a_1732_, 0);
lean_inc_ref(v_code_1769_);
v___x_1770_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1769_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
lean_inc_ref(v_a_1732_);
v___x_1772_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1732_, v_a_1771_);
v_a_1734_ = v___x_1772_;
goto v___jp_1733_;
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_as_1720_);
lean_dec(v_i_1719_);
lean_dec(v_discr_1718_);
v_a_1773_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1770_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1770_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
v___jp_1733_:
{
size_t v___x_1735_; size_t v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = lean_ptr_addr(v_a_1732_);
v___x_1736_ = lean_ptr_addr(v_a_1734_);
v___x_1737_ = lean_usize_dec_eq(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1719_, v___x_1738_);
v___x_1740_ = lean_array_fset(v_as_1720_, v_i_1719_, v_a_1734_);
lean_dec(v_i_1719_);
v_i_1719_ = v___x_1739_;
v_as_1720_ = v___x_1740_;
goto _start;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
lean_dec_ref(v_a_1734_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_i_1719_, v___x_1742_);
lean_dec(v_i_1719_);
v_i_1719_ = v___x_1743_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object* v_discr_1781_, lean_object* v_i_1782_, lean_object* v_as_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1781_, v_i_1782_, v_as_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec(v___y_1784_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object* v_decl_1793_, lean_object* v_k_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1793_, v_k_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec(v_a_1795_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object** _args){
lean_object* v_discr_1804_ = _args[0];
lean_object* v___x_1805_ = _args[1];
lean_object* v_val_1806_ = _args[2];
lean_object* v_fst_1807_ = _args[3];
lean_object* v_params_1808_ = _args[4];
lean_object* v_snd_1809_ = _args[5];
lean_object* v_as_1810_ = _args[6];
lean_object* v_sz_1811_ = _args[7];
lean_object* v_i_1812_ = _args[8];
lean_object* v_b_1813_ = _args[9];
lean_object* v___y_1814_ = _args[10];
lean_object* v___y_1815_ = _args[11];
lean_object* v___y_1816_ = _args[12];
lean_object* v___y_1817_ = _args[13];
lean_object* v___y_1818_ = _args[14];
lean_object* v___y_1819_ = _args[15];
lean_object* v___y_1820_ = _args[16];
lean_object* v___y_1821_ = _args[17];
_start:
{
size_t v_sz_boxed_1822_; size_t v_i_boxed_1823_; lean_object* v_res_1824_; 
v_sz_boxed_1822_ = lean_unbox_usize(v_sz_1811_);
lean_dec(v_sz_1811_);
v_i_boxed_1823_ = lean_unbox_usize(v_i_1812_);
lean_dec(v_i_1812_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1804_, v___x_1805_, v_val_1806_, v_fst_1807_, v_params_1808_, v_snd_1809_, v_as_1810_, v_sz_boxed_1822_, v_i_boxed_1823_, v_b_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v_as_1810_);
lean_dec_ref(v_snd_1809_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object* v_code_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec(v_a_1826_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object* v___x_1835_, lean_object* v_a_1836_, lean_object* v_init_1837_, lean_object* v_x_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1835_, v_a_1836_, v_init_1837_, v_x_1838_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object* v___x_1848_, lean_object* v_a_1849_, lean_object* v_init_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(v___x_1848_, v_a_1849_, v_init_1850_, v_x_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec(v___x_1848_);
return v_res_1860_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1864_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
lean_ctor_set(v___x_1866_, 2, v___x_1865_);
lean_ctor_set(v___x_1866_, 3, v___x_1865_);
lean_ctor_set(v___x_1866_, 4, v___x_1864_);
lean_ctor_set(v___x_1866_, 5, v___x_1864_);
lean_ctor_set(v___x_1866_, 6, v___x_1864_);
lean_ctor_set(v___x_1866_, 7, v___x_1864_);
lean_ctor_set(v___x_1866_, 8, v___x_1864_);
lean_ctor_set(v___x_1866_, 9, v___x_1864_);
lean_ctor_set(v___x_1866_, 10, v___x_1864_);
lean_ctor_set(v___x_1866_, 11, v___x_1863_);
return v___x_1866_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1867_; double v___x_1868_; 
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_float_of_nat(v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object* v_cls_1872_, lean_object* v_msg_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_ref_1879_; lean_object* v___x_1880_; lean_object* v_env_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_ref_1879_ = lean_ctor_get(v___y_1876_, 2);
v___x_1880_ = lean_st_ref_get(v___y_1877_);
v_env_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc_ref(v_env_1881_);
lean_dec(v___x_1880_);
v___x_1882_ = lean_st_ref_get(v___y_1875_);
v___x_1883_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1874_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1943_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1943_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1943_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_lctx_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1941_; 
v_lctx_1888_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1882_, 1);
lean_dec(v_unused_1942_);
v___x_1890_ = v___x_1882_;
v_isShared_1891_ = v_isSharedCheck_1941_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_lctx_1888_);
lean_dec(v___x_1882_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1941_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
uint8_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1892_ = lean_unbox(v_a_1884_);
lean_dec(v_a_1884_);
v___x_1893_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1888_, v___x_1892_);
lean_dec_ref(v_lctx_1888_);
v___x_1894_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1876_);
v___x_1895_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1);
v___x_1896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1896_, 0, v_env_1881_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
lean_ctor_set(v___x_1896_, 2, v___x_1893_);
lean_ctor_set(v___x_1896_, 3, v___x_1894_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 3);
lean_ctor_set(v___x_1890_, 1, v_msg_1873_);
lean_ctor_set(v___x_1890_, 0, v___x_1896_);
v___x_1898_ = v___x_1890_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_msg_1873_);
v___x_1898_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v_traceState_1900_; lean_object* v_env_1901_; lean_object* v_nextMacroScope_1902_; lean_object* v_ngen_1903_; lean_object* v_auxDeclNGen_1904_; lean_object* v_cache_1905_; lean_object* v_recordedDeps_1906_; lean_object* v_messages_1907_; lean_object* v_infoState_1908_; lean_object* v_snapshotTasks_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1939_; 
v___x_1899_ = lean_st_ref_take(v___y_1877_);
v_traceState_1900_ = lean_ctor_get(v___x_1899_, 4);
v_env_1901_ = lean_ctor_get(v___x_1899_, 0);
v_nextMacroScope_1902_ = lean_ctor_get(v___x_1899_, 1);
v_ngen_1903_ = lean_ctor_get(v___x_1899_, 2);
v_auxDeclNGen_1904_ = lean_ctor_get(v___x_1899_, 3);
v_cache_1905_ = lean_ctor_get(v___x_1899_, 5);
v_recordedDeps_1906_ = lean_ctor_get(v___x_1899_, 6);
v_messages_1907_ = lean_ctor_get(v___x_1899_, 7);
v_infoState_1908_ = lean_ctor_get(v___x_1899_, 8);
v_snapshotTasks_1909_ = lean_ctor_get(v___x_1899_, 9);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1911_ = v___x_1899_;
v_isShared_1912_ = v_isSharedCheck_1939_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_snapshotTasks_1909_);
lean_inc(v_infoState_1908_);
lean_inc(v_messages_1907_);
lean_inc(v_recordedDeps_1906_);
lean_inc(v_cache_1905_);
lean_inc(v_traceState_1900_);
lean_inc(v_auxDeclNGen_1904_);
lean_inc(v_ngen_1903_);
lean_inc(v_nextMacroScope_1902_);
lean_inc(v_env_1901_);
lean_dec(v___x_1899_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1939_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
uint64_t v_tid_1913_; lean_object* v_traces_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1938_; 
v_tid_1913_ = lean_ctor_get_uint64(v_traceState_1900_, sizeof(void*)*1);
v_traces_1914_ = lean_ctor_get(v_traceState_1900_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_traceState_1900_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1916_ = v_traceState_1900_;
v_isShared_1917_ = v_isSharedCheck_1938_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_traces_1914_);
lean_dec(v_traceState_1900_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1938_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; double v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2);
v___x_1921_ = 0;
v___x_1922_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3));
v___x_1923_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1923_, 0, v_cls_1872_);
lean_ctor_set(v___x_1923_, 1, v___x_1919_);
lean_ctor_set(v___x_1923_, 2, v___x_1922_);
lean_ctor_set_float(v___x_1923_, sizeof(void*)*3, v___x_1920_);
lean_ctor_set_float(v___x_1923_, sizeof(void*)*3 + 8, v___x_1920_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*3 + 16, v___x_1921_);
v___x_1924_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4));
v___x_1925_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1898_);
lean_ctor_set(v___x_1925_, 2, v___x_1924_);
lean_inc(v_ref_1879_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_ref_1879_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = l_Lean_PersistentArray_push___redArg(v_traces_1914_, v___x_1926_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1927_);
v___x_1929_ = v___x_1916_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1927_);
lean_ctor_set_uint64(v_reuseFailAlloc_1937_, sizeof(void*)*1, v_tid_1913_);
v___x_1929_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1931_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 4, v___x_1929_);
v___x_1931_ = v___x_1911_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_env_1901_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_nextMacroScope_1902_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_ngen_1903_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_auxDeclNGen_1904_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1936_, 5, v_cache_1905_);
lean_ctor_set(v_reuseFailAlloc_1936_, 6, v_recordedDeps_1906_);
lean_ctor_set(v_reuseFailAlloc_1936_, 7, v_messages_1907_);
lean_ctor_set(v_reuseFailAlloc_1936_, 8, v_infoState_1908_);
lean_ctor_set(v_reuseFailAlloc_1936_, 9, v_snapshotTasks_1909_);
v___x_1931_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_st_ref_put(v___y_1877_, v___x_1931_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1918_);
v___x_1934_ = v___x_1886_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1918_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
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
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v___x_1882_);
lean_dec_ref(v_env_1881_);
lean_dec_ref(v_msg_1873_);
lean_dec(v_cls_1872_);
v_a_1944_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1883_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1883_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object* v_cls_1952_, lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v_cls_1952_, v_msg_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object* v_init_1960_, lean_object* v_x_1961_){
_start:
{
if (lean_obj_tag(v_x_1961_) == 0)
{
lean_object* v_k_1962_; lean_object* v_v_1963_; lean_object* v_l_1964_; lean_object* v_r_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_k_1962_ = lean_ctor_get(v_x_1961_, 1);
v_v_1963_ = lean_ctor_get(v_x_1961_, 2);
v_l_1964_ = lean_ctor_get(v_x_1961_, 3);
v_r_1965_ = lean_ctor_get(v_x_1961_, 4);
v___x_1966_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_1960_, v_r_1965_);
lean_inc(v_v_1963_);
lean_inc(v_k_1962_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_k_1962_);
lean_ctor_set(v___x_1967_, 1, v_v_1963_);
v___x_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___x_1966_);
v_init_1960_ = v___x_1968_;
v_x_1961_ = v_l_1964_;
goto _start;
}
else
{
return v_init_1960_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object* v_init_1970_, lean_object* v_x_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_1970_, v_x_1971_);
lean_dec(v_x_1971_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
if (lean_obj_tag(v_a_1973_) == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = l_List_reverse___redArg(v_a_1974_);
return v___x_1975_;
}
else
{
lean_object* v_head_1976_; lean_object* v_tail_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1986_; 
v_head_1976_ = lean_ctor_get(v_a_1973_, 0);
v_tail_1977_ = lean_ctor_get(v_a_1973_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_a_1973_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1979_ = v_a_1973_;
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_tail_1977_);
lean_inc(v_head_1976_);
lean_dec(v_a_1973_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1986_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = l_Lean_MessageData_ofName(v_head_1976_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v_a_1974_);
lean_ctor_set(v___x_1979_, 0, v___x_1981_);
v___x_1983_ = v___x_1979_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_a_1974_);
v___x_1983_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
v_a_1973_ = v_tail_1977_;
v_a_1974_ = v___x_1983_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object* v_init_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1988_) == 0)
{
lean_object* v_k_1989_; lean_object* v_l_1990_; lean_object* v_r_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_k_1989_ = lean_ctor_get(v_x_1988_, 1);
v_l_1990_ = lean_ctor_get(v_x_1988_, 3);
v_r_1991_ = lean_ctor_get(v_x_1988_, 4);
v___x_1992_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_1987_, v_r_1991_);
lean_inc(v_k_1989_);
v___x_1993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1993_, 0, v_k_1989_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v_init_1987_ = v___x_1993_;
v_x_1988_ = v_l_1990_;
goto _start;
}
else
{
return v_init_1987_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object* v_init_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_1995_, v_x_1996_);
lean_dec(v_x_1996_);
return v_res_1997_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(lean_object* v_as_x27_2001_, lean_object* v_b_2002_){
_start:
{
if (lean_obj_tag(v_as_x27_2001_) == 0)
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_b_2002_);
return v___x_2004_;
}
else
{
lean_object* v_head_2005_; lean_object* v_snd_2006_; lean_object* v_tail_2007_; lean_object* v_fst_2008_; lean_object* v_ctorNames_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_head_2005_ = lean_ctor_get(v_as_x27_2001_, 0);
v_snd_2006_ = lean_ctor_get(v_head_2005_, 1);
v_tail_2007_ = lean_ctor_get(v_as_x27_2001_, 1);
v_fst_2008_ = lean_ctor_get(v_head_2005_, 0);
v_ctorNames_2009_ = lean_ctor_get(v_snd_2006_, 1);
lean_inc(v_fst_2008_);
v___x_2010_ = l_Lean_mkFVar(v_fst_2008_);
v___x_2011_ = l_Lean_MessageData_ofExpr(v___x_2010_);
v___x_2012_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v___x_2014_, v_ctorNames_2009_);
v___x_2016_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(v___x_2015_, v___x_2014_);
v___x_2017_ = l_Lean_MessageData_ofList(v___x_2016_);
v___x_2018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2013_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v___x_2019_ = l_Lean_indentD(v___x_2018_);
v___x_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2020_, 0, v_b_2002_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v_as_x27_2001_ = v_tail_2007_;
v_b_2002_ = v___x_2020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___boxed(lean_object* v_as_x27_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2022_, v_b_2023_);
lean_dec(v_as_x27_2022_);
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2037_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5));
v___x_2038_ = l_Lean_Name_append(v___x_2037_, v___x_2036_);
return v___x_2038_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8));
v___x_2043_ = l_Lean_MessageData_ofFormat(v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object* v_code_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; 
lean_inc_ref(v_code_2044_);
v___x_2050_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2104_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2104_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2104_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_a_2051_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
lean_dec(v_a_2051_);
lean_dec_ref(v_code_2044_);
v___x_2079_ = lean_box(0);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2079_);
v___x_2081_ = v___x_2053_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
else
{
lean_object* v_toCold_2083_; lean_object* v_options_2084_; uint8_t v_hasTrace_2085_; 
lean_del_object(v___x_2053_);
v_toCold_2083_ = lean_ctor_get(v_a_2047_, 0);
v_options_2084_ = lean_ctor_get(v_toCold_2083_, 2);
v_hasTrace_2085_ = lean_ctor_get_uint8(v_options_2084_, sizeof(void*)*1);
if (v_hasTrace_2085_ == 0)
{
goto v___jp_2055_;
}
else
{
lean_object* v_inheritedTraceOptions_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_inheritedTraceOptions_2086_ = lean_ctor_get(v_toCold_2083_, 11);
v___x_2087_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2088_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6);
v___x_2089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2086_, v_options_2084_, v___x_2088_);
if (v___x_2089_ == 0)
{
goto v___jp_2055_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_a_2094_; lean_object* v___x_2095_; 
v___x_2090_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9);
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v___x_2091_, v_a_2051_);
v___x_2093_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v___x_2092_, v___x_2090_);
lean_dec(v___x_2092_);
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2093_);
v___x_2095_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v___x_2087_, v_a_2094_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
goto v___jp_2055_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2051_);
lean_dec_ref(v_code_2044_);
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
v___jp_2055_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2056_ = lean_box(1);
v___x_2057_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_2058_ = lean_st_mk_ref(v___x_2056_);
v___x_2059_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_2044_, v_a_2051_, v___x_2058_, v___x_2057_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2051_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2069_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2069_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2069_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2064_ = lean_st_ref_get(v___x_2058_);
lean_dec(v___x_2058_);
lean_dec(v___x_2064_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_a_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2065_);
v___x_2067_ = v___x_2062_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v___x_2058_);
v_a_2070_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2059_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2059_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_code_2044_);
v_a_2105_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2050_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2050_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object* v_code_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v_code_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object* v_as_2120_, lean_object* v_as_x27_2121_, lean_object* v_b_2122_, lean_object* v_a_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2121_, v_b_2122_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object* v_as_2130_, lean_object* v_as_x27_2131_, lean_object* v_b_2132_, lean_object* v_a_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v_as_2130_, v_as_x27_2131_, v_b_2132_, v_a_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v_as_x27_2131_);
lean_dec(v_as_2130_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2214_ = 0;
v___x_2215_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_));
v___x_2216_ = l_Lean_registerTraceClass(v___x_2213_, v___x_2214_, v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
return v_res_2218_;
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
