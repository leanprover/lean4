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
lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(lean_object* v_decl_39_, lean_object* v_a_40_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_39_ = stack[0].m_obj;
lean_object* v_a_40_ = stack[1].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_39_, v_a_40_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg___boxed(lean_object* v_decl_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_69_, v_a_70_);
lean_dec_ref(v_a_70_);
lean_dec_ref(v_decl_69_);
return v_res_72_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(lean_object* v_decl_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_73_, v_a_74_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_isJpCases_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_73_ = stack[0].m_obj;
lean_object* v_a_74_ = stack[1].m_obj;
lean_object* v_a_75_ = stack[2].m_obj;
lean_object* v_a_76_ = stack[3].m_obj;
lean_object* v_a_77_ = stack[4].m_obj;
lean_object* v_res_80_;
v_res_80_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(v_decl_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___boxed(lean_object* v_decl_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(v_decl_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec_ref(v_decl_81_);
return v_res_87_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = l_Lean_NameSet_empty;
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0, &l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default;
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object* v_init_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v_v_106_; lean_object* v_l_107_; lean_object* v_r_108_; lean_object* v___x_109_; 
v_v_106_ = lean_ctor_get(v_x_105_, 2);
v_l_107_ = lean_ctor_get(v_x_105_, 3);
v_r_108_ = lean_ctor_get(v_x_105_, 4);
v___x_109_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_104_, v_l_107_);
if (lean_obj_tag(v___x_109_) == 0)
{
return v___x_109_;
}
else
{
lean_object* v_ctorNames_110_; 
lean_dec_ref_known(v___x_109_, 1);
v_ctorNames_110_ = lean_ctor_get(v_v_106_, 1);
if (lean_obj_tag(v_ctorNames_110_) == 0)
{
lean_object* v___x_111_; 
v___x_111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2));
return v___x_111_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v_init_104_ = v___x_112_;
v_x_105_ = v_r_108_;
goto _start;
}
}
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v_init_104_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___boxed(lean_object* v_init_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_115_, v_x_116_);
lean_dec(v_x_116_);
return v_res_117_;
}
}
uint8_t l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(lean_object* v_info_118_){
_start:
{
lean_object* v___y_120_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_a_127_; 
v___x_125_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v___x_126_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v___x_125_, v_info_118_);
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref(v___x_126_);
v___y_120_ = v_a_127_;
goto v___jp_119_;
v___jp_119_:
{
lean_object* v_fst_121_; 
v_fst_121_ = lean_ctor_get(v___y_120_, 0);
lean_inc(v_fst_121_);
lean_dec_ref(v___y_120_);
if (lean_obj_tag(v_fst_121_) == 0)
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
else
{
lean_object* v_val_123_; uint8_t v___x_124_; 
v_val_123_ = lean_ctor_get(v_fst_121_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_fst_121_, 1);
v___x_124_ = lean_unbox(v_val_123_);
lean_dec(v_val_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_118_ = stack[0].m_obj;
uint8_t v_res_128_;
v_res_128_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_info_118_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(lean_object* v_info_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_info_129_);
lean_dec(v_info_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(lean_object* v_t_132_, lean_object* v_k_133_){
_start:
{
if (lean_obj_tag(v_t_132_) == 0)
{
lean_object* v_k_134_; lean_object* v_v_135_; lean_object* v_l_136_; lean_object* v_r_137_; uint8_t v___x_138_; 
v_k_134_ = lean_ctor_get(v_t_132_, 1);
v_v_135_ = lean_ctor_get(v_t_132_, 2);
v_l_136_ = lean_ctor_get(v_t_132_, 3);
v_r_137_ = lean_ctor_get(v_t_132_, 4);
v___x_138_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_133_, v_k_134_);
switch(v___x_138_)
{
case 0:
{
v_t_132_ = v_l_136_;
goto _start;
}
case 1:
{
lean_object* v___x_140_; 
lean_inc(v_v_135_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_v_135_);
return v___x_140_;
}
default: 
{
v_t_132_ = v_r_137_;
goto _start;
}
}
}
else
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(0);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(lean_object* v_t_143_, lean_object* v_k_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_143_, v_k_144_);
lean_dec(v_k_144_);
lean_dec(v_t_143_);
return v_res_145_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(lean_object* v_code_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
switch(lean_obj_tag(v_code_146_))
{
case 0:
{
lean_object* v_k_154_; 
v_k_154_ = lean_ctor_get(v_code_146_, 1);
lean_inc_ref(v_k_154_);
lean_dec_ref_known(v_code_146_, 2);
v_code_146_ = v_k_154_;
goto _start;
}
case 1:
{
lean_object* v_decl_156_; lean_object* v_k_157_; lean_object* v_value_158_; lean_object* v___x_159_; 
v_decl_156_ = lean_ctor_get(v_code_146_, 0);
lean_inc_ref(v_decl_156_);
v_k_157_ = lean_ctor_get(v_code_146_, 1);
lean_inc_ref(v_k_157_);
lean_dec_ref_known(v_code_146_, 2);
v_value_158_ = lean_ctor_get(v_decl_156_, 4);
lean_inc_ref(v_value_158_);
lean_dec_ref(v_decl_156_);
v___x_159_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_158_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_dec_ref_known(v___x_159_, 1);
v_code_146_ = v_k_157_;
goto _start;
}
else
{
lean_dec_ref(v_k_157_);
return v___x_159_;
}
}
case 2:
{
lean_object* v_decl_161_; lean_object* v_k_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_195_; 
v_decl_161_ = lean_ctor_get(v_code_146_, 0);
v_k_162_ = lean_ctor_get(v_code_146_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_code_146_);
if (v_isSharedCheck_195_ == 0)
{
v___x_164_ = v_code_146_;
v_isShared_165_ = v_isSharedCheck_195_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_k_162_);
lean_inc(v_decl_161_);
lean_dec(v_code_146_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_195_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___x_176_; 
v___x_176_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_161_, v_a_149_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
if (lean_obj_tag(v_a_177_) == 1)
{
lean_object* v_val_178_; lean_object* v___x_179_; lean_object* v_fvarId_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v_val_178_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_val_178_);
lean_dec_ref_known(v_a_177_, 1);
v___x_179_ = lean_st_ref_take(v_a_147_);
v_fvarId_180_ = lean_ctor_get(v_decl_161_, 0);
v___x_181_ = l_Lean_NameSet_empty;
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 0);
lean_ctor_set(v___x_164_, 1, v___x_181_);
lean_ctor_set(v___x_164_, 0, v_val_178_);
v___x_183_ = v___x_164_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_val_178_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_186_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_inc(v_fvarId_180_);
v___x_184_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_180_, v___x_183_, v___x_179_);
v___x_185_ = lean_st_ref_put(v_a_147_, v___x_184_);
v___y_167_ = v_a_147_;
v___y_168_ = v_a_148_;
v___y_169_ = v_a_149_;
v___y_170_ = v_a_150_;
v___y_171_ = v_a_151_;
v___y_172_ = v_a_152_;
goto v___jp_166_;
}
}
else
{
lean_dec(v_a_177_);
lean_del_object(v___x_164_);
v___y_167_ = v_a_147_;
v___y_168_ = v_a_148_;
v___y_169_ = v_a_149_;
v___y_170_ = v_a_150_;
v___y_171_ = v_a_151_;
v___y_172_ = v_a_152_;
goto v___jp_166_;
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_del_object(v___x_164_);
lean_dec_ref(v_k_162_);
lean_dec_ref(v_decl_161_);
v_a_187_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_176_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_176_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
v___jp_166_:
{
lean_object* v_value_173_; lean_object* v___x_174_; 
v_value_173_ = lean_ctor_get(v_decl_161_, 4);
lean_inc_ref(v_value_173_);
lean_dec_ref(v_decl_161_);
v___x_174_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_173_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_dec_ref_known(v___x_174_, 1);
v_code_146_ = v_k_162_;
v_a_147_ = v___y_167_;
v_a_148_ = v___y_168_;
v_a_149_ = v___y_169_;
v_a_150_ = v___y_170_;
v_a_151_ = v___y_171_;
v_a_152_ = v___y_172_;
goto _start;
}
else
{
lean_dec_ref(v_k_162_);
return v___x_174_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_196_; lean_object* v_args_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_fvarId_196_ = lean_ctor_get(v_code_146_, 0);
lean_inc(v_fvarId_196_);
v_args_197_ = lean_ctor_get(v_code_146_, 1);
lean_inc_ref(v_args_197_);
lean_dec_ref_known(v_code_146_, 2);
v___x_198_ = lean_st_ref_get(v_a_147_);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_198_, v_fvarId_196_);
lean_dec(v___x_198_);
if (lean_obj_tag(v___x_199_) == 1)
{
lean_object* v_val_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_247_; 
v_val_200_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_247_ == 0)
{
v___x_202_ = v___x_199_;
v_isShared_203_ = v_isSharedCheck_247_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_val_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_247_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v_paramIdx_204_; lean_object* v_ctorNames_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_246_; 
v_paramIdx_204_ = lean_ctor_get(v_val_200_, 0);
v_ctorNames_205_ = lean_ctor_get(v_val_200_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_val_200_);
if (v_isSharedCheck_246_ == 0)
{
v___x_207_ = v_val_200_;
v_isShared_208_ = v_isSharedCheck_246_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_ctorNames_205_);
lean_inc(v_paramIdx_204_);
lean_dec(v_val_200_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_246_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(0);
v___x_210_ = lean_array_get(v___x_209_, v_args_197_, v_paramIdx_204_);
lean_dec_ref(v_args_197_);
if (lean_obj_tag(v___x_210_) == 1)
{
lean_object* v_fvarId_211_; lean_object* v___x_212_; 
lean_del_object(v___x_202_);
v_fvarId_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_fvarId_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(v_fvarId_211_, v_a_148_, v_a_150_, v_a_152_);
lean_dec(v_fvarId_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_233_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_233_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_233_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_233_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
if (lean_obj_tag(v_a_213_) == 1)
{
lean_object* v_val_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v_val_217_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v_a_213_, 1);
v___x_218_ = lean_st_ref_take(v_a_147_);
v___x_219_ = lean_box(0);
v___x_220_ = l_Lean_NameSet_insert(v_ctorNames_205_, v_val_217_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v___x_220_);
v___x_222_ = v___x_207_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_paramIdx_204_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_228_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_223_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_196_, v___x_222_, v___x_218_);
v___x_224_ = lean_st_ref_put(v_a_147_, v___x_223_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_219_);
v___x_226_ = v___x_215_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_219_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v_a_213_);
lean_del_object(v___x_207_);
lean_dec(v_ctorNames_205_);
lean_dec(v_paramIdx_204_);
lean_dec(v_fvarId_196_);
v___x_229_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_229_);
v___x_231_ = v___x_215_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_del_object(v___x_207_);
lean_dec(v_ctorNames_205_);
lean_dec(v_paramIdx_204_);
lean_dec(v_fvarId_196_);
v_a_234_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_212_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_212_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_244_; 
lean_dec(v___x_210_);
lean_del_object(v___x_207_);
lean_dec(v_ctorNames_205_);
lean_dec(v_paramIdx_204_);
lean_dec(v_fvarId_196_);
v___x_242_ = lean_box(0);
if (v_isShared_203_ == 0)
{
lean_ctor_set_tag(v___x_202_, 0);
lean_ctor_set(v___x_202_, 0, v___x_242_);
v___x_244_ = v___x_202_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v___x_199_);
lean_dec_ref(v_args_197_);
lean_dec(v_fvarId_196_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
case 4:
{
lean_object* v_cases_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_273_; 
v_cases_250_ = lean_ctor_get(v_code_146_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_code_146_);
if (v_isSharedCheck_273_ == 0)
{
v___x_252_ = v_code_146_;
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_cases_250_);
lean_dec(v_code_146_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_discr_254_; lean_object* v_alts_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_discr_254_ = lean_ctor_get(v_cases_250_, 2);
lean_inc(v_discr_254_);
v_alts_255_ = lean_ctor_get(v_cases_250_, 3);
lean_inc_ref(v_alts_255_);
lean_dec_ref(v_cases_250_);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_array_get_size(v_alts_255_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_nat_dec_lt(v___x_256_, v___x_257_);
if (v___x_259_ == 0)
{
lean_object* v___x_261_; 
lean_dec_ref(v_alts_255_);
lean_dec(v_discr_254_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 0);
lean_ctor_set(v___x_252_, 0, v___x_258_);
v___x_261_ = v___x_252_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_258_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
else
{
uint8_t v___x_263_; 
v___x_263_ = lean_nat_dec_le(v___x_257_, v___x_257_);
if (v___x_263_ == 0)
{
if (v___x_259_ == 0)
{
lean_object* v___x_265_; 
lean_dec_ref(v_alts_255_);
lean_dec(v_discr_254_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 0);
lean_ctor_set(v___x_252_, 0, v___x_258_);
v___x_265_ = v___x_252_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_258_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; 
lean_del_object(v___x_252_);
v___x_267_ = ((size_t)0ULL);
v___x_268_ = lean_usize_of_nat(v___x_257_);
v___x_269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_254_, v_alts_255_, v___x_267_, v___x_268_, v___x_258_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec_ref(v_alts_255_);
return v___x_269_;
}
}
else
{
size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
lean_del_object(v___x_252_);
v___x_270_ = ((size_t)0ULL);
v___x_271_ = lean_usize_of_nat(v___x_257_);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_254_, v_alts_255_, v___x_270_, v___x_271_, v___x_258_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec_ref(v_alts_255_);
return v___x_272_;
}
}
}
}
default: 
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_isSharedCheck_281_ = !lean_is_exclusive(v_code_146_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v_code_146_, 0);
lean_dec(v_unused_282_);
v___x_275_ = v_code_146_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_code_146_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_box(0);
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 0);
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_146_ = stack[0].m_obj;
lean_object* v_a_147_ = stack[1].m_obj;
lean_object* v_a_148_ = stack[2].m_obj;
lean_object* v_a_149_ = stack[3].m_obj;
lean_object* v_a_150_ = stack[4].m_obj;
lean_object* v_a_151_ = stack[5].m_obj;
lean_object* v_a_152_ = stack[6].m_obj;
lean_object* v_res_283_;
v_res_283_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
stack->m_obj
 = v_res_283_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object* v_discr_284_, lean_object* v_as_285_, size_t v_i_286_, size_t v_stop_287_, lean_object* v_b_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___y_297_; uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_eq(v_i_286_, v_stop_287_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_array_uget_borrowed(v_as_285_, v_i_286_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_ctorName_304_; lean_object* v_params_305_; lean_object* v_code_306_; lean_object* v___x_307_; 
v_ctorName_304_ = lean_ctor_get(v___x_303_, 0);
v_params_305_ = lean_ctor_get(v___x_303_, 1);
v_code_306_ = lean_ctor_get(v___x_303_, 2);
lean_inc_ref(v_params_305_);
lean_inc(v_ctorName_304_);
lean_inc(v_discr_284_);
v___x_307_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_284_, v_ctorName_304_, v_params_305_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
lean_inc_ref(v_code_306_);
v___x_309_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_306_, v___y_289_, v_a_308_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v_a_308_);
v___y_297_ = v___x_309_;
goto v___jp_296_;
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec(v_discr_284_);
v_a_310_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_307_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_307_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
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
else
{
lean_object* v_code_318_; lean_object* v___x_319_; 
v_code_318_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_code_318_);
v___x_319_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_318_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
v___y_297_ = v___x_319_;
goto v___jp_296_;
}
}
else
{
lean_object* v___x_320_; 
lean_dec(v_discr_284_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_b_288_);
return v___x_320_;
}
v___jp_296_:
{
if (lean_obj_tag(v___y_297_) == 0)
{
lean_object* v_a_298_; size_t v___x_299_; size_t v___x_300_; 
v_a_298_ = lean_ctor_get(v___y_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___y_297_, 1);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_i_286_, v___x_299_);
v_i_286_ = v___x_300_;
v_b_288_ = v_a_298_;
goto _start;
}
else
{
lean_dec(v_discr_284_);
return v___y_297_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_284_ = stack[0].m_obj;
lean_object* v_as_285_ = stack[1].m_obj;
size_t v_i_286_ = stack[2].m_num;
size_t v_stop_287_ = stack[3].m_num;
lean_object* v_b_288_ = stack[4].m_obj;
lean_object* v___y_289_ = stack[5].m_obj;
lean_object* v___y_290_ = stack[6].m_obj;
lean_object* v___y_291_ = stack[7].m_obj;
lean_object* v___y_292_ = stack[8].m_obj;
lean_object* v___y_293_ = stack[9].m_obj;
lean_object* v___y_294_ = stack[10].m_obj;
lean_object* v_res_321_;
v_res_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_284_, v_as_285_, v_i_286_, v_stop_287_, v_b_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object* v_discr_322_, lean_object* v_as_323_, lean_object* v_i_324_, lean_object* v_stop_325_, lean_object* v_b_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
size_t v_i_boxed_334_; size_t v_stop_boxed_335_; lean_object* v_res_336_; 
v_i_boxed_334_ = lean_unbox_usize(v_i_324_);
lean_dec(v_i_324_);
v_stop_boxed_335_ = lean_unbox_usize(v_stop_325_);
lean_dec(v_stop_325_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_322_, v_as_323_, v_i_boxed_334_, v_stop_boxed_335_, v_b_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v_as_323_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object* v_code_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object* v_00_u03b4_346_, lean_object* v_t_347_, lean_object* v_k_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_347_, v_k_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object* v_00_u03b4_350_, lean_object* v_t_351_, lean_object* v_k_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(v_00_u03b4_350_, v_t_351_, v_k_352_);
lean_dec(v_k_352_);
lean_dec(v_t_351_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1);
v___x_358_ = lean_box(1);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
return v___x_359_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object* v_code_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_366_ = lean_box(1);
v___x_367_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_368_ = lean_st_mk_ref(v___x_366_);
v___x_369_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_360_, v___x_368_, v___x_367_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_369_, 0);
lean_dec(v_unused_378_);
v___x_371_ = v___x_369_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_dec(v___x_369_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_st_ref_get(v___x_368_);
lean_dec(v___x_368_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v___x_368_);
v_a_379_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_369_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_369_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_360_ = stack[0].m_obj;
lean_object* v_a_361_ = stack[1].m_obj;
lean_object* v_a_362_ = stack[2].m_obj;
lean_object* v_a_363_ = stack[3].m_obj;
lean_object* v_a_364_ = stack[4].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object* v_code_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
return v_res_394_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Array_instInhabited___redArg();
return v___x_395_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1(void){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Compiler_LCNF_instInhabitedCases_default__1___redArg();
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(lean_object* v_msg_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_398_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0);
v___x_399_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_panic_fn_borrowed(v___x_400_, v_msg_397_);
lean_dec_ref_known(v___x_400_, 2);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2));
v___x_406_ = lean_unsigned_to_nat(11u);
v___x_407_ = lean_unsigned_to_nat(100u);
v___x_408_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1));
v___x_409_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0));
v___x_410_ = l_mkPanicMessageWithDecl(v___x_409_, v___x_408_, v___x_407_, v___x_406_, v___x_405_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(lean_object* v_code_411_, lean_object* v_decls_412_){
_start:
{
switch(lean_obj_tag(v_code_411_))
{
case 0:
{
lean_object* v_decl_413_; lean_object* v_k_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_decl_413_ = lean_ctor_get(v_code_411_, 0);
v_k_414_ = lean_ctor_get(v_code_411_, 1);
lean_inc_ref(v_decl_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v_decl_413_);
v___x_416_ = lean_array_push(v_decls_412_, v___x_415_);
v_code_411_ = v_k_414_;
v_decls_412_ = v___x_416_;
goto _start;
}
case 4:
{
lean_object* v_cases_418_; lean_object* v___x_419_; 
v_cases_418_ = lean_ctor_get(v_code_411_, 0);
lean_inc_ref(v_cases_418_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_decls_412_);
lean_ctor_set(v___x_419_, 1, v_cases_418_);
return v___x_419_;
}
default: 
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec_ref(v_decls_412_);
v___x_420_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3);
v___x_421_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(v___x_420_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(lean_object* v_code_422_, lean_object* v_decls_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_422_, v_decls_423_);
lean_dec_ref(v_code_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(lean_object* v_code_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0));
v___x_429_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(v_code_427_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(lean_object* v_code_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_code_430_);
lean_dec_ref(v_code_430_);
return v_res_431_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(lean_object* v_singleton_432_, lean_object* v_as_433_, size_t v_i_434_, size_t v_stop_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_eq(v_i_434_, v_stop_435_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = 0;
v___x_438_ = lean_array_uget_borrowed(v_as_433_, v_i_434_);
v___x_439_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v___x_437_, v___x_438_, v_singleton_432_);
if (v___x_439_ == 0)
{
size_t v___x_440_; size_t v___x_441_; 
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_i_434_, v___x_440_);
v_i_434_ = v___x_441_;
goto _start;
}
else
{
return v___x_439_;
}
}
else
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_singleton_432_ = stack[0].m_obj;
lean_object* v_as_433_ = stack[1].m_obj;
size_t v_i_434_ = stack[2].m_num;
size_t v_stop_435_ = stack[3].m_num;
uint8_t v_res_444_;
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_432_, v_as_433_, v_i_434_, v_stop_435_);
stack->m_num = v_res_444_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(lean_object* v_singleton_445_, lean_object* v_as_446_, lean_object* v_i_447_, lean_object* v_stop_448_){
_start:
{
size_t v_i_boxed_449_; size_t v_stop_boxed_450_; uint8_t v_res_451_; lean_object* v_r_452_; 
v_i_boxed_449_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_stop_boxed_450_ = lean_unbox_usize(v_stop_448_);
lean_dec(v_stop_448_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_445_, v_as_446_, v_i_boxed_449_, v_stop_boxed_450_);
lean_dec_ref(v_as_446_);
lean_dec(v_singleton_445_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(size_t v_sz_453_, size_t v_i_454_, lean_object* v_bs_455_, uint8_t v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_bs_455_);
return v___x_464_;
}
else
{
uint8_t v___x_465_; lean_object* v_v_466_; lean_object* v___x_467_; lean_object* v_bs_x27_468_; lean_object* v___x_469_; 
v___x_465_ = 0;
v_v_466_ = lean_array_uget(v_bs_455_, v_i_454_);
v___x_467_ = lean_unsigned_to_nat(0u);
v_bs_x27_468_ = lean_array_uset(v_bs_455_, v_i_454_, v___x_467_);
v___x_469_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_465_, v_v_466_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_454_, v___x_471_);
v___x_473_ = lean_array_uset(v_bs_x27_468_, v_i_454_, v_a_470_);
v_i_454_ = v___x_472_;
v_bs_455_ = v___x_473_;
goto _start;
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_bs_x27_468_);
v_a_475_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_469_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_469_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_453_ = stack[0].m_num;
size_t v_i_454_ = stack[1].m_num;
lean_object* v_bs_455_ = stack[2].m_obj;
uint8_t v___y_456_ = stack[3].m_num;
lean_object* v___y_457_ = stack[4].m_obj;
lean_object* v___y_458_ = stack[5].m_obj;
lean_object* v___y_459_ = stack[6].m_obj;
lean_object* v___y_460_ = stack[7].m_obj;
lean_object* v___y_461_ = stack[8].m_obj;
lean_object* v_res_483_;
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_453_, v_i_454_, v_bs_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(lean_object* v_sz_484_, lean_object* v_i_485_, lean_object* v_bs_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
size_t v_sz_boxed_494_; size_t v_i_boxed_495_; uint8_t v___y_5220__boxed_496_; lean_object* v_res_497_; 
v_sz_boxed_494_ = lean_unbox_usize(v_sz_484_);
lean_dec(v_sz_484_);
v_i_boxed_495_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v___y_5220__boxed_496_ = lean_unbox(v___y_487_);
v_res_497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_boxed_494_, v_i_boxed_495_, v_bs_486_, v___y_5220__boxed_496_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
return v_res_497_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(lean_object* v_fields_498_, lean_object* v_____r_499_, lean_object* v_paramsNew_500_, uint8_t v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
size_t v_sz_508_; size_t v___x_509_; lean_object* v___x_510_; 
v_sz_508_ = lean_array_size(v_fields_498_);
v___x_509_ = ((size_t)0ULL);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_508_, v___x_509_, v_fields_498_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_520_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_520_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_515_ = l_Array_append___redArg(v_paramsNew_500_, v_a_511_);
lean_dec(v_a_511_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_516_);
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v_paramsNew_500_);
v_a_521_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_510_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_510_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fields_498_ = stack[0].m_obj;
lean_object* v_____r_499_ = stack[1].m_obj;
lean_object* v_paramsNew_500_ = stack[2].m_obj;
uint8_t v___y_501_ = stack[3].m_num;
lean_object* v___y_502_ = stack[4].m_obj;
lean_object* v___y_503_ = stack[5].m_obj;
lean_object* v___y_504_ = stack[6].m_obj;
lean_object* v___y_505_ = stack[7].m_obj;
lean_object* v___y_506_ = stack[8].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_498_, v_____r_499_, v_paramsNew_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(lean_object* v_fields_530_, lean_object* v_____r_531_, lean_object* v_paramsNew_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
uint8_t v___y_5310__boxed_540_; lean_object* v_res_541_; 
v___y_5310__boxed_540_ = lean_unbox(v___y_533_);
v_res_541_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_530_, v_____r_531_, v_paramsNew_532_, v___y_5310__boxed_540_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
return v_res_541_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(lean_object* v_upperBound_542_, lean_object* v_params_543_, lean_object* v_targetParamIdx_544_, uint8_t v___y_545_, lean_object* v_fields_546_, lean_object* v_a_547_, lean_object* v_b_548_, uint8_t v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_a_557_; lean_object* v___y_562_; uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_lt(v_a_547_, v_upperBound_542_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v_a_547_);
lean_dec_ref(v_fields_546_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_b_548_);
return v___x_582_;
}
else
{
uint8_t v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = 0;
v___x_584_ = lean_array_fget_borrowed(v_params_543_, v_a_547_);
v___x_585_ = lean_nat_dec_eq(v_targetParamIdx_544_, v_a_547_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_inc(v___x_584_);
v___x_586_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_583_, v___x_584_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = lean_array_push(v_b_548_, v_a_587_);
v_a_557_ = v___x_588_;
goto v___jp_556_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_b_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_fields_546_);
v_a_589_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_586_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_586_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
if (v___y_545_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(0);
lean_inc_ref(v_fields_546_);
v___x_598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_546_, v___x_597_, v_b_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
v___y_562_ = v___x_598_;
goto v___jp_561_;
}
else
{
lean_object* v___x_599_; 
lean_inc(v___x_584_);
v___x_599_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_583_, v___x_584_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_array_push(v_b_548_, v_a_600_);
v___x_602_ = lean_box(0);
lean_inc_ref(v_fields_546_);
v___x_603_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_546_, v___x_602_, v___x_601_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
v___y_562_ = v___x_603_;
goto v___jp_561_;
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_b_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_fields_546_);
v_a_604_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_599_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_599_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
v___jp_556_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_add(v_a_547_, v___x_558_);
lean_dec(v_a_547_);
v_a_547_ = v___x_559_;
v_b_548_ = v_a_557_;
goto _start;
}
v___jp_561_:
{
if (lean_obj_tag(v___y_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v_a_563_ = lean_ctor_get(v___y_562_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___y_562_);
if (v_isSharedCheck_572_ == 0)
{
v___x_565_ = v___y_562_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___y_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_a_563_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; 
lean_dec(v_a_547_);
lean_dec_ref(v_fields_546_);
v_a_567_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v_a_563_, 1);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_a_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
else
{
lean_object* v_a_571_; 
lean_del_object(v___x_565_);
v_a_571_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v_a_563_, 1);
v_a_557_ = v_a_571_;
goto v___jp_556_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_a_547_);
lean_dec_ref(v_fields_546_);
v_a_573_ = lean_ctor_get(v___y_562_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___y_562_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___y_562_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___y_562_);
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
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_542_ = stack[0].m_obj;
lean_object* v_params_543_ = stack[1].m_obj;
lean_object* v_targetParamIdx_544_ = stack[2].m_obj;
uint8_t v___y_545_ = stack[3].m_num;
lean_object* v_fields_546_ = stack[4].m_obj;
lean_object* v_a_547_ = stack[5].m_obj;
lean_object* v_b_548_ = stack[6].m_obj;
uint8_t v___y_549_ = stack[7].m_num;
lean_object* v___y_550_ = stack[8].m_obj;
lean_object* v___y_551_ = stack[9].m_obj;
lean_object* v___y_552_ = stack[10].m_obj;
lean_object* v___y_553_ = stack[11].m_obj;
lean_object* v___y_554_ = stack[12].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_542_, v_params_543_, v_targetParamIdx_544_, v___y_545_, v_fields_546_, v_a_547_, v_b_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(lean_object* v_upperBound_613_, lean_object* v_params_614_, lean_object* v_targetParamIdx_615_, lean_object* v___y_616_, lean_object* v_fields_617_, lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___y_5410__boxed_627_; uint8_t v___y_5411__boxed_628_; lean_object* v_res_629_; 
v___y_5410__boxed_627_ = lean_unbox(v___y_616_);
v___y_5411__boxed_628_ = lean_unbox(v___y_620_);
v_res_629_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_613_, v_params_614_, v_targetParamIdx_615_, v___y_5410__boxed_627_, v_fields_617_, v_a_618_, v_b_619_, v___y_5411__boxed_628_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec(v_targetParamIdx_615_);
lean_dec_ref(v_params_614_);
lean_dec(v_upperBound_613_);
return v_res_629_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(size_t v_sz_630_, size_t v_i_631_, lean_object* v_bs_632_, uint8_t v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_631_, v_sz_630_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v_bs_632_);
return v___x_641_;
}
else
{
uint8_t v___x_642_; lean_object* v_v_643_; lean_object* v___x_644_; lean_object* v_bs_x27_645_; lean_object* v___x_646_; 
v___x_642_ = 0;
v_v_643_ = lean_array_uget(v_bs_632_, v_i_631_);
v___x_644_ = lean_unsigned_to_nat(0u);
v_bs_x27_645_ = lean_array_uset(v_bs_632_, v_i_631_, v___x_644_);
v___x_646_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_642_, v_v_643_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_631_, v___x_648_);
v___x_650_ = lean_array_uset(v_bs_x27_645_, v_i_631_, v_a_647_);
v_i_631_ = v___x_649_;
v_bs_632_ = v___x_650_;
goto _start;
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_bs_x27_645_);
v_a_652_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_646_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_646_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_630_ = stack[0].m_num;
size_t v_i_631_ = stack[1].m_num;
lean_object* v_bs_632_ = stack[2].m_obj;
uint8_t v___y_633_ = stack[3].m_num;
lean_object* v___y_634_ = stack[4].m_obj;
lean_object* v___y_635_ = stack[5].m_obj;
lean_object* v___y_636_ = stack[6].m_obj;
lean_object* v___y_637_ = stack[7].m_obj;
lean_object* v___y_638_ = stack[8].m_obj;
lean_object* v_res_660_;
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_630_, v_i_631_, v_bs_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(lean_object* v_sz_661_, lean_object* v_i_662_, lean_object* v_bs_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; uint8_t v___y_5622__boxed_673_; lean_object* v_res_674_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_661_);
lean_dec(v_sz_661_);
v_i_boxed_672_ = lean_unbox_usize(v_i_662_);
lean_dec(v_i_662_);
v___y_5622__boxed_673_ = lean_unbox(v___y_664_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_boxed_671_, v_i_boxed_672_, v_bs_663_, v___y_5622__boxed_673_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
return v_res_674_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_675_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object* v_decls_681_, lean_object* v_params_682_, lean_object* v_targetParamIdx_683_, lean_object* v_fields_684_, lean_object* v_k_685_, uint8_t v_default_686_, uint8_t v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_fvarId_696_; lean_object* v___x_697_; lean_object* v_paramsNew_698_; uint8_t v___x_699_; uint8_t v___y_701_; lean_object* v_singleton_755_; uint8_t v___x_756_; 
v___x_694_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0);
v___x_695_ = lean_array_get_borrowed(v___x_694_, v_params_682_, v_targetParamIdx_683_);
v_fvarId_696_ = lean_ctor_get(v___x_695_, 0);
v___x_697_ = lean_unsigned_to_nat(0u);
v_paramsNew_698_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
v___x_699_ = 0;
lean_inc(v_fvarId_696_);
v_singleton_755_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_696_);
v___x_756_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_699_, v_k_685_, v_singleton_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_decls_681_);
v___x_758_ = lean_nat_dec_lt(v___x_697_, v___x_757_);
if (v___x_758_ == 0)
{
lean_dec(v_singleton_755_);
v___y_701_ = v___x_758_;
goto v___jp_700_;
}
else
{
if (v___x_758_ == 0)
{
lean_dec(v_singleton_755_);
v___y_701_ = v___x_758_;
goto v___jp_700_;
}
else
{
size_t v___x_759_; size_t v___x_760_; uint8_t v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_757_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_755_, v_decls_681_, v___x_759_, v___x_760_);
lean_dec(v_singleton_755_);
v___y_701_ = v___x_761_;
goto v___jp_700_;
}
}
}
else
{
lean_dec(v_singleton_755_);
v___y_701_ = v___x_756_;
goto v___jp_700_;
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_array_get_size(v_params_682_);
v___x_703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v___x_702_, v_params_682_, v_targetParamIdx_683_, v___y_701_, v_fields_684_, v___x_697_, v_paramsNew_698_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; size_t v_sz_705_; size_t v___x_706_; lean_object* v___x_707_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v_sz_705_ = lean_array_size(v_decls_681_);
v___x_706_ = ((size_t)0ULL);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_705_, v___x_706_, v_decls_681_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_699_, v_k_685_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_708_, v_a_710_);
lean_dec(v_a_708_);
v___x_712_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3));
v___x_713_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___x_699_, v_a_704_, v___x_711_, v___x_712_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_718_, 0, v_a_714_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1, v_default_686_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*1 + 1, v___y_701_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_a_723_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_713_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_713_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_a_708_);
lean_dec(v_a_704_);
v_a_731_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_709_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_709_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_a_704_);
lean_dec_ref(v_k_685_);
v_a_739_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_707_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_707_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_k_685_);
lean_dec_ref(v_decls_681_);
v_a_747_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_703_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_703_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_681_ = stack[0].m_obj;
lean_object* v_params_682_ = stack[1].m_obj;
lean_object* v_targetParamIdx_683_ = stack[2].m_obj;
lean_object* v_fields_684_ = stack[3].m_obj;
lean_object* v_k_685_ = stack[4].m_obj;
uint8_t v_default_686_ = stack[5].m_num;
uint8_t v_a_687_ = stack[6].m_num;
lean_object* v_a_688_ = stack[7].m_obj;
lean_object* v_a_689_ = stack[8].m_obj;
lean_object* v_a_690_ = stack[9].m_obj;
lean_object* v_a_691_ = stack[10].m_obj;
lean_object* v_a_692_ = stack[11].m_obj;
lean_object* v_res_762_;
v_res_762_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_681_, v_params_682_, v_targetParamIdx_683_, v_fields_684_, v_k_685_, v_default_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object* v_decls_763_, lean_object* v_params_764_, lean_object* v_targetParamIdx_765_, lean_object* v_fields_766_, lean_object* v_k_767_, lean_object* v_default_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
uint8_t v_default_boxed_776_; uint8_t v_a_boxed_777_; lean_object* v_res_778_; 
v_default_boxed_776_ = lean_unbox(v_default_768_);
v_a_boxed_777_ = lean_unbox(v_a_769_);
v_res_778_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_763_, v_params_764_, v_targetParamIdx_765_, v_fields_766_, v_k_767_, v_default_boxed_776_, v_a_boxed_777_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec(v_targetParamIdx_765_);
lean_dec_ref(v_params_764_);
return v_res_778_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object* v_upperBound_779_, lean_object* v_params_780_, lean_object* v_targetParamIdx_781_, uint8_t v___y_782_, lean_object* v_fields_783_, lean_object* v_inst_784_, lean_object* v_R_785_, lean_object* v_a_786_, lean_object* v_b_787_, lean_object* v_c_788_, uint8_t v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_779_, v_params_780_, v_targetParamIdx_781_, v___y_782_, v_fields_783_, v_a_786_, v_b_787_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_796_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_779_ = stack[0].m_obj;
lean_object* v_params_780_ = stack[1].m_obj;
lean_object* v_targetParamIdx_781_ = stack[2].m_obj;
uint8_t v___y_782_ = stack[3].m_num;
lean_object* v_fields_783_ = stack[4].m_obj;
lean_object* v_a_786_ = stack[7].m_obj;
lean_object* v_b_787_ = stack[8].m_obj;
uint8_t v___y_789_ = stack[10].m_num;
lean_object* v___y_790_ = stack[11].m_obj;
lean_object* v___y_791_ = stack[12].m_obj;
lean_object* v___y_792_ = stack[13].m_obj;
lean_object* v___y_793_ = stack[14].m_obj;
lean_object* v___y_794_ = stack[15].m_obj;
lean_object* v_res_797_;
v_res_797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(v_upperBound_779_, v_params_780_, v_targetParamIdx_781_, v___y_782_, v_fields_783_, lean_box(0), lean_box(0), v_a_786_, v_b_787_, lean_box(0), v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
stack->m_obj
 = v_res_797_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_798_ = _args[0];
lean_object* v_params_799_ = _args[1];
lean_object* v_targetParamIdx_800_ = _args[2];
lean_object* v___y_801_ = _args[3];
lean_object* v_fields_802_ = _args[4];
lean_object* v_inst_803_ = _args[5];
lean_object* v_R_804_ = _args[6];
lean_object* v_a_805_ = _args[7];
lean_object* v_b_806_ = _args[8];
lean_object* v_c_807_ = _args[9];
lean_object* v___y_808_ = _args[10];
lean_object* v___y_809_ = _args[11];
lean_object* v___y_810_ = _args[12];
lean_object* v___y_811_ = _args[13];
lean_object* v___y_812_ = _args[14];
lean_object* v___y_813_ = _args[15];
lean_object* v___y_814_ = _args[16];
_start:
{
uint8_t v___y_5929__boxed_815_; uint8_t v___y_5931__boxed_816_; lean_object* v_res_817_; 
v___y_5929__boxed_815_ = lean_unbox(v___y_801_);
v___y_5931__boxed_816_ = lean_unbox(v___y_808_);
v_res_817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(v_upperBound_798_, v_params_799_, v_targetParamIdx_800_, v___y_5929__boxed_815_, v_fields_802_, v_inst_803_, v_R_804_, v_a_805_, v_b_806_, v_c_807_, v___y_5931__boxed_816_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec(v_targetParamIdx_800_);
lean_dec_ref(v_params_799_);
lean_dec(v_upperBound_798_);
return v_res_817_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_unsigned_to_nat(16u);
v___x_820_ = lean_mk_array(v___x_819_, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
return v___x_823_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object* v_decls_824_, lean_object* v_params_825_, lean_object* v_targetParamIdx_826_, lean_object* v_fields_827_, lean_object* v_k_828_, uint8_t v_default_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_835_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1);
v___x_836_ = 0;
v___x_837_ = lean_st_mk_ref(v___x_835_);
v___x_838_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_824_, v_params_825_, v_targetParamIdx_826_, v_fields_827_, v_k_828_, v_default_829_, v___x_836_, v___x_837_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_847_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_st_ref_get(v___x_837_);
lean_dec(v___x_837_);
lean_dec(v___x_843_);
if (v_isShared_842_ == 0)
{
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_839_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_dec(v___x_837_);
return v___x_838_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_824_ = stack[0].m_obj;
lean_object* v_params_825_ = stack[1].m_obj;
lean_object* v_targetParamIdx_826_ = stack[2].m_obj;
lean_object* v_fields_827_ = stack[3].m_obj;
lean_object* v_k_828_ = stack[4].m_obj;
uint8_t v_default_829_ = stack[5].m_num;
lean_object* v_a_830_ = stack[6].m_obj;
lean_object* v_a_831_ = stack[7].m_obj;
lean_object* v_a_832_ = stack[8].m_obj;
lean_object* v_a_833_ = stack[9].m_obj;
lean_object* v_res_848_;
v_res_848_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_decls_824_, v_params_825_, v_targetParamIdx_826_, v_fields_827_, v_k_828_, v_default_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
stack->m_obj
 = v_res_848_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object* v_decls_849_, lean_object* v_params_850_, lean_object* v_targetParamIdx_851_, lean_object* v_fields_852_, lean_object* v_k_853_, lean_object* v_default_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
uint8_t v_default_boxed_860_; lean_object* v_res_861_; 
v_default_boxed_860_ = lean_unbox(v_default_854_);
v_res_861_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_decls_849_, v_params_850_, v_targetParamIdx_851_, v_fields_852_, v_k_853_, v_default_boxed_860_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_targetParamIdx_851_);
lean_dec_ref(v_params_850_);
return v_res_861_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object* v_args_862_, lean_object* v_targetParamIdx_863_, lean_object* v_fields_864_, uint8_t v_dependsOnTarget_865_){
_start:
{
if (v_dependsOnTarget_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_lower_871_; lean_object* v_upper_872_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_866_ = lean_unsigned_to_nat(0u);
lean_inc(v_targetParamIdx_863_);
lean_inc_ref(v_args_862_);
v___x_867_ = l_Array_toSubarray___redArg(v_args_862_, v___x_866_, v_targetParamIdx_863_);
v___x_868_ = l_Subarray_copy___redArg(v___x_867_);
v___x_869_ = l_Array_append___redArg(v___x_868_, v_fields_864_);
v___x_876_ = lean_array_get_size(v_args_862_);
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_targetParamIdx_863_, v___x_877_);
lean_dec(v_targetParamIdx_863_);
v___x_879_ = lean_nat_dec_le(v___x_878_, v___x_866_);
if (v___x_879_ == 0)
{
v_lower_871_ = v___x_878_;
v_upper_872_ = v___x_876_;
goto v___jp_870_;
}
else
{
lean_dec(v___x_878_);
v_lower_871_ = v___x_866_;
v_upper_872_ = v___x_876_;
goto v___jp_870_;
}
v___jp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = l_Array_toSubarray___redArg(v_args_862_, v_lower_871_, v_upper_872_);
v___x_874_ = l_Subarray_copy___redArg(v___x_873_);
v___x_875_ = l_Array_append___redArg(v___x_869_, v___x_874_);
lean_dec_ref(v___x_874_);
return v___x_875_;
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_lower_887_; lean_object* v_upper_888_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_add(v_targetParamIdx_863_, v___x_881_);
lean_dec(v_targetParamIdx_863_);
lean_inc(v___x_882_);
lean_inc_ref(v_args_862_);
v___x_883_ = l_Array_toSubarray___redArg(v_args_862_, v___x_880_, v___x_882_);
v___x_884_ = l_Subarray_copy___redArg(v___x_883_);
v___x_885_ = l_Array_append___redArg(v___x_884_, v_fields_864_);
v___x_892_ = lean_array_get_size(v_args_862_);
v___x_893_ = lean_nat_dec_le(v___x_882_, v___x_880_);
if (v___x_893_ == 0)
{
v_lower_887_ = v___x_882_;
v_upper_888_ = v___x_892_;
goto v___jp_886_;
}
else
{
lean_dec(v___x_882_);
v_lower_887_ = v___x_880_;
v_upper_888_ = v___x_892_;
goto v___jp_886_;
}
v___jp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = l_Array_toSubarray___redArg(v_args_862_, v_lower_887_, v_upper_888_);
v___x_890_ = l_Subarray_copy___redArg(v___x_889_);
v___x_891_ = l_Array_append___redArg(v___x_885_, v___x_890_);
lean_dec_ref(v___x_890_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_862_ = stack[0].m_obj;
lean_object* v_targetParamIdx_863_ = stack[1].m_obj;
lean_object* v_fields_864_ = stack[2].m_obj;
uint8_t v_dependsOnTarget_865_ = stack[3].m_num;
lean_object* v_res_894_;
v_res_894_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_862_, v_targetParamIdx_863_, v_fields_864_, v_dependsOnTarget_865_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object* v_args_895_, lean_object* v_targetParamIdx_896_, lean_object* v_fields_897_, lean_object* v_dependsOnTarget_898_){
_start:
{
uint8_t v_dependsOnTarget_boxed_899_; lean_object* v_res_900_; 
v_dependsOnTarget_boxed_899_ = lean_unbox(v_dependsOnTarget_898_);
v_res_900_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_895_, v_targetParamIdx_896_, v_fields_897_, v_dependsOnTarget_boxed_899_);
lean_dec_ref(v_fields_897_);
return v_res_900_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t v_sz_901_, size_t v_i_902_, lean_object* v_bs_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_lt(v_i_902_, v_sz_901_);
if (v___x_904_ == 0)
{
return v_bs_903_;
}
else
{
lean_object* v_v_905_; lean_object* v_fvarId_906_; lean_object* v___x_907_; lean_object* v_bs_x27_908_; lean_object* v___x_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v_v_905_ = lean_array_uget_borrowed(v_bs_903_, v_i_902_);
v_fvarId_906_ = lean_ctor_get(v_v_905_, 0);
lean_inc(v_fvarId_906_);
v___x_907_ = lean_unsigned_to_nat(0u);
v_bs_x27_908_ = lean_array_uset(v_bs_903_, v_i_902_, v___x_907_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v_fvarId_906_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_add(v_i_902_, v___x_910_);
v___x_912_ = lean_array_uset(v_bs_x27_908_, v_i_902_, v___x_909_);
v_i_902_ = v___x_911_;
v_bs_903_ = v___x_912_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_901_ = stack[0].m_num;
size_t v_i_902_ = stack[1].m_num;
lean_object* v_bs_903_ = stack[2].m_obj;
lean_object* v_res_914_;
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_901_, v_i_902_, v_bs_903_);
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_bs_917_){
_start:
{
size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_sz_boxed_918_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_919_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_boxed_918_, v_i_boxed_919_, v_bs_917_);
return v_res_920_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t v_sz_921_, size_t v_i_922_, lean_object* v_bs_923_){
_start:
{
uint8_t v___x_924_; 
v___x_924_ = lean_usize_dec_lt(v_i_922_, v_sz_921_);
if (v___x_924_ == 0)
{
return v_bs_923_;
}
else
{
lean_object* v_v_925_; lean_object* v_fvarId_926_; lean_object* v___x_927_; lean_object* v_bs_x27_928_; lean_object* v___x_929_; size_t v___x_930_; size_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_v_925_ = lean_array_uget_borrowed(v_bs_923_, v_i_922_);
v_fvarId_926_ = lean_ctor_get(v_v_925_, 0);
lean_inc(v_fvarId_926_);
v___x_927_ = lean_unsigned_to_nat(0u);
v_bs_x27_928_ = lean_array_uset(v_bs_923_, v_i_922_, v___x_927_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_fvarId_926_);
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_922_, v___x_930_);
v___x_932_ = lean_array_uset(v_bs_x27_928_, v_i_922_, v___x_929_);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_921_, v___x_931_, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_921_ = stack[0].m_num;
size_t v_i_922_ = stack[1].m_num;
lean_object* v_bs_923_ = stack[2].m_obj;
lean_object* v_res_934_;
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_921_, v_i_922_, v_bs_923_);
stack->m_obj
 = v_res_934_;
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
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object* v_params_941_, lean_object* v_targetParamIdx_942_, lean_object* v_fields_943_, uint8_t v_dependsOnTarget_944_){
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
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_941_ = stack[0].m_obj;
lean_object* v_targetParamIdx_942_ = stack[1].m_obj;
lean_object* v_fields_943_ = stack[2].m_obj;
uint8_t v_dependsOnTarget_944_ = stack[3].m_num;
lean_object* v_res_951_;
v_res_951_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_941_, v_targetParamIdx_942_, v_fields_943_, v_dependsOnTarget_944_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object* v_params_952_, lean_object* v_targetParamIdx_953_, lean_object* v_fields_954_, lean_object* v_dependsOnTarget_955_){
_start:
{
uint8_t v_dependsOnTarget_boxed_956_; lean_object* v_res_957_; 
v_dependsOnTarget_boxed_956_ = lean_unbox(v_dependsOnTarget_955_);
v_res_957_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_952_, v_targetParamIdx_953_, v_fields_954_, v_dependsOnTarget_boxed_956_);
return v_res_957_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object* v_fvarId_963_, lean_object* v_args_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_st_ref_get(v_a_966_);
v___x_974_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_973_, v_fvarId_963_);
lean_dec(v___x_973_);
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1157_; 
v_val_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1157_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1157_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; 
v___x_979_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_965_, v_fvarId_963_);
if (lean_obj_tag(v___x_979_) == 1)
{
lean_object* v_val_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_977_);
v_val_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_1152_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_val_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1152_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_paramIdx_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1150_; 
v_paramIdx_984_ = lean_ctor_get(v_val_980_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_val_980_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_val_980_, 1);
lean_dec(v_unused_1151_);
v___x_986_ = v_val_980_;
v_isShared_987_ = v_isSharedCheck_1150_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_paramIdx_984_);
lean_dec(v_val_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1150_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_box(0);
v___x_989_ = lean_array_get(v___x_988_, v_args_964_, v_paramIdx_984_);
if (lean_obj_tag(v___x_989_) == 1)
{
lean_object* v_fvarId_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1145_; 
lean_del_object(v___x_982_);
v_fvarId_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1145_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_fvarId_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1145_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; lean_object* v___x_995_; 
v___x_994_ = 0;
v___x_995_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_990_, v_a_967_, v_a_969_, v_a_971_);
lean_dec(v_fvarId_990_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1136_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1136_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1136_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
if (lean_obj_tag(v_a_996_) == 1)
{
lean_object* v_val_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1131_; 
v_val_1000_ = lean_ctor_get(v_a_996_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_a_996_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1002_ = v_a_996_;
v_isShared_1003_ = v_isSharedCheck_1131_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_val_1000_);
lean_dec(v_a_996_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1131_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_1000_);
v___x_1005_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_975_, v___x_1004_);
lean_dec(v___x_1004_);
lean_dec(v_val_975_);
if (lean_obj_tag(v___x_1005_) == 1)
{
lean_object* v_val_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1126_; 
v_val_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1126_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_val_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1126_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v_default_1010_; 
v_default_1010_ = lean_ctor_get_uint8(v_val_1006_, sizeof(void*)*1);
if (v_default_1010_ == 0)
{
if (lean_obj_tag(v_val_1000_) == 0)
{
lean_object* v_decl_1011_; uint8_t v_dependsOnDiscr_1012_; lean_object* v_val_1013_; lean_object* v_args_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1049_; 
lean_del_object(v___x_1002_);
lean_del_object(v___x_992_);
lean_del_object(v___x_986_);
v_decl_1011_ = lean_ctor_get(v_val_1006_, 0);
lean_inc_ref(v_decl_1011_);
v_dependsOnDiscr_1012_ = lean_ctor_get_uint8(v_val_1006_, sizeof(void*)*1 + 1);
lean_dec(v_val_1006_);
v_val_1013_ = lean_ctor_get(v_val_1000_, 0);
v_args_1014_ = lean_ctor_get(v_val_1000_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_val_1000_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1016_ = v_val_1000_;
v_isShared_1017_ = v_isSharedCheck_1049_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_args_1014_);
lean_inc(v_val_1013_);
lean_dec(v_val_1000_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1049_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___y_1019_; lean_object* v_numParams_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_numParams_1039_ = lean_ctor_get(v_val_1013_, 3);
lean_inc(v_numParams_1039_);
lean_dec_ref(v_val_1013_);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_array_get_size(v_args_1014_);
v___x_1042_ = lean_nat_dec_le(v_numParams_1039_, v___x_1040_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1044_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1041_);
lean_ctor_set(v___x_1016_, 0, v_numParams_1039_);
v___x_1044_ = v___x_1016_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_numParams_1039_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1041_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
v___y_1019_ = v___x_1044_;
goto v___jp_1018_;
}
}
else
{
lean_object* v___x_1047_; 
lean_dec(v_numParams_1039_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1041_);
lean_ctor_set(v___x_1016_, 0, v___x_1040_);
v___x_1047_ = v___x_1016_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1041_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v___y_1019_ = v___x_1047_;
goto v___jp_1018_;
}
}
v___jp_1018_:
{
lean_object* v_fvarId_1020_; lean_object* v_lower_1021_; lean_object* v_upper_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1038_; 
v_fvarId_1020_ = lean_ctor_get(v_decl_1011_, 0);
lean_inc(v_fvarId_1020_);
lean_dec_ref(v_decl_1011_);
v_lower_1021_ = lean_ctor_get(v___y_1019_, 0);
v_upper_1022_ = lean_ctor_get(v___y_1019_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___y_1019_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1024_ = v___y_1019_;
v_isShared_1025_ = v_isSharedCheck_1038_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_upper_1022_);
lean_inc(v_lower_1021_);
lean_dec(v___y_1019_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1038_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1026_ = l_Array_toSubarray___redArg(v_args_1014_, v_lower_1021_, v_upper_1022_);
v___x_1027_ = l_Subarray_copy___redArg(v___x_1026_);
v___x_1028_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_964_, v_paramIdx_984_, v___x_1027_, v_dependsOnDiscr_1012_);
lean_dec_ref(v___x_1027_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 3);
lean_ctor_set(v___x_1024_, 1, v___x_1028_);
lean_ctor_set(v___x_1024_, 0, v_fvarId_1020_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_fvarId_1020_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1030_);
v___x_1032_ = v___x_1008_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1032_);
v___x_1034_ = v___x_998_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
}
else
{
lean_object* v_decl_1050_; uint8_t v_dependsOnDiscr_1051_; lean_object* v_n_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1111_; 
v_decl_1050_ = lean_ctor_get(v_val_1006_, 0);
lean_inc_ref(v_decl_1050_);
v_dependsOnDiscr_1051_ = lean_ctor_get_uint8(v_val_1006_, sizeof(void*)*1 + 1);
lean_dec(v_val_1006_);
v_n_1052_ = lean_ctor_get(v_val_1000_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_val_1000_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1054_ = v_val_1000_;
v_isShared_1055_ = v_isSharedCheck_1111_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_n_1052_);
lean_dec(v_val_1000_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1111_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_zero_1056_; uint8_t v_isZero_1057_; 
v_zero_1056_ = lean_unsigned_to_nat(0u);
v_isZero_1057_ = lean_nat_dec_eq(v_n_1052_, v_zero_1056_);
if (v_isZero_1057_ == 1)
{
lean_object* v_fvarId_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_del_object(v___x_1054_);
lean_dec(v_n_1052_);
lean_del_object(v___x_1002_);
lean_del_object(v___x_992_);
v_fvarId_1058_ = lean_ctor_get(v_decl_1050_, 0);
lean_inc(v_fvarId_1058_);
lean_dec_ref(v_decl_1050_);
v___x_1059_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1060_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_964_, v_paramIdx_984_, v___x_1059_, v_dependsOnDiscr_1051_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 3);
lean_ctor_set(v___x_986_, 1, v___x_1060_);
lean_ctor_set(v___x_986_, 0, v_fvarId_1058_);
v___x_1062_ = v___x_986_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_fvarId_1058_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1064_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1062_);
v___x_1064_ = v___x_1008_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1064_);
v___x_1066_ = v___x_998_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_one_1070_; lean_object* v_n_1071_; lean_object* v___x_1073_; 
lean_del_object(v___x_998_);
v_one_1070_ = lean_unsigned_to_nat(1u);
v_n_1071_ = lean_nat_sub(v_n_1052_, v_one_1070_);
lean_dec(v_n_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 0);
lean_ctor_set(v___x_1054_, 0, v_n_1071_);
v___x_1073_ = v___x_1054_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_n_1071_);
v___x_1073_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1073_);
v___x_1075_ = v___x_1002_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
v___x_1077_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_994_, v___x_1075_, v___x_1076_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1100_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1100_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1100_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v_fvarId_1082_; lean_object* v_fvarId_1083_; lean_object* v___x_1085_; 
v_fvarId_1082_ = lean_ctor_get(v_decl_1050_, 0);
lean_inc(v_fvarId_1082_);
lean_dec_ref(v_decl_1050_);
v_fvarId_1083_ = lean_ctor_get(v_a_1078_, 0);
lean_inc(v_fvarId_1083_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_fvarId_1083_);
v___x_1085_ = v___x_992_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_fvarId_1083_);
v___x_1085_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1086_ = lean_mk_empty_array_with_capacity(v_one_1070_);
v___x_1087_ = lean_array_push(v___x_1086_, v___x_1085_);
v___x_1088_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_964_, v_paramIdx_984_, v___x_1087_, v_dependsOnDiscr_1051_);
lean_dec_ref(v___x_1087_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 3);
lean_ctor_set(v___x_986_, 1, v___x_1088_);
lean_ctor_set(v___x_986_, 0, v_fvarId_1082_);
v___x_1090_ = v___x_986_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_fvarId_1082_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_a_1078_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1091_);
v___x_1093_ = v___x_1008_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1093_);
v___x_1095_ = v___x_1080_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_decl_1050_);
lean_del_object(v___x_1008_);
lean_del_object(v___x_992_);
lean_del_object(v___x_986_);
lean_dec(v_paramIdx_984_);
lean_dec_ref(v_args_964_);
v_a_1101_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1077_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1077_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
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
lean_object* v_decl_1112_; uint8_t v_dependsOnDiscr_1113_; lean_object* v_fvarId_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_del_object(v___x_1002_);
lean_dec(v_val_1000_);
lean_del_object(v___x_992_);
v_decl_1112_ = lean_ctor_get(v_val_1006_, 0);
lean_inc_ref(v_decl_1112_);
v_dependsOnDiscr_1113_ = lean_ctor_get_uint8(v_val_1006_, sizeof(void*)*1 + 1);
lean_dec(v_val_1006_);
v_fvarId_1114_ = lean_ctor_get(v_decl_1112_, 0);
lean_inc(v_fvarId_1114_);
lean_dec_ref(v_decl_1112_);
v___x_1115_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1116_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_964_, v_paramIdx_984_, v___x_1115_, v_dependsOnDiscr_1113_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 3);
lean_ctor_set(v___x_986_, 1, v___x_1116_);
lean_ctor_set(v___x_986_, 0, v_fvarId_1114_);
v___x_1118_ = v___x_986_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_fvarId_1114_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1118_);
v___x_1120_ = v___x_1008_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1120_);
v___x_1122_ = v___x_998_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec(v___x_1005_);
lean_del_object(v___x_1002_);
lean_dec(v_val_1000_);
lean_del_object(v___x_992_);
lean_del_object(v___x_986_);
lean_dec(v_paramIdx_984_);
lean_dec_ref(v_args_964_);
v___x_1127_ = lean_box(0);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1127_);
v___x_1129_ = v___x_998_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec(v_a_996_);
lean_del_object(v___x_992_);
lean_del_object(v___x_986_);
lean_dec(v_paramIdx_984_);
lean_dec(v_val_975_);
lean_dec_ref(v_args_964_);
v___x_1132_ = lean_box(0);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1132_);
v___x_1134_ = v___x_998_;
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
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_del_object(v___x_992_);
lean_del_object(v___x_986_);
lean_dec(v_paramIdx_984_);
lean_dec(v_val_975_);
lean_dec_ref(v_args_964_);
v_a_1137_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_995_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_995_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec(v___x_989_);
lean_del_object(v___x_986_);
lean_dec(v_paramIdx_984_);
lean_dec(v_val_975_);
lean_dec_ref(v_args_964_);
v___x_1146_ = lean_box(0);
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 0);
lean_ctor_set(v___x_982_, 0, v___x_1146_);
v___x_1148_ = v___x_982_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
lean_dec(v___x_979_);
lean_dec(v_val_975_);
lean_dec_ref(v_args_964_);
v___x_1153_ = lean_box(0);
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 0);
lean_ctor_set(v___x_977_, 0, v___x_1153_);
v___x_1155_ = v___x_977_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v___x_974_);
lean_dec_ref(v_args_964_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_963_ = stack[0].m_obj;
lean_object* v_args_964_ = stack[1].m_obj;
lean_object* v_a_965_ = stack[2].m_obj;
lean_object* v_a_966_ = stack[3].m_obj;
lean_object* v_a_967_ = stack[4].m_obj;
lean_object* v_a_968_ = stack[5].m_obj;
lean_object* v_a_969_ = stack[6].m_obj;
lean_object* v_a_970_ = stack[7].m_obj;
lean_object* v_a_971_ = stack[8].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_963_, v_args_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object* v_fvarId_1161_, lean_object* v_args_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1161_, v_args_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec(v_fvarId_1161_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object* v___x_1172_, lean_object* v_init_1173_, lean_object* v_x_1174_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v_k_1175_; lean_object* v_l_1176_; lean_object* v_r_1177_; lean_object* v___x_1178_; 
v_k_1175_ = lean_ctor_get(v_x_1174_, 1);
v_l_1176_ = lean_ctor_get(v_x_1174_, 3);
v_r_1177_ = lean_ctor_get(v_x_1174_, 4);
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1172_, v_init_1173_, v_l_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
return v___x_1178_;
}
else
{
uint8_t v___x_1179_; 
lean_dec_ref_known(v___x_1178_, 1);
v___x_1179_ = l_Lean_NameSet_contains(v___x_1172_, v_k_1175_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2));
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; 
v___x_1181_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v_init_1173_ = v___x_1181_;
v_x_1174_ = v_r_1177_;
goto _start;
}
}
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_init_1173_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object* v___x_1184_, lean_object* v_init_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1184_, v_init_1185_, v_x_1186_);
lean_dec(v_x_1186_);
lean_dec(v___x_1184_);
return v_res_1187_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object* v___x_1188_, lean_object* v_a_1189_, lean_object* v_init_1190_, lean_object* v_x_1191_){
_start:
{
lean_object* v_d_1194_; 
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_k_1197_; lean_object* v_l_1198_; lean_object* v_r_1199_; lean_object* v___x_1200_; lean_object* v_a_1201_; 
v_k_1197_ = lean_ctor_get(v_x_1191_, 1);
lean_inc(v_k_1197_);
v_l_1198_ = lean_ctor_get(v_x_1191_, 3);
lean_inc(v_l_1198_);
v_r_1199_ = lean_ctor_get(v_x_1191_, 4);
lean_inc(v_r_1199_);
lean_dec_ref_known(v_x_1191_, 5);
lean_inc_ref(v_a_1189_);
v___x_1200_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1188_, v_a_1189_, v_init_1190_, v_l_1198_);
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
if (lean_obj_tag(v_a_1201_) == 0)
{
lean_object* v_a_1202_; 
lean_inc_ref(v_a_1201_);
lean_dec_ref(v___x_1200_);
lean_dec(v_r_1199_);
lean_dec(v_k_1197_);
lean_dec_ref(v_a_1189_);
v_a_1202_ = lean_ctor_get(v_a_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v_a_1201_, 1);
v_d_1194_ = v_a_1202_;
goto v___jp_1193_;
}
else
{
lean_object* v_a_1203_; uint8_t v___x_1204_; 
v_a_1203_ = lean_ctor_get(v_a_1201_, 0);
v___x_1204_ = l_Lean_NameSet_contains(v___x_1188_, v_k_1197_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_inc(v_a_1203_);
lean_dec_ref(v___x_1200_);
lean_inc_ref(v_a_1189_);
v___x_1205_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1197_, v_a_1189_, v_a_1203_);
v_init_1190_ = v___x_1205_;
v_x_1191_ = v_r_1199_;
goto _start;
}
else
{
lean_object* v_a_1207_; 
lean_dec(v_k_1197_);
v_a_1207_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1200_);
if (lean_obj_tag(v_a_1207_) == 0)
{
lean_object* v_a_1208_; 
lean_dec(v_r_1199_);
lean_dec_ref(v_a_1189_);
v_a_1208_ = lean_ctor_get(v_a_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v_a_1207_, 1);
v_d_1194_ = v_a_1208_;
goto v___jp_1193_;
}
else
{
lean_object* v_a_1209_; 
v_a_1209_ = lean_ctor_get(v_a_1207_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v_a_1207_, 1);
v_init_1190_ = v_a_1209_;
v_x_1191_ = v_r_1199_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_dec_ref(v_a_1189_);
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_init_1190_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
v___jp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_d_1194_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1188_ = stack[0].m_obj;
lean_object* v_a_1189_ = stack[1].m_obj;
lean_object* v_init_1190_ = stack[2].m_obj;
lean_object* v_x_1191_ = stack[3].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1188_, v_a_1189_, v_init_1190_, v_x_1191_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object* v___x_1214_, lean_object* v_a_1215_, lean_object* v_init_1216_, lean_object* v_x_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1214_, v_a_1215_, v_init_1216_, v_x_1217_);
lean_dec(v___x_1214_);
return v_res_1219_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object* v_discr_1225_, lean_object* v___x_1226_, lean_object* v_val_1227_, lean_object* v_fst_1228_, lean_object* v_params_1229_, lean_object* v_snd_1230_, lean_object* v_as_1231_, size_t v_sz_1232_, size_t v_i_1233_, lean_object* v_b_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_a_1244_; uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_lt(v_i_1233_, v_sz_1232_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_b_1234_);
return v___x_1249_;
}
else
{
lean_object* v_snd_1250_; lean_object* v_fst_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1409_; 
v_snd_1250_ = lean_ctor_get(v_b_1234_, 1);
v_fst_1251_ = lean_ctor_get(v_b_1234_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_b_1234_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1253_ = v_b_1234_;
v_isShared_1254_ = v_isSharedCheck_1409_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1251_);
lean_dec(v_b_1234_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1409_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_fst_1255_; lean_object* v_snd_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1408_; 
v_fst_1255_ = lean_ctor_get(v_snd_1250_, 0);
v_snd_1256_ = lean_ctor_get(v_snd_1250_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_snd_1250_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1258_ = v_snd_1250_;
v_isShared_1259_ = v_isSharedCheck_1408_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_snd_1256_);
lean_inc(v_fst_1255_);
lean_dec(v_snd_1250_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1408_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
uint8_t v___x_1260_; lean_object* v_a_1261_; uint8_t v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v_a_1268_; 
v___x_1260_ = 0;
v_a_1261_ = lean_array_uget_borrowed(v_as_1231_, v_i_1233_);
if (lean_obj_tag(v_a_1261_) == 0)
{
lean_object* v_ctorName_1280_; lean_object* v_params_1281_; lean_object* v_code_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; 
lean_del_object(v___x_1258_);
lean_del_object(v___x_1253_);
v_ctorName_1280_ = lean_ctor_get(v_a_1261_, 0);
v_params_1281_ = lean_ctor_get(v_a_1261_, 1);
v_code_1282_ = lean_ctor_get(v_a_1261_, 2);
v___x_1283_ = 0;
lean_inc_ref(v_params_1281_);
lean_inc(v_ctorName_1280_);
lean_inc(v_discr_1225_);
v___x_1284_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1225_, v_ctorName_1280_, v_params_1281_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
lean_inc_ref(v_code_1282_);
v___x_1286_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1282_, v___y_1235_, v___y_1236_, v_a_1285_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v_a_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = l_Lean_NameSet_contains(v___x_1226_, v_ctorName_1280_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_inc_ref(v_a_1261_);
v___x_1289_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1261_, v_a_1287_);
v___x_1290_ = lean_array_push(v_snd_1256_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_fst_1255_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_fst_1251_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v_a_1244_ = v___x_1292_;
goto v___jp_1243_;
}
else
{
lean_object* v_paramIdx_1293_; lean_object* v___x_1294_; 
v_paramIdx_1293_ = lean_ctor_get(v_val_1227_, 0);
lean_inc(v_a_1287_);
lean_inc_ref(v_params_1281_);
lean_inc_ref(v_fst_1228_);
v___x_1294_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1228_, v_params_1229_, v_paramIdx_1293_, v_params_1281_, v_a_1287_, v___x_1283_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v_decl_1296_; uint8_t v_dependsOnDiscr_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v_decl_1296_ = lean_ctor_get(v_a_1295_, 0);
lean_inc_ref_n(v_decl_1296_, 2);
v_dependsOnDiscr_1297_ = lean_ctor_get_uint8(v_a_1295_, sizeof(void*)*1 + 1);
v___x_1298_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_decl_1296_);
v___x_1299_ = lean_array_push(v_fst_1255_, v___x_1298_);
lean_inc(v_ctorName_1280_);
v___x_1300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_ctorName_1280_, v_a_1295_, v_fst_1251_);
lean_inc_ref(v_params_1281_);
lean_inc(v_paramIdx_1293_);
lean_inc_ref(v_params_1229_);
v___x_1301_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1229_, v_paramIdx_1293_, v_params_1281_, v_dependsOnDiscr_1297_);
v___x_1302_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1260_, v_a_1287_, v___y_1239_);
lean_dec(v_a_1287_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_fvarId_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec_ref_known(v___x_1302_, 1);
v_fvarId_1303_ = lean_ctor_get(v_decl_1296_, 0);
lean_inc(v_fvarId_1303_);
lean_dec_ref(v_decl_1296_);
v___x_1304_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_fvarId_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1301_);
lean_inc_ref(v_a_1261_);
v___x_1305_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1261_, v___x_1304_);
v___x_1306_ = lean_array_push(v_snd_1256_, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1299_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1300_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v_a_1244_ = v___x_1308_;
goto v___jp_1243_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v___x_1301_);
lean_dec(v___x_1300_);
lean_dec_ref(v___x_1299_);
lean_dec_ref(v_decl_1296_);
lean_dec(v_snd_1256_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1309_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1302_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1302_);
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
lean_dec(v_a_1287_);
lean_dec(v_snd_1256_);
lean_dec(v_fst_1255_);
lean_dec(v_fst_1251_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1317_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1294_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1294_);
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
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_snd_1256_);
lean_dec(v_fst_1255_);
lean_dec(v_fst_1251_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1325_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1286_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1286_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_snd_1256_);
lean_dec(v_fst_1255_);
lean_dec(v_fst_1251_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1333_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1284_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1284_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_code_1341_; lean_object* v___x_1342_; 
v_code_1341_ = lean_ctor_get(v_a_1261_, 0);
lean_inc_ref(v_code_1341_);
v___x_1342_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1341_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1349_; lean_object* v___y_1351_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_a_1399_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1349_ = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(v_snd_1230_);
v___x_1397_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v___x_1398_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1349_, v___x_1397_, v___x_1226_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___y_1351_ = v_a_1399_;
goto v___jp_1350_;
v___jp_1344_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_inc_ref(v_a_1261_);
v___x_1345_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1261_, v_a_1343_);
v___x_1346_ = lean_array_push(v_snd_1256_, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_fst_1255_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_fst_1251_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v_a_1244_ = v___x_1348_;
goto v___jp_1243_;
}
v___jp_1350_:
{
lean_object* v_fst_1352_; 
v_fst_1352_ = lean_ctor_get(v___y_1351_, 0);
lean_inc(v_fst_1352_);
lean_dec_ref(v___y_1351_);
if (lean_obj_tag(v_fst_1352_) == 0)
{
lean_dec(v___x_1349_);
lean_del_object(v___x_1258_);
lean_del_object(v___x_1253_);
goto v___jp_1344_;
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1396_; 
v_val_1353_ = lean_ctor_get(v_fst_1352_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_fst_1352_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1355_ = v_fst_1352_;
v_isShared_1356_ = v_isSharedCheck_1396_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_val_1353_);
lean_dec(v_fst_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1396_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_unbox(v_val_1353_);
lean_dec(v_val_1353_);
if (v___x_1357_ == 0)
{
lean_del_object(v___x_1355_);
lean_dec(v___x_1349_);
lean_del_object(v___x_1258_);
lean_del_object(v___x_1253_);
goto v___jp_1344_;
}
else
{
lean_object* v_paramIdx_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_paramIdx_1358_ = lean_ctor_get(v_val_1227_, 0);
v___x_1359_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
lean_inc(v_a_1343_);
lean_inc_ref(v_fst_1228_);
v___x_1360_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1228_, v_params_1229_, v_paramIdx_1358_, v___x_1359_, v_a_1343_, v___x_1248_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_decl_1362_; uint8_t v_dependsOnDiscr_1363_; lean_object* v___x_1365_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_decl_1362_ = lean_ctor_get(v_a_1361_, 0);
lean_inc_ref_n(v_decl_1362_, 2);
v_dependsOnDiscr_1363_ = lean_ctor_get_uint8(v_a_1361_, sizeof(void*)*1 + 1);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 2);
lean_ctor_set(v___x_1355_, 0, v_decl_1362_);
v___x_1365_ = v___x_1355_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_decl_1362_);
v___x_1365_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_array_push(v_fst_1255_, v___x_1365_);
v___x_1367_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1260_, v_a_1343_, v___y_1239_);
lean_dec(v_a_1343_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
lean_dec_ref_known(v___x_1367_, 1);
lean_inc(v___x_1226_);
v___x_1368_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1349_, v_a_1361_, v_fst_1251_, v___x_1226_);
lean_dec(v___x_1349_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v_a_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v_a_1370_ = lean_ctor_get(v_a_1369_, 0);
lean_inc(v_a_1370_);
lean_dec(v_a_1369_);
lean_inc(v_paramIdx_1358_);
v___y_1263_ = v_dependsOnDiscr_1363_;
v___y_1264_ = v___x_1359_;
v___y_1265_ = v___x_1366_;
v___y_1266_ = v_decl_1362_;
v___y_1267_ = v_paramIdx_1358_;
v_a_1268_ = v_a_1370_;
goto v___jp_1262_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v___x_1366_);
lean_dec_ref(v_decl_1362_);
lean_del_object(v___x_1258_);
lean_dec(v_snd_1256_);
lean_del_object(v___x_1253_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1371_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1368_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1368_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v___x_1366_);
lean_dec_ref(v_decl_1362_);
lean_dec(v_a_1361_);
lean_dec(v___x_1349_);
lean_del_object(v___x_1258_);
lean_dec(v_snd_1256_);
lean_del_object(v___x_1253_);
lean_dec(v_fst_1251_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1379_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1367_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1367_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_del_object(v___x_1355_);
lean_dec(v___x_1349_);
lean_dec(v_a_1343_);
lean_del_object(v___x_1258_);
lean_dec(v_snd_1256_);
lean_dec(v_fst_1255_);
lean_del_object(v___x_1253_);
lean_dec(v_fst_1251_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1388_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1360_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1360_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
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
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_del_object(v___x_1258_);
lean_dec(v_snd_1256_);
lean_dec(v_fst_1255_);
lean_del_object(v___x_1253_);
lean_dec(v_fst_1251_);
lean_dec_ref(v_params_1229_);
lean_dec_ref(v_fst_1228_);
lean_dec_ref(v_val_1227_);
lean_dec(v___x_1226_);
lean_dec(v_discr_1225_);
v_a_1400_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1342_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1342_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
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
v___jp_1262_:
{
lean_object* v_fvarId_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v_fvarId_1269_ = lean_ctor_get(v___y_1266_, 0);
lean_inc(v_fvarId_1269_);
lean_dec_ref(v___y_1266_);
lean_inc_ref(v_params_1229_);
v___x_1270_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1229_, v___y_1267_, v___y_1264_, v___y_1263_);
v___x_1271_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_fvarId_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
lean_inc(v_a_1261_);
v___x_1272_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1261_, v___x_1271_);
v___x_1273_ = lean_array_push(v_snd_1256_, v___x_1272_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1273_);
lean_ctor_set(v___x_1258_, 0, v___y_1265_);
v___x_1275_ = v___x_1258_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___y_1265_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___x_1275_);
lean_ctor_set(v___x_1253_, 0, v_a_1268_);
v___x_1277_ = v___x_1253_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
v_a_1244_ = v___x_1277_;
goto v___jp_1243_;
}
}
}
}
}
}
v___jp_1243_:
{
size_t v___x_1245_; size_t v___x_1246_; 
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_i_1233_, v___x_1245_);
v_i_1233_ = v___x_1246_;
v_b_1234_ = v_a_1244_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_1225_ = stack[0].m_obj;
lean_object* v___x_1226_ = stack[1].m_obj;
lean_object* v_val_1227_ = stack[2].m_obj;
lean_object* v_fst_1228_ = stack[3].m_obj;
lean_object* v_params_1229_ = stack[4].m_obj;
lean_object* v_snd_1230_ = stack[5].m_obj;
lean_object* v_as_1231_ = stack[6].m_obj;
size_t v_sz_1232_ = stack[7].m_num;
size_t v_i_1233_ = stack[8].m_num;
lean_object* v_b_1234_ = stack[9].m_obj;
lean_object* v___y_1235_ = stack[10].m_obj;
lean_object* v___y_1236_ = stack[11].m_obj;
lean_object* v___y_1237_ = stack[12].m_obj;
lean_object* v___y_1238_ = stack[13].m_obj;
lean_object* v___y_1239_ = stack[14].m_obj;
lean_object* v___y_1240_ = stack[15].m_obj;
lean_object* v___y_1241_ = stack[16].m_obj;
lean_object* v_res_1410_;
v_res_1410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1225_, v___x_1226_, v_val_1227_, v_fst_1228_, v_params_1229_, v_snd_1230_, v_as_1231_, v_sz_1232_, v_i_1233_, v_b_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
stack->m_obj
 = v_res_1410_;
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object* v_decl_1411_, lean_object* v_k_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_fvarId_1421_; lean_object* v_params_1422_; lean_object* v_type_1423_; lean_object* v_value_1424_; lean_object* v___x_1425_; 
v_fvarId_1421_ = lean_ctor_get(v_decl_1411_, 0);
v_params_1422_ = lean_ctor_get(v_decl_1411_, 2);
lean_inc_ref(v_params_1422_);
v_type_1423_ = lean_ctor_get(v_decl_1411_, 3);
lean_inc_ref(v_type_1423_);
v_value_1424_ = lean_ctor_get(v_decl_1411_, 4);
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_1413_, v_fvarId_1421_);
if (lean_obj_tag(v___x_1425_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1502_; 
v_val_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1502_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_val_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1502_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_ctorNames_1430_; 
v_ctorNames_1430_ = lean_ctor_get(v_val_1426_, 1);
lean_inc(v_ctorNames_1430_);
if (lean_obj_tag(v_ctorNames_1430_) == 0)
{
lean_object* v___x_1431_; lean_object* v_snd_1432_; lean_object* v_fst_1433_; lean_object* v_typeName_1434_; lean_object* v_resultType_1435_; lean_object* v_discr_1436_; lean_object* v_alts_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; size_t v_sz_1440_; size_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1431_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_value_1424_);
v_snd_1432_ = lean_ctor_get(v___x_1431_, 1);
lean_inc(v_snd_1432_);
v_fst_1433_ = lean_ctor_get(v___x_1431_, 0);
lean_inc_n(v_fst_1433_, 2);
lean_dec_ref(v___x_1431_);
v_typeName_1434_ = lean_ctor_get(v_snd_1432_, 0);
lean_inc(v_typeName_1434_);
v_resultType_1435_ = lean_ctor_get(v_snd_1432_, 1);
lean_inc_ref(v_resultType_1435_);
v_discr_1436_ = lean_ctor_get(v_snd_1432_, 2);
lean_inc_n(v_discr_1436_, 2);
v_alts_1437_ = lean_ctor_get(v_snd_1432_, 3);
lean_inc_ref(v_alts_1437_);
v___x_1438_ = 0;
v___x_1439_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1));
v_sz_1440_ = lean_array_size(v_alts_1437_);
v___x_1441_ = ((size_t)0ULL);
lean_inc_ref(v_params_1422_);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1436_, v_ctorNames_1430_, v_val_1426_, v_fst_1433_, v_params_1422_, v_snd_1432_, v_alts_1437_, v_sz_1440_, v___x_1441_, v___x_1439_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec_ref(v_alts_1437_);
lean_dec(v_snd_1432_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v_snd_1444_; lean_object* v_fst_1445_; lean_object* v_fst_1446_; lean_object* v_snd_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1491_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v_snd_1444_ = lean_ctor_get(v_a_1443_, 1);
lean_inc(v_snd_1444_);
v_fst_1445_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_fst_1445_);
lean_dec(v_a_1443_);
v_fst_1446_ = lean_ctor_get(v_snd_1444_, 0);
v_snd_1447_ = lean_ctor_get(v_snd_1444_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_snd_1444_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1449_ = v_snd_1444_;
v_isShared_1450_ = v_isSharedCheck_1491_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_snd_1447_);
lean_inc(v_fst_1446_);
lean_dec(v_snd_1444_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1491_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1451_ = lean_st_ref_take(v_a_1414_);
lean_inc(v_fvarId_1421_);
v___x_1452_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1421_, v_fst_1445_, v___x_1451_);
v___x_1453_ = lean_st_ref_put(v_a_1414_, v___x_1452_);
v___x_1454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1454_, 0, v_typeName_1434_);
lean_ctor_set(v___x_1454_, 1, v_resultType_1435_);
lean_ctor_set(v___x_1454_, 2, v_discr_1436_);
lean_ctor_set(v___x_1454_, 3, v_snd_1447_);
v___x_1455_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
v___x_1456_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_1433_, v___x_1455_);
lean_dec(v_fst_1433_);
v___x_1457_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1438_, v_decl_1411_, v_type_1423_, v_params_1422_, v___x_1456_, v_a_1417_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1474_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1474_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1474_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 2);
lean_ctor_set(v___x_1449_, 1, v_a_1460_);
lean_ctor_set(v___x_1449_, 0, v_a_1458_);
v___x_1465_ = v___x_1449_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1458_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_fst_1446_, v___x_1465_);
lean_dec(v_fst_1446_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1466_);
v___x_1468_ = v___x_1428_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1468_);
v___x_1470_ = v___x_1462_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1458_);
lean_del_object(v___x_1449_);
lean_dec(v_fst_1446_);
lean_del_object(v___x_1428_);
v_a_1475_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1459_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1459_);
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
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_del_object(v___x_1449_);
lean_dec(v_fst_1446_);
lean_del_object(v___x_1428_);
lean_dec_ref(v_k_1412_);
v_a_1483_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1457_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1457_);
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
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_discr_1436_);
lean_dec_ref(v_resultType_1435_);
lean_dec(v_typeName_1434_);
lean_dec(v_fst_1433_);
lean_del_object(v___x_1428_);
lean_dec_ref(v_type_1423_);
lean_dec_ref(v_params_1422_);
lean_dec_ref(v_k_1412_);
lean_dec_ref(v_decl_1411_);
v_a_1492_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1442_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1442_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_del_object(v___x_1428_);
lean_dec(v_val_1426_);
lean_dec_ref(v_type_1423_);
lean_dec_ref(v_params_1422_);
lean_dec_ref(v_k_1412_);
lean_dec_ref(v_decl_1411_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec(v___x_1425_);
lean_dec_ref(v_type_1423_);
lean_dec_ref(v_params_1422_);
lean_dec_ref(v_k_1412_);
lean_dec_ref(v_decl_1411_);
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1411_ = stack[0].m_obj;
lean_object* v_k_1412_ = stack[1].m_obj;
lean_object* v_a_1413_ = stack[2].m_obj;
lean_object* v_a_1414_ = stack[3].m_obj;
lean_object* v_a_1415_ = stack[4].m_obj;
lean_object* v_a_1416_ = stack[5].m_obj;
lean_object* v_a_1417_ = stack[6].m_obj;
lean_object* v_a_1418_ = stack[7].m_obj;
lean_object* v_a_1419_ = stack[8].m_obj;
lean_object* v_res_1505_;
v_res_1505_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1411_, v_k_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
stack->m_obj
 = v_res_1505_;
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object* v_code_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
switch(lean_obj_tag(v_code_1506_))
{
case 0:
{
lean_object* v_decl_1515_; lean_object* v_k_1516_; lean_object* v___x_1517_; 
v_decl_1515_ = lean_ctor_get(v_code_1506_, 0);
v_k_1516_ = lean_ctor_get(v_code_1506_, 1);
lean_inc_ref(v_k_1516_);
v___x_1517_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1516_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1554_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1554_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1554_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
size_t v___x_1522_; size_t v___x_1523_; uint8_t v___x_1524_; 
v___x_1522_ = lean_ptr_addr(v_k_1516_);
v___x_1523_ = lean_ptr_addr(v_a_1518_);
v___x_1524_ = lean_usize_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1534_; 
lean_inc_ref(v_decl_1515_);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_code_1506_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; lean_object* v_unused_1536_; 
v_unused_1535_ = lean_ctor_get(v_code_1506_, 1);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_code_1506_, 0);
lean_dec(v_unused_1536_);
v___x_1526_ = v_code_1506_;
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v_code_1506_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1534_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v_a_1518_);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_decl_1515_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_a_1518_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1529_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
size_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = lean_ptr_addr(v_decl_1515_);
v___x_1538_ = lean_usize_dec_eq(v___x_1537_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1548_; 
lean_inc_ref(v_decl_1515_);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_code_1506_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; 
v_unused_1549_ = lean_ctor_get(v_code_1506_, 1);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_code_1506_, 0);
lean_dec(v_unused_1550_);
v___x_1540_ = v_code_1506_;
v_isShared_1541_ = v_isSharedCheck_1548_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_code_1506_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1548_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v_a_1518_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_decl_1515_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_a_1518_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1543_);
v___x_1545_ = v___x_1520_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v___x_1552_; 
lean_dec(v_a_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v_code_1506_);
v___x_1552_ = v___x_1520_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_code_1506_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1506_, 2);
return v___x_1517_;
}
}
case 1:
{
lean_object* v_decl_1555_; lean_object* v_k_1556_; lean_object* v_params_1557_; lean_object* v_type_1558_; lean_object* v_value_1559_; uint8_t v___x_1560_; lean_object* v___x_1561_; 
v_decl_1555_ = lean_ctor_get(v_code_1506_, 0);
v_k_1556_ = lean_ctor_get(v_code_1506_, 1);
v_params_1557_ = lean_ctor_get(v_decl_1555_, 2);
v_type_1558_ = lean_ctor_get(v_decl_1555_, 3);
v_value_1559_ = lean_ctor_get(v_decl_1555_, 4);
v___x_1560_ = 0;
lean_inc_ref(v_value_1559_);
v___x_1561_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1559_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
lean_inc_ref(v_params_1557_);
lean_inc_ref(v_type_1558_);
lean_inc_ref(v_decl_1555_);
v___x_1563_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1560_, v_decl_1555_, v_type_1558_, v_params_1557_, v_a_1562_, v_a_1511_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
lean_inc_ref(v_k_1556_);
v___x_1565_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1556_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1603_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1603_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1603_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
size_t v___x_1570_; size_t v___x_1571_; uint8_t v___x_1572_; 
v___x_1570_ = lean_ptr_addr(v_k_1556_);
v___x_1571_ = lean_ptr_addr(v_a_1566_);
v___x_1572_ = lean_usize_dec_eq(v___x_1570_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1582_; 
v_isSharedCheck_1582_ = !lean_is_exclusive(v_code_1506_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1583_ = lean_ctor_get(v_code_1506_, 1);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_code_1506_, 0);
lean_dec(v_unused_1584_);
v___x_1574_ = v_code_1506_;
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v_code_1506_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v_a_1566_);
lean_ctor_set(v___x_1574_, 0, v_a_1564_);
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1564_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_a_1566_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1577_);
v___x_1579_ = v___x_1568_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
size_t v___x_1585_; size_t v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_ptr_addr(v_decl_1555_);
v___x_1586_ = lean_ptr_addr(v_a_1564_);
v___x_1587_ = lean_usize_dec_eq(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v_code_1506_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1598_ = lean_ctor_get(v_code_1506_, 1);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_code_1506_, 0);
lean_dec(v_unused_1599_);
v___x_1589_ = v_code_1506_;
v_isShared_1590_ = v_isSharedCheck_1597_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v_code_1506_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1597_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v_a_1566_);
lean_ctor_set(v___x_1589_, 0, v_a_1564_);
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1564_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1566_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1592_);
v___x_1594_ = v___x_1568_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v___x_1601_; 
lean_dec(v_a_1566_);
lean_dec(v_a_1564_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_code_1506_);
v___x_1601_ = v___x_1568_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_code_1506_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
else
{
lean_dec(v_a_1564_);
lean_dec_ref_known(v_code_1506_, 2);
return v___x_1565_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref_known(v_code_1506_, 2);
v_a_1604_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1563_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1563_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1506_, 2);
return v___x_1561_;
}
}
case 2:
{
lean_object* v_decl_1612_; lean_object* v_k_1613_; lean_object* v___x_1614_; 
v_decl_1612_ = lean_ctor_get(v_code_1506_, 0);
v_k_1613_ = lean_ctor_get(v_code_1506_, 1);
lean_inc_ref(v_k_1613_);
lean_inc_ref(v_decl_1612_);
v___x_1614_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1612_, v_k_1613_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1678_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1678_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1678_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
if (lean_obj_tag(v_a_1615_) == 1)
{
lean_object* v_val_1619_; lean_object* v___x_1621_; 
lean_dec_ref_known(v_code_1506_, 2);
v_val_1619_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v_a_1615_, 1);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v_val_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_val_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v_params_1623_; lean_object* v_type_1624_; lean_object* v_value_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; 
lean_del_object(v___x_1617_);
lean_dec(v_a_1615_);
v_params_1623_ = lean_ctor_get(v_decl_1612_, 2);
v_type_1624_ = lean_ctor_get(v_decl_1612_, 3);
v_value_1625_ = lean_ctor_get(v_decl_1612_, 4);
v___x_1626_ = 0;
lean_inc_ref(v_value_1625_);
v___x_1627_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1625_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
lean_inc_ref(v_params_1623_);
lean_inc_ref(v_type_1624_);
lean_inc_ref(v_decl_1612_);
v___x_1629_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1626_, v_decl_1612_, v_type_1624_, v_params_1623_, v_a_1628_, v_a_1511_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
lean_inc_ref(v_k_1613_);
v___x_1631_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1613_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1669_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1669_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1669_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
size_t v___x_1636_; size_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = lean_ptr_addr(v_k_1613_);
v___x_1637_ = lean_ptr_addr(v_a_1632_);
v___x_1638_ = lean_usize_dec_eq(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1648_; 
v_isSharedCheck_1648_ = !lean_is_exclusive(v_code_1506_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; 
v_unused_1649_ = lean_ctor_get(v_code_1506_, 1);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_code_1506_, 0);
lean_dec(v_unused_1650_);
v___x_1640_ = v_code_1506_;
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_code_1506_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v_a_1632_);
lean_ctor_set(v___x_1640_, 0, v_a_1630_);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1630_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_a_1632_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1643_);
v___x_1645_ = v___x_1634_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
size_t v___x_1651_; size_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_ptr_addr(v_decl_1612_);
v___x_1652_ = lean_ptr_addr(v_a_1630_);
v___x_1653_ = lean_usize_dec_eq(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1663_; 
v_isSharedCheck_1663_ = !lean_is_exclusive(v_code_1506_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; lean_object* v_unused_1665_; 
v_unused_1664_ = lean_ctor_get(v_code_1506_, 1);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_code_1506_, 0);
lean_dec(v_unused_1665_);
v___x_1655_ = v_code_1506_;
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_code_1506_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_a_1632_);
lean_ctor_set(v___x_1655_, 0, v_a_1630_);
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1630_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1632_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1658_);
v___x_1660_ = v___x_1634_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v___x_1667_; 
lean_dec(v_a_1632_);
lean_dec(v_a_1630_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v_code_1506_);
v___x_1667_ = v___x_1634_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_code_1506_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
else
{
lean_dec(v_a_1630_);
lean_dec_ref_known(v_code_1506_, 2);
return v___x_1631_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref_known(v_code_1506_, 2);
v_a_1670_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1629_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1629_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_dec_ref_known(v_code_1506_, 2);
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref_known(v_code_1506_, 2);
v_a_1679_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1614_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1614_);
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
case 3:
{
lean_object* v_fvarId_1687_; lean_object* v_args_1688_; lean_object* v___x_1689_; 
v_fvarId_1687_ = lean_ctor_get(v_code_1506_, 0);
v_args_1688_ = lean_ctor_get(v_code_1506_, 1);
lean_inc_ref(v_args_1688_);
v___x_1689_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1687_, v_args_1688_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1701_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
if (lean_obj_tag(v_a_1690_) == 1)
{
lean_object* v_val_1694_; lean_object* v___x_1696_; 
lean_dec_ref_known(v_code_1506_, 2);
v_val_1694_ = lean_ctor_get(v_a_1690_, 0);
lean_inc(v_val_1694_);
lean_dec_ref_known(v_a_1690_, 1);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v_val_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_val_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
lean_object* v___x_1699_; 
lean_dec(v_a_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v_code_1506_);
v___x_1699_ = v___x_1692_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_code_1506_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref_known(v_code_1506_, 2);
v_a_1702_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1689_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1689_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
case 4:
{
lean_object* v_cases_1710_; lean_object* v_typeName_1711_; lean_object* v_resultType_1712_; lean_object* v_discr_1713_; lean_object* v_alts_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1753_; 
v_cases_1710_ = lean_ctor_get(v_code_1506_, 0);
lean_inc_ref(v_cases_1710_);
v_typeName_1711_ = lean_ctor_get(v_cases_1710_, 0);
v_resultType_1712_ = lean_ctor_get(v_cases_1710_, 1);
v_discr_1713_ = lean_ctor_get(v_cases_1710_, 2);
v_alts_1714_ = lean_ctor_get(v_cases_1710_, 3);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_cases_1710_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1716_ = v_cases_1710_;
v_isShared_1717_ = v_isSharedCheck_1753_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_alts_1714_);
lean_inc(v_discr_1713_);
lean_inc(v_resultType_1712_);
lean_inc(v_typeName_1711_);
lean_dec(v_cases_1710_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1753_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1714_);
lean_inc(v_discr_1713_);
v___x_1719_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1713_, v___x_1718_, v_alts_1714_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1744_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1744_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1744_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
size_t v___x_1724_; size_t v___x_1725_; uint8_t v___x_1726_; 
v___x_1724_ = lean_ptr_addr(v_alts_1714_);
lean_dec_ref(v_alts_1714_);
v___x_1725_ = lean_ptr_addr(v_a_1720_);
v___x_1726_ = lean_usize_dec_eq(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1739_; 
v_isSharedCheck_1739_ = !lean_is_exclusive(v_code_1506_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v_code_1506_, 0);
lean_dec(v_unused_1740_);
v___x_1728_ = v_code_1506_;
v_isShared_1729_ = v_isSharedCheck_1739_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v_code_1506_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1739_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 3, v_a_1720_);
v___x_1731_ = v___x_1716_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_typeName_1711_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_resultType_1712_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_discr_1713_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v_a_1720_);
v___x_1731_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1731_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1733_);
v___x_1735_ = v___x_1722_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
else
{
lean_object* v___x_1742_; 
lean_dec(v_a_1720_);
lean_del_object(v___x_1716_);
lean_dec(v_discr_1713_);
lean_dec_ref(v_resultType_1712_);
lean_dec(v_typeName_1711_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v_code_1506_);
v___x_1742_ = v___x_1722_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_code_1506_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_del_object(v___x_1716_);
lean_dec_ref(v_alts_1714_);
lean_dec(v_discr_1713_);
lean_dec_ref(v_resultType_1712_);
lean_dec(v_typeName_1711_);
lean_dec_ref_known(v_code_1506_, 1);
v_a_1745_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1719_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1719_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
default: 
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_code_1506_);
return v___x_1754_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_1506_ = stack[0].m_obj;
lean_object* v_a_1507_ = stack[1].m_obj;
lean_object* v_a_1508_ = stack[2].m_obj;
lean_object* v_a_1509_ = stack[3].m_obj;
lean_object* v_a_1510_ = stack[4].m_obj;
lean_object* v_a_1511_ = stack[5].m_obj;
lean_object* v_a_1512_ = stack[6].m_obj;
lean_object* v_a_1513_ = stack[7].m_obj;
lean_object* v_res_1755_;
v_res_1755_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
stack->m_obj
 = v_res_1755_;
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object* v_discr_1756_, lean_object* v_i_1757_, lean_object* v_as_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_array_get_size(v_as_1758_);
v___x_1768_ = lean_nat_dec_lt(v_i_1757_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; 
lean_dec(v_i_1757_);
lean_dec(v_discr_1756_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_as_1758_);
return v___x_1769_;
}
else
{
lean_object* v_a_1770_; lean_object* v_a_1772_; 
v_a_1770_ = lean_array_fget_borrowed(v_as_1758_, v_i_1757_);
if (lean_obj_tag(v_a_1770_) == 0)
{
lean_object* v_ctorName_1783_; lean_object* v_params_1784_; lean_object* v_code_1785_; lean_object* v___x_1786_; 
v_ctorName_1783_ = lean_ctor_get(v_a_1770_, 0);
v_params_1784_ = lean_ctor_get(v_a_1770_, 1);
v_code_1785_ = lean_ctor_get(v_a_1770_, 2);
lean_inc_ref(v_params_1784_);
lean_inc(v_ctorName_1783_);
lean_inc(v_discr_1756_);
v___x_1786_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1756_, v_ctorName_1783_, v_params_1784_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
lean_inc_ref(v_code_1785_);
v___x_1788_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1785_, v___y_1759_, v___y_1760_, v_a_1787_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v_a_1787_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
lean_inc_ref(v_a_1770_);
v___x_1790_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1770_, v_a_1789_);
v_a_1772_ = v___x_1790_;
goto v___jp_1771_;
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec_ref(v_as_1758_);
lean_dec(v_i_1757_);
lean_dec(v_discr_1756_);
v_a_1791_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1788_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1788_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v_as_1758_);
lean_dec(v_i_1757_);
lean_dec(v_discr_1756_);
v_a_1799_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1786_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1786_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_code_1807_; lean_object* v___x_1808_; 
v_code_1807_ = lean_ctor_get(v_a_1770_, 0);
lean_inc_ref(v_code_1807_);
v___x_1808_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1807_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
lean_inc_ref(v_a_1770_);
v___x_1810_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1770_, v_a_1809_);
v_a_1772_ = v___x_1810_;
goto v___jp_1771_;
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_as_1758_);
lean_dec(v_i_1757_);
lean_dec(v_discr_1756_);
v_a_1811_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1808_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1808_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
v___jp_1771_:
{
size_t v___x_1773_; size_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = lean_ptr_addr(v_a_1770_);
v___x_1774_ = lean_ptr_addr(v_a_1772_);
v___x_1775_ = lean_usize_dec_eq(v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_i_1757_, v___x_1776_);
v___x_1778_ = lean_array_fset(v_as_1758_, v_i_1757_, v_a_1772_);
lean_dec(v_i_1757_);
v_i_1757_ = v___x_1777_;
v_as_1758_ = v___x_1778_;
goto _start;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec_ref(v_a_1772_);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_nat_add(v_i_1757_, v___x_1780_);
lean_dec(v_i_1757_);
v_i_1757_ = v___x_1781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_1756_ = stack[0].m_obj;
lean_object* v_i_1757_ = stack[1].m_obj;
lean_object* v_as_1758_ = stack[2].m_obj;
lean_object* v___y_1759_ = stack[3].m_obj;
lean_object* v___y_1760_ = stack[4].m_obj;
lean_object* v___y_1761_ = stack[5].m_obj;
lean_object* v___y_1762_ = stack[6].m_obj;
lean_object* v___y_1763_ = stack[7].m_obj;
lean_object* v___y_1764_ = stack[8].m_obj;
lean_object* v___y_1765_ = stack[9].m_obj;
lean_object* v_res_1819_;
v_res_1819_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1756_, v_i_1757_, v_as_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
stack->m_obj
 = v_res_1819_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object* v_discr_1820_, lean_object* v_i_1821_, lean_object* v_as_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1820_, v_i_1821_, v_as_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec(v___y_1823_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object* v_decl_1832_, lean_object* v_k_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1832_, v_k_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec(v_a_1834_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object** _args){
lean_object* v_discr_1843_ = _args[0];
lean_object* v___x_1844_ = _args[1];
lean_object* v_val_1845_ = _args[2];
lean_object* v_fst_1846_ = _args[3];
lean_object* v_params_1847_ = _args[4];
lean_object* v_snd_1848_ = _args[5];
lean_object* v_as_1849_ = _args[6];
lean_object* v_sz_1850_ = _args[7];
lean_object* v_i_1851_ = _args[8];
lean_object* v_b_1852_ = _args[9];
lean_object* v___y_1853_ = _args[10];
lean_object* v___y_1854_ = _args[11];
lean_object* v___y_1855_ = _args[12];
lean_object* v___y_1856_ = _args[13];
lean_object* v___y_1857_ = _args[14];
lean_object* v___y_1858_ = _args[15];
lean_object* v___y_1859_ = _args[16];
lean_object* v___y_1860_ = _args[17];
_start:
{
size_t v_sz_boxed_1861_; size_t v_i_boxed_1862_; lean_object* v_res_1863_; 
v_sz_boxed_1861_ = lean_unbox_usize(v_sz_1850_);
lean_dec(v_sz_1850_);
v_i_boxed_1862_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_res_1863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1843_, v___x_1844_, v_val_1845_, v_fst_1846_, v_params_1847_, v_snd_1848_, v_as_1849_, v_sz_boxed_1861_, v_i_boxed_1862_, v_b_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v_as_1849_);
lean_dec_ref(v_snd_1848_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object* v_code_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec(v_a_1865_);
return v_res_1873_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object* v___x_1874_, lean_object* v_a_1875_, lean_object* v_init_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1874_, v_a_1875_, v_init_1876_, v_x_1877_);
return v___x_1886_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1874_ = stack[0].m_obj;
lean_object* v_a_1875_ = stack[1].m_obj;
lean_object* v_init_1876_ = stack[2].m_obj;
lean_object* v_x_1877_ = stack[3].m_obj;
lean_object* v___y_1878_ = stack[4].m_obj;
lean_object* v___y_1879_ = stack[5].m_obj;
lean_object* v___y_1880_ = stack[6].m_obj;
lean_object* v___y_1881_ = stack[7].m_obj;
lean_object* v___y_1882_ = stack[8].m_obj;
lean_object* v___y_1883_ = stack[9].m_obj;
lean_object* v___y_1884_ = stack[10].m_obj;
lean_object* v_res_1887_;
v_res_1887_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(v___x_1874_, v_a_1875_, v_init_1876_, v_x_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
stack->m_obj
 = v_res_1887_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object* v___x_1888_, lean_object* v_a_1889_, lean_object* v_init_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(v___x_1888_, v_a_1889_, v_init_1890_, v_x_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec(v___x_1888_);
return v_res_1900_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1903_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1904_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
lean_ctor_set(v___x_1906_, 2, v___x_1905_);
lean_ctor_set(v___x_1906_, 3, v___x_1905_);
lean_ctor_set(v___x_1906_, 4, v___x_1904_);
lean_ctor_set(v___x_1906_, 5, v___x_1904_);
lean_ctor_set(v___x_1906_, 6, v___x_1904_);
lean_ctor_set(v___x_1906_, 7, v___x_1904_);
lean_ctor_set(v___x_1906_, 8, v___x_1904_);
lean_ctor_set(v___x_1906_, 9, v___x_1904_);
lean_ctor_set(v___x_1906_, 10, v___x_1904_);
lean_ctor_set(v___x_1906_, 11, v___x_1903_);
return v___x_1906_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1907_; double v___x_1908_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_float_of_nat(v___x_1907_);
return v___x_1908_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object* v_cls_1912_, lean_object* v_msg_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_ref_1919_; lean_object* v___x_1920_; lean_object* v_env_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_ref_1919_ = lean_ctor_get(v___y_1916_, 2);
v___x_1920_ = lean_st_ref_get(v___y_1917_);
v_env_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_ref(v_env_1921_);
lean_dec(v___x_1920_);
v___x_1922_ = lean_st_ref_get(v___y_1915_);
v___x_1923_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1914_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1983_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1983_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1983_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_lctx_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1981_; 
v_lctx_1928_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v___x_1922_, 1);
lean_dec(v_unused_1982_);
v___x_1930_ = v___x_1922_;
v_isShared_1931_ = v_isSharedCheck_1981_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_lctx_1928_);
lean_dec(v___x_1922_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1981_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1932_ = lean_unbox(v_a_1924_);
lean_dec(v_a_1924_);
v___x_1933_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1928_, v___x_1932_);
lean_dec_ref(v_lctx_1928_);
v___x_1934_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1916_);
v___x_1935_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1);
v___x_1936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1936_, 0, v_env_1921_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
lean_ctor_set(v___x_1936_, 2, v___x_1933_);
lean_ctor_set(v___x_1936_, 3, v___x_1934_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set_tag(v___x_1930_, 3);
lean_ctor_set(v___x_1930_, 1, v_msg_1913_);
lean_ctor_set(v___x_1930_, 0, v___x_1936_);
v___x_1938_ = v___x_1930_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_msg_1913_);
v___x_1938_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; lean_object* v_traceState_1940_; lean_object* v_env_1941_; lean_object* v_nextMacroScope_1942_; lean_object* v_ngen_1943_; lean_object* v_auxDeclNGen_1944_; lean_object* v_cache_1945_; lean_object* v_recordedDeps_1946_; lean_object* v_messages_1947_; lean_object* v_infoState_1948_; lean_object* v_snapshotTasks_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1979_; 
v___x_1939_ = lean_st_ref_take(v___y_1917_);
v_traceState_1940_ = lean_ctor_get(v___x_1939_, 4);
v_env_1941_ = lean_ctor_get(v___x_1939_, 0);
v_nextMacroScope_1942_ = lean_ctor_get(v___x_1939_, 1);
v_ngen_1943_ = lean_ctor_get(v___x_1939_, 2);
v_auxDeclNGen_1944_ = lean_ctor_get(v___x_1939_, 3);
v_cache_1945_ = lean_ctor_get(v___x_1939_, 5);
v_recordedDeps_1946_ = lean_ctor_get(v___x_1939_, 6);
v_messages_1947_ = lean_ctor_get(v___x_1939_, 7);
v_infoState_1948_ = lean_ctor_get(v___x_1939_, 8);
v_snapshotTasks_1949_ = lean_ctor_get(v___x_1939_, 9);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1951_ = v___x_1939_;
v_isShared_1952_ = v_isSharedCheck_1979_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_snapshotTasks_1949_);
lean_inc(v_infoState_1948_);
lean_inc(v_messages_1947_);
lean_inc(v_recordedDeps_1946_);
lean_inc(v_cache_1945_);
lean_inc(v_traceState_1940_);
lean_inc(v_auxDeclNGen_1944_);
lean_inc(v_ngen_1943_);
lean_inc(v_nextMacroScope_1942_);
lean_inc(v_env_1941_);
lean_dec(v___x_1939_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1979_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
uint64_t v_tid_1953_; lean_object* v_traces_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1978_; 
v_tid_1953_ = lean_ctor_get_uint64(v_traceState_1940_, sizeof(void*)*1);
v_traces_1954_ = lean_ctor_get(v_traceState_1940_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_traceState_1940_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1956_ = v_traceState_1940_;
v_isShared_1957_ = v_isSharedCheck_1978_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_traces_1954_);
lean_dec(v_traceState_1940_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1978_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; double v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2);
v___x_1961_ = 0;
v___x_1962_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3));
v___x_1963_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1963_, 0, v_cls_1912_);
lean_ctor_set(v___x_1963_, 1, v___x_1959_);
lean_ctor_set(v___x_1963_, 2, v___x_1962_);
lean_ctor_set_float(v___x_1963_, sizeof(void*)*3, v___x_1960_);
lean_ctor_set_float(v___x_1963_, sizeof(void*)*3 + 8, v___x_1960_);
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*3 + 16, v___x_1961_);
v___x_1964_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4));
v___x_1965_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1938_);
lean_ctor_set(v___x_1965_, 2, v___x_1964_);
lean_inc(v_ref_1919_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_ref_1919_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = l_Lean_PersistentArray_push___redArg(v_traces_1954_, v___x_1966_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1967_);
v___x_1969_ = v___x_1956_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1967_);
lean_ctor_set_uint64(v_reuseFailAlloc_1977_, sizeof(void*)*1, v_tid_1953_);
v___x_1969_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 4, v___x_1969_);
v___x_1971_ = v___x_1951_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_env_1941_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_nextMacroScope_1942_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_ngen_1943_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_auxDeclNGen_1944_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1976_, 5, v_cache_1945_);
lean_ctor_set(v_reuseFailAlloc_1976_, 6, v_recordedDeps_1946_);
lean_ctor_set(v_reuseFailAlloc_1976_, 7, v_messages_1947_);
lean_ctor_set(v_reuseFailAlloc_1976_, 8, v_infoState_1948_);
lean_ctor_set(v_reuseFailAlloc_1976_, 9, v_snapshotTasks_1949_);
v___x_1971_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = lean_st_ref_put(v___y_1917_, v___x_1971_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1958_);
v___x_1974_ = v___x_1926_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1958_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
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
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v___x_1922_);
lean_dec_ref(v_env_1921_);
lean_dec_ref(v_msg_1913_);
lean_dec(v_cls_1912_);
v_a_1984_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1923_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1923_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1912_ = stack[0].m_obj;
lean_object* v_msg_1913_ = stack[1].m_obj;
lean_object* v___y_1914_ = stack[2].m_obj;
lean_object* v___y_1915_ = stack[3].m_obj;
lean_object* v___y_1916_ = stack[4].m_obj;
lean_object* v___y_1917_ = stack[5].m_obj;
lean_object* v_res_1992_;
v_res_1992_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v_cls_1912_, v_msg_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
stack->m_obj
 = v_res_1992_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object* v_cls_1993_, lean_object* v_msg_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v_cls_1993_, v_msg_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object* v_init_2001_, lean_object* v_x_2002_){
_start:
{
if (lean_obj_tag(v_x_2002_) == 0)
{
lean_object* v_k_2003_; lean_object* v_v_2004_; lean_object* v_l_2005_; lean_object* v_r_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_k_2003_ = lean_ctor_get(v_x_2002_, 1);
v_v_2004_ = lean_ctor_get(v_x_2002_, 2);
v_l_2005_ = lean_ctor_get(v_x_2002_, 3);
v_r_2006_ = lean_ctor_get(v_x_2002_, 4);
v___x_2007_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_2001_, v_r_2006_);
lean_inc(v_v_2004_);
lean_inc(v_k_2003_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_k_2003_);
lean_ctor_set(v___x_2008_, 1, v_v_2004_);
v___x_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v___x_2007_);
v_init_2001_ = v___x_2009_;
v_x_2002_ = v_l_2005_;
goto _start;
}
else
{
return v_init_2001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object* v_init_2011_, lean_object* v_x_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_2011_, v_x_2012_);
lean_dec(v_x_2012_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
if (lean_obj_tag(v_a_2014_) == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = l_List_reverse___redArg(v_a_2015_);
return v___x_2016_;
}
else
{
lean_object* v_head_2017_; lean_object* v_tail_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2027_; 
v_head_2017_ = lean_ctor_get(v_a_2014_, 0);
v_tail_2018_ = lean_ctor_get(v_a_2014_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2020_ = v_a_2014_;
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_tail_2018_);
lean_inc(v_head_2017_);
lean_dec(v_a_2014_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = l_Lean_MessageData_ofName(v_head_2017_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v_a_2015_);
lean_ctor_set(v___x_2020_, 0, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_a_2015_);
v___x_2024_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
v_a_2014_ = v_tail_2018_;
v_a_2015_ = v___x_2024_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object* v_init_2028_, lean_object* v_x_2029_){
_start:
{
if (lean_obj_tag(v_x_2029_) == 0)
{
lean_object* v_k_2030_; lean_object* v_l_2031_; lean_object* v_r_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_k_2030_ = lean_ctor_get(v_x_2029_, 1);
v_l_2031_ = lean_ctor_get(v_x_2029_, 3);
v_r_2032_ = lean_ctor_get(v_x_2029_, 4);
v___x_2033_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_2028_, v_r_2032_);
lean_inc(v_k_2030_);
v___x_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2034_, 0, v_k_2030_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v_init_2028_ = v___x_2034_;
v_x_2029_ = v_l_2031_;
goto _start;
}
else
{
return v_init_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object* v_init_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_2036_, v_x_2037_);
lean_dec(v_x_2037_);
return v_res_2038_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0));
v___x_2041_ = l_Lean_stringToMessageData(v___x_2040_);
return v___x_2041_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(lean_object* v_as_x27_2042_, lean_object* v_b_2043_){
_start:
{
if (lean_obj_tag(v_as_x27_2042_) == 0)
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_b_2043_);
return v___x_2045_;
}
else
{
lean_object* v_head_2046_; lean_object* v_snd_2047_; lean_object* v_tail_2048_; lean_object* v_fst_2049_; lean_object* v_ctorNames_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_head_2046_ = lean_ctor_get(v_as_x27_2042_, 0);
v_snd_2047_ = lean_ctor_get(v_head_2046_, 1);
v_tail_2048_ = lean_ctor_get(v_as_x27_2042_, 1);
v_fst_2049_ = lean_ctor_get(v_head_2046_, 0);
v_ctorNames_2050_ = lean_ctor_get(v_snd_2047_, 1);
lean_inc(v_fst_2049_);
v___x_2051_ = l_Lean_mkFVar(v_fst_2049_);
v___x_2052_ = l_Lean_MessageData_ofExpr(v___x_2051_);
v___x_2053_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = lean_box(0);
v___x_2056_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v___x_2055_, v_ctorNames_2050_);
v___x_2057_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(v___x_2056_, v___x_2055_);
v___x_2058_ = l_Lean_MessageData_ofList(v___x_2057_);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2054_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_indentD(v___x_2059_);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_b_2043_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v_as_x27_2042_ = v_tail_2048_;
v_b_2043_ = v___x_2061_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2042_ = stack[0].m_obj;
lean_object* v_b_2043_ = stack[1].m_obj;
lean_object* v_res_2063_;
v_res_2063_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2042_, v_b_2043_);
stack->m_obj
 = v_res_2063_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___boxed(lean_object* v_as_x27_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2064_, v_b_2065_);
lean_dec(v_as_x27_2064_);
return v_res_2067_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2079_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5));
v___x_2080_ = l_Lean_Name_append(v___x_2079_, v___x_2078_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8));
v___x_2085_ = l_Lean_MessageData_ofFormat(v___x_2084_);
return v___x_2085_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object* v_code_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___x_2092_; 
lean_inc_ref(v_code_2086_);
v___x_2092_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2146_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2146_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2146_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
uint8_t v___x_2120_; 
v___x_2120_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_a_2093_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec(v_a_2093_);
lean_dec_ref(v_code_2086_);
v___x_2121_ = lean_box(0);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2121_);
v___x_2123_ = v___x_2095_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
else
{
lean_object* v_toCold_2125_; lean_object* v_options_2126_; uint8_t v_hasTrace_2127_; 
lean_del_object(v___x_2095_);
v_toCold_2125_ = lean_ctor_get(v_a_2089_, 0);
v_options_2126_ = lean_ctor_get(v_toCold_2125_, 2);
v_hasTrace_2127_ = lean_ctor_get_uint8(v_options_2126_, sizeof(void*)*1);
if (v_hasTrace_2127_ == 0)
{
goto v___jp_2097_;
}
else
{
lean_object* v_inheritedTraceOptions_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_inheritedTraceOptions_2128_ = lean_ctor_get(v_toCold_2125_, 11);
v___x_2129_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2130_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6);
v___x_2131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2128_, v_options_2126_, v___x_2130_);
if (v___x_2131_ == 0)
{
goto v___jp_2097_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_a_2136_; lean_object* v___x_2137_; 
v___x_2132_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9);
v___x_2133_ = lean_box(0);
v___x_2134_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v___x_2133_, v_a_2093_);
v___x_2135_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v___x_2134_, v___x_2132_);
lean_dec(v___x_2134_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref(v___x_2135_);
v___x_2137_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v___x_2129_, v_a_2136_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_dec_ref_known(v___x_2137_, 1);
goto v___jp_2097_;
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_a_2093_);
lean_dec_ref(v_code_2086_);
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
v___jp_2097_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2098_ = lean_box(1);
v___x_2099_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_2100_ = lean_st_mk_ref(v___x_2098_);
v___x_2101_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_2086_, v_a_2093_, v___x_2100_, v___x_2099_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2093_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2111_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2111_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2111_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2106_ = lean_st_ref_get(v___x_2100_);
lean_dec(v___x_2100_);
lean_dec(v___x_2106_);
v___x_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_a_2102_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2107_);
v___x_2109_ = v___x_2104_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v___x_2100_);
v_a_2112_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2101_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2101_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_code_2086_);
v_a_2147_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2092_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2092_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_2086_ = stack[0].m_obj;
lean_object* v_a_2087_ = stack[1].m_obj;
lean_object* v_a_2088_ = stack[2].m_obj;
lean_object* v_a_2089_ = stack[3].m_obj;
lean_object* v_a_2090_ = stack[4].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v_code_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object* v_code_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v_code_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v_res_2162_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object* v_as_2163_, lean_object* v_as_x27_2164_, lean_object* v_b_2165_, lean_object* v_a_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v_as_x27_2164_, v_b_2165_);
return v___x_2172_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2163_ = stack[0].m_obj;
lean_object* v_as_x27_2164_ = stack[1].m_obj;
lean_object* v_b_2165_ = stack[2].m_obj;
lean_object* v___y_2167_ = stack[4].m_obj;
lean_object* v___y_2168_ = stack[5].m_obj;
lean_object* v___y_2169_ = stack[6].m_obj;
lean_object* v___y_2170_ = stack[7].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v_as_2163_, v_as_x27_2164_, v_b_2165_, lean_box(0), v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object* v_as_2174_, lean_object* v_as_x27_2175_, lean_object* v_b_2176_, lean_object* v_a_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v_as_2174_, v_as_x27_2175_, v_b_2176_, v_a_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_as_x27_2175_);
lean_dec(v_as_2174_);
return v_res_2183_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2257_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2258_ = 0;
v___x_2259_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_));
v___x_2260_ = l_Lean_registerTraceClass(v___x_2257_, v___x_2258_, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2261_;
v_res_2261_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2261_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
return v_res_2263_;
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
