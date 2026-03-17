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
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1(uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instSingletonFVarIdFVarIdSet;
uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1;
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
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 122, 96, 221, 209, 205, 68, 156)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 92, 220, 8, 204, 108, 198, 7)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "candidates"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0(lean_object* v_cases_1_, lean_object* v_param_2_){
_start:
{
lean_object* v_discr_3_; lean_object* v_fvarId_4_; uint8_t v___x_5_; 
v_discr_3_ = lean_ctor_get(v_cases_1_, 2);
v_fvarId_4_ = lean_ctor_get(v_param_2_, 0);
v___x_5_ = l_Lean_instBEqFVarId_beq(v_discr_3_, v_fvarId_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0___boxed(lean_object* v_cases_6_, lean_object* v_param_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0(v_cases_6_, v_param_7_);
lean_dec_ref(v_param_7_);
lean_dec_ref(v_cases_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(lean_object* v_decl_10_, lean_object* v_small_11_, lean_object* v_code_12_, lean_object* v_prefixSize_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_lt(v_small_11_, v_prefixSize_13_);
if (v___x_14_ == 0)
{
switch(lean_obj_tag(v_code_12_))
{
case 0:
{
lean_object* v_k_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_k_15_ = lean_ctor_get(v_code_12_, 1);
lean_inc_ref(v_k_15_);
lean_dec_ref(v_code_12_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_prefixSize_13_, v___x_16_);
lean_dec(v_prefixSize_13_);
v_code_12_ = v_k_15_;
v_prefixSize_13_ = v___x_17_;
goto _start;
}
case 4:
{
lean_object* v_cases_19_; lean_object* v_params_20_; lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_prefixSize_13_);
v_cases_19_ = lean_ctor_get(v_code_12_, 0);
lean_inc_ref(v_cases_19_);
lean_dec_ref(v_code_12_);
v_params_20_ = lean_ctor_get(v_decl_10_, 2);
v___f_21_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___lam__0___boxed), 2, 1);
lean_closure_set(v___f_21_, 0, v_cases_19_);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = l_Array_findIdx_x3f_loop___redArg(v___f_21_, v_params_20_, v___x_22_);
return v___x_23_;
}
default: 
{
lean_object* v___x_24_; 
lean_dec(v_prefixSize_13_);
lean_dec_ref(v_code_12_);
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
}
else
{
lean_object* v___x_25_; 
lean_dec(v_prefixSize_13_);
lean_dec_ref(v_code_12_);
v___x_25_ = lean_box(0);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___boxed(lean_object* v_decl_26_, lean_object* v_small_27_, lean_object* v_code_28_, lean_object* v_prefixSize_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(v_decl_26_, v_small_27_, v_code_28_, v_prefixSize_29_);
lean_dec(v_small_27_);
lean_dec_ref(v_decl_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(lean_object* v_decl_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_params_34_; lean_object* v_value_35_; lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_params_34_ = lean_ctor_get(v_decl_31_, 2);
v_value_35_ = lean_ctor_get(v_decl_31_, 4);
lean_inc_ref(v_value_35_);
v___x_36_ = lean_array_get_size(v_params_34_);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_nat_dec_eq(v___x_36_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_32_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_49_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_49_ == 0)
{
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_smallThreshold_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v_smallThreshold_44_ = lean_ctor_get(v_a_40_, 0);
lean_inc(v_smallThreshold_44_);
lean_dec(v_a_40_);
v___x_45_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(v_decl_31_, v_smallThreshold_44_, v_value_35_, v___x_37_);
lean_dec(v_smallThreshold_44_);
lean_dec_ref(v_decl_31_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_45_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
else
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
lean_dec_ref(v_value_35_);
lean_dec_ref(v_decl_31_);
v_a_50_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_39_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_39_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec_ref(v_value_35_);
lean_dec_ref(v_decl_31_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg___boxed(lean_object* v_decl_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_60_, v_a_61_);
lean_dec_ref(v_a_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(lean_object* v_decl_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_64_, v_a_65_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___boxed(lean_object* v_decl_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(v_decl_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_77_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = l_Lean_NameSet_empty;
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0, &l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default;
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(lean_object* v_init_94_, lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v_v_96_; lean_object* v_l_97_; lean_object* v_r_98_; lean_object* v___x_99_; 
v_v_96_ = lean_ctor_get(v_x_95_, 2);
v_l_97_ = lean_ctor_get(v_x_95_, 3);
v_r_98_ = lean_ctor_get(v_x_95_, 4);
v___x_99_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_94_, v_l_97_);
if (lean_obj_tag(v___x_99_) == 0)
{
return v___x_99_;
}
else
{
lean_object* v_ctorNames_100_; 
lean_dec_ref(v___x_99_);
v_ctorNames_100_ = lean_ctor_get(v_v_96_, 1);
if (lean_obj_tag(v_ctorNames_100_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2));
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v_init_94_ = v___x_102_;
v_x_95_ = v_r_98_;
goto _start;
}
}
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_init_94_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___boxed(lean_object* v_init_105_, lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_105_, v_x_106_);
lean_dec(v_x_106_);
return v_res_107_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(lean_object* v_info_108_){
_start:
{
lean_object* v___y_110_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_a_117_; 
v___x_115_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v___x_116_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v___x_115_, v_info_108_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v___x_116_);
v___y_110_ = v_a_117_;
goto v___jp_109_;
v___jp_109_:
{
lean_object* v_fst_111_; 
v_fst_111_ = lean_ctor_get(v___y_110_, 0);
lean_inc(v_fst_111_);
lean_dec_ref(v___y_110_);
if (lean_obj_tag(v_fst_111_) == 0)
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
else
{
lean_object* v_val_113_; uint8_t v___x_114_; 
v_val_113_ = lean_ctor_get(v_fst_111_, 0);
lean_inc(v_val_113_);
lean_dec_ref(v_fst_111_);
v___x_114_ = lean_unbox(v_val_113_);
lean_dec(v_val_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(lean_object* v_info_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_info_118_);
lean_dec(v_info_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(lean_object* v_t_121_, lean_object* v_k_122_){
_start:
{
if (lean_obj_tag(v_t_121_) == 0)
{
lean_object* v_k_123_; lean_object* v_v_124_; lean_object* v_l_125_; lean_object* v_r_126_; uint8_t v___x_127_; 
v_k_123_ = lean_ctor_get(v_t_121_, 1);
v_v_124_ = lean_ctor_get(v_t_121_, 2);
v_l_125_ = lean_ctor_get(v_t_121_, 3);
v_r_126_ = lean_ctor_get(v_t_121_, 4);
v___x_127_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_122_, v_k_123_);
switch(v___x_127_)
{
case 0:
{
v_t_121_ = v_l_125_;
goto _start;
}
case 1:
{
lean_object* v___x_129_; 
lean_inc(v_v_124_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_v_124_);
return v___x_129_;
}
default: 
{
v_t_121_ = v_r_126_;
goto _start;
}
}
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(lean_object* v_t_132_, lean_object* v_k_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_132_, v_k_133_);
lean_dec(v_k_133_);
lean_dec(v_t_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(lean_object* v_code_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
switch(lean_obj_tag(v_code_135_))
{
case 0:
{
lean_object* v_k_143_; 
v_k_143_ = lean_ctor_get(v_code_135_, 1);
lean_inc_ref(v_k_143_);
lean_dec_ref(v_code_135_);
v_code_135_ = v_k_143_;
goto _start;
}
case 1:
{
lean_object* v_decl_145_; lean_object* v_k_146_; lean_object* v_value_147_; lean_object* v___x_148_; 
v_decl_145_ = lean_ctor_get(v_code_135_, 0);
lean_inc_ref(v_decl_145_);
v_k_146_ = lean_ctor_get(v_code_135_, 1);
lean_inc_ref(v_k_146_);
lean_dec_ref(v_code_135_);
v_value_147_ = lean_ctor_get(v_decl_145_, 4);
lean_inc_ref(v_value_147_);
lean_dec_ref(v_decl_145_);
lean_inc(v_a_141_);
lean_inc_ref(v_a_140_);
lean_inc(v_a_139_);
lean_inc_ref(v_a_138_);
lean_inc_ref(v_a_137_);
v___x_148_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_147_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_dec_ref(v___x_148_);
v_code_135_ = v_k_146_;
goto _start;
}
else
{
lean_dec_ref(v_k_146_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_a_137_);
return v___x_148_;
}
}
case 2:
{
lean_object* v_decl_150_; lean_object* v_k_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_184_; 
v_decl_150_ = lean_ctor_get(v_code_135_, 0);
v_k_151_ = lean_ctor_get(v_code_135_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_code_135_);
if (v_isSharedCheck_184_ == 0)
{
v___x_153_ = v_code_135_;
v_isShared_154_ = v_isSharedCheck_184_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_k_151_);
lean_inc(v_decl_150_);
lean_dec(v_code_135_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_184_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___x_165_; 
lean_inc_ref(v_decl_150_);
v___x_165_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_150_, v_a_138_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref(v___x_165_);
if (lean_obj_tag(v_a_166_) == 1)
{
lean_object* v_val_167_; lean_object* v___x_168_; lean_object* v_fvarId_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v_val_167_ = lean_ctor_get(v_a_166_, 0);
lean_inc(v_val_167_);
lean_dec_ref(v_a_166_);
v___x_168_ = lean_st_ref_take(v_a_136_);
v_fvarId_169_ = lean_ctor_get(v_decl_150_, 0);
v___x_170_ = l_Lean_NameSet_empty;
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 0);
lean_ctor_set(v___x_153_, 1, v___x_170_);
lean_ctor_set(v___x_153_, 0, v_val_167_);
v___x_172_ = v___x_153_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_val_167_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_175_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_inc(v_fvarId_169_);
v___x_173_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_169_, v___x_172_, v___x_168_);
v___x_174_ = lean_st_ref_set(v_a_136_, v___x_173_);
v___y_156_ = v_a_136_;
v___y_157_ = v_a_137_;
v___y_158_ = v_a_138_;
v___y_159_ = v_a_139_;
v___y_160_ = v_a_140_;
v___y_161_ = v_a_141_;
goto v___jp_155_;
}
}
else
{
lean_dec(v_a_166_);
lean_del_object(v___x_153_);
v___y_156_ = v_a_136_;
v___y_157_ = v_a_137_;
v___y_158_ = v_a_138_;
v___y_159_ = v_a_139_;
v___y_160_ = v_a_140_;
v___y_161_ = v_a_141_;
goto v___jp_155_;
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_del_object(v___x_153_);
lean_dec_ref(v_k_151_);
lean_dec_ref(v_decl_150_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_a_137_);
v_a_176_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_165_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_165_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
v___jp_155_:
{
lean_object* v_value_162_; lean_object* v___x_163_; 
v_value_162_ = lean_ctor_get(v_decl_150_, 4);
lean_inc_ref(v_value_162_);
lean_dec_ref(v_decl_150_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc(v___y_159_);
lean_inc_ref(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_163_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_162_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_dec_ref(v___x_163_);
v_code_135_ = v_k_151_;
v_a_136_ = v___y_156_;
v_a_137_ = v___y_157_;
v_a_138_ = v___y_158_;
v_a_139_ = v___y_159_;
v_a_140_ = v___y_160_;
v_a_141_ = v___y_161_;
goto _start;
}
else
{
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec_ref(v_k_151_);
return v___x_163_;
}
}
}
}
case 3:
{
lean_object* v_fvarId_185_; lean_object* v_args_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_a_140_);
lean_dec_ref(v_a_138_);
v_fvarId_185_ = lean_ctor_get(v_code_135_, 0);
lean_inc(v_fvarId_185_);
v_args_186_ = lean_ctor_get(v_code_135_, 1);
lean_inc_ref(v_args_186_);
lean_dec_ref(v_code_135_);
v___x_187_ = lean_st_ref_get(v_a_136_);
v___x_188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_187_, v_fvarId_185_);
lean_dec(v___x_187_);
if (lean_obj_tag(v___x_188_) == 1)
{
lean_object* v_val_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_236_; 
v_val_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_236_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_236_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_val_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_236_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_paramIdx_193_; lean_object* v_ctorNames_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_235_; 
v_paramIdx_193_ = lean_ctor_get(v_val_189_, 0);
v_ctorNames_194_ = lean_ctor_get(v_val_189_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_val_189_);
if (v_isSharedCheck_235_ == 0)
{
v___x_196_ = v_val_189_;
v_isShared_197_ = v_isSharedCheck_235_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_ctorNames_194_);
lean_inc(v_paramIdx_193_);
lean_dec(v_val_189_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_235_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_box(0);
v___x_199_ = lean_array_get(v___x_198_, v_args_186_, v_paramIdx_193_);
lean_dec_ref(v_args_186_);
if (lean_obj_tag(v___x_199_) == 1)
{
lean_object* v_fvarId_200_; lean_object* v___x_201_; 
lean_del_object(v___x_191_);
v_fvarId_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_fvarId_200_);
lean_dec_ref(v___x_199_);
v___x_201_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(v_fvarId_200_, v_a_137_, v_a_139_, v_a_141_);
lean_dec(v_a_141_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_137_);
lean_dec(v_fvarId_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_222_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_222_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_222_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_222_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
if (lean_obj_tag(v_a_202_) == 1)
{
lean_object* v_val_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v_val_206_ = lean_ctor_get(v_a_202_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v_a_202_);
v___x_207_ = lean_st_ref_take(v_a_136_);
v___x_208_ = l_Lean_NameSet_insert(v_ctorNames_194_, v_val_206_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_208_);
v___x_210_ = v___x_196_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_paramIdx_193_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_217_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_185_, v___x_210_, v___x_207_);
v___x_212_ = lean_st_ref_set(v_a_136_, v___x_211_);
v___x_213_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_213_);
v___x_215_ = v___x_204_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_220_; 
lean_dec(v_a_202_);
lean_del_object(v___x_196_);
lean_dec(v_ctorNames_194_);
lean_dec(v_paramIdx_193_);
lean_dec(v_fvarId_185_);
v___x_218_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_218_);
v___x_220_ = v___x_204_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
else
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_del_object(v___x_196_);
lean_dec(v_ctorNames_194_);
lean_dec(v_paramIdx_193_);
lean_dec(v_fvarId_185_);
v_a_223_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_201_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_201_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
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
lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v___x_199_);
lean_del_object(v___x_196_);
lean_dec(v_ctorNames_194_);
lean_dec(v_paramIdx_193_);
lean_dec(v_fvarId_185_);
lean_dec(v_a_141_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_137_);
v___x_231_ = lean_box(0);
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 0);
lean_ctor_set(v___x_191_, 0, v___x_231_);
v___x_233_ = v___x_191_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v___x_188_);
lean_dec_ref(v_args_186_);
lean_dec(v_fvarId_185_);
lean_dec(v_a_141_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_137_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
case 4:
{
lean_object* v_cases_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_262_; 
v_cases_239_ = lean_ctor_get(v_code_135_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_code_135_);
if (v_isSharedCheck_262_ == 0)
{
v___x_241_ = v_code_135_;
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_cases_239_);
lean_dec(v_code_135_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_262_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_discr_243_; lean_object* v_alts_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_discr_243_ = lean_ctor_get(v_cases_239_, 2);
lean_inc(v_discr_243_);
v_alts_244_ = lean_ctor_get(v_cases_239_, 3);
lean_inc_ref(v_alts_244_);
lean_dec_ref(v_cases_239_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_array_get_size(v_alts_244_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_nat_dec_lt(v___x_245_, v___x_246_);
if (v___x_248_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_alts_244_);
lean_dec(v_discr_243_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_a_137_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 0);
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_250_ = v___x_241_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_247_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
else
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_le(v___x_246_, v___x_246_);
if (v___x_252_ == 0)
{
if (v___x_248_ == 0)
{
lean_object* v___x_254_; 
lean_dec_ref(v_alts_244_);
lean_dec(v_discr_243_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_a_137_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 0);
lean_ctor_set(v___x_241_, 0, v___x_247_);
v___x_254_ = v___x_241_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_247_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
size_t v___x_256_; size_t v___x_257_; lean_object* v___x_258_; 
lean_del_object(v___x_241_);
v___x_256_ = ((size_t)0ULL);
v___x_257_ = lean_usize_of_nat(v___x_246_);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_243_, v_alts_244_, v___x_256_, v___x_257_, v___x_247_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec_ref(v_alts_244_);
return v___x_258_;
}
}
else
{
size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; 
lean_del_object(v___x_241_);
v___x_259_ = ((size_t)0ULL);
v___x_260_ = lean_usize_of_nat(v___x_246_);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_243_, v_alts_244_, v___x_259_, v___x_260_, v___x_247_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec_ref(v_alts_244_);
return v___x_261_;
}
}
}
}
default: 
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec_ref(v_a_137_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_code_135_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v_code_135_, 0);
lean_dec(v_unused_271_);
v___x_264_ = v_code_135_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_dec(v_code_135_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 0);
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(lean_object* v_discr_272_, lean_object* v_as_273_, size_t v_i_274_, size_t v_stop_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___y_285_; uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_eq(v_i_274_, v_stop_275_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_array_uget_borrowed(v_as_273_, v_i_274_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_ctorName_292_; lean_object* v_params_293_; lean_object* v_code_294_; lean_object* v___x_295_; 
v_ctorName_292_ = lean_ctor_get(v___x_291_, 0);
v_params_293_ = lean_ctor_get(v___x_291_, 1);
v_code_294_ = lean_ctor_get(v___x_291_, 2);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc_ref(v_params_293_);
lean_inc(v_ctorName_292_);
lean_inc(v_discr_272_);
v___x_295_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_272_, v_ctorName_292_, v_params_293_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___x_295_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc_ref(v_code_294_);
v___x_297_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_294_, v___y_277_, v_a_296_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_297_;
goto v___jp_284_;
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v_discr_272_);
v_a_298_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_295_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_295_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_code_306_; lean_object* v___x_307_; 
v_code_306_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc_ref(v_code_306_);
v___x_307_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_306_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
v___y_285_ = v___x_307_;
goto v___jp_284_;
}
}
else
{
lean_object* v___x_308_; 
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v_discr_272_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v_b_276_);
return v___x_308_;
}
v___jp_284_:
{
if (lean_obj_tag(v___y_285_) == 0)
{
lean_object* v_a_286_; size_t v___x_287_; size_t v___x_288_; 
v_a_286_ = lean_ctor_get(v___y_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref(v___y_285_);
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_i_274_, v___x_287_);
v_i_274_ = v___x_288_;
v_b_276_ = v_a_286_;
goto _start;
}
else
{
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v_discr_272_);
return v___y_285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(lean_object* v_discr_309_, lean_object* v_as_310_, lean_object* v_i_311_, lean_object* v_stop_312_, lean_object* v_b_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
size_t v_i_boxed_321_; size_t v_stop_boxed_322_; lean_object* v_res_323_; 
v_i_boxed_321_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_stop_boxed_322_ = lean_unbox_usize(v_stop_312_);
lean_dec(v_stop_312_);
v_res_323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_309_, v_as_310_, v_i_boxed_321_, v_stop_boxed_322_, v_b_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_314_);
lean_dec_ref(v_as_310_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(lean_object* v_code_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_325_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(lean_object* v_00_u03b4_333_, lean_object* v_t_334_, lean_object* v_k_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_334_, v_k_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(lean_object* v_00_u03b4_337_, lean_object* v_t_338_, lean_object* v_k_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(v_00_u03b4_337_, v_t_338_, v_k_339_);
lean_dec(v_k_339_);
lean_dec(v_t_338_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1);
v___x_345_ = lean_box(1);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(lean_object* v_code_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_box(1);
v___x_354_ = lean_st_mk_ref(v___x_353_);
v___x_355_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_356_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_347_, v___x_354_, v___x_355_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_364_; 
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; 
v_unused_365_ = lean_ctor_get(v___x_356_, 0);
lean_dec(v_unused_365_);
v___x_358_ = v___x_356_;
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
else
{
lean_dec(v___x_356_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_st_ref_get(v___x_354_);
lean_dec(v___x_354_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v___x_354_);
v_a_366_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_356_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_356_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(lean_object* v_code_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
return v_res_380_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Array_instInhabited(lean_box(0));
return v___x_381_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1(void){
_start:
{
uint8_t v___x_382_; lean_object* v___x_383_; 
v___x_382_ = 0;
v___x_383_ = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(v___x_382_);
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
v___x_388_ = lean_panic_fn(v___x_387_, v_msg_384_);
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
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_bs_441_);
return v___x_450_;
}
else
{
uint8_t v___x_451_; lean_object* v_v_452_; lean_object* v___x_453_; 
v___x_451_ = 0;
v_v_452_ = lean_array_uget_borrowed(v_bs_441_, v_i_440_);
lean_inc(v___y_447_);
lean_inc_ref(v___y_446_);
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
lean_inc(v___y_443_);
lean_inc(v_v_452_);
v___x_453_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_451_, v_v_452_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; lean_object* v_bs_x27_456_; size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref(v___x_453_);
v___x_455_ = lean_unsigned_to_nat(0u);
v_bs_x27_456_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_455_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_add(v_i_440_, v___x_457_);
v___x_459_ = lean_array_uset(v_bs_x27_456_, v_i_440_, v_a_454_);
v_i_440_ = v___x_458_;
v_bs_441_ = v___x_459_;
goto _start;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v_bs_441_);
v_a_461_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_453_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_453_);
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
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; uint8_t v___y_5699__boxed_481_; lean_object* v_res_482_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_469_);
lean_dec(v_sz_469_);
v_i_boxed_480_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v___y_5699__boxed_481_ = lean_unbox(v___y_472_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_boxed_479_, v_i_boxed_480_, v_bs_471_, v___y_5699__boxed_481_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
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
uint8_t v___y_5757__boxed_524_; lean_object* v_res_525_; 
v___y_5757__boxed_524_ = lean_unbox(v___y_517_);
v_res_525_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_514_, v_____r_515_, v_paramsNew_516_, v___y_5757__boxed_524_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
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
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
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
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc(v___x_568_);
v___x_570_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_567_, v___x_568_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
v___x_572_ = lean_array_push(v_b_532_, v_a_571_);
v_a_541_ = v___x_572_;
goto v___jp_540_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
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
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc_ref(v_fields_530_);
v___x_582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_530_, v___x_581_, v_b_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v___y_546_ = v___x_582_;
goto v___jp_545_;
}
else
{
lean_object* v___x_583_; 
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc(v___x_568_);
v___x_583_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_567_, v___x_568_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref(v___x_583_);
v___x_585_ = lean_array_push(v_b_532_, v_a_584_);
v___x_586_ = lean_box(0);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc_ref(v_fields_530_);
v___x_587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_530_, v___x_586_, v___x_585_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
v___y_546_ = v___x_587_;
goto v___jp_545_;
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
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
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec(v_a_531_);
lean_dec_ref(v_fields_530_);
v_a_551_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_a_551_);
lean_dec_ref(v_a_547_);
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
lean_dec_ref(v_a_547_);
v_a_541_ = v_a_555_;
goto v___jp_540_;
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
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
uint8_t v___y_5821__boxed_610_; uint8_t v___y_5822__boxed_611_; lean_object* v_res_612_; 
v___y_5821__boxed_610_ = lean_unbox(v___y_599_);
v___y_5822__boxed_611_ = lean_unbox(v___y_603_);
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_596_, v_params_597_, v_targetParamIdx_598_, v___y_5821__boxed_610_, v_fields_600_, v_a_601_, v_b_602_, v___y_5822__boxed_611_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
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
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_bs_615_);
return v___x_624_;
}
else
{
uint8_t v___x_625_; lean_object* v_v_626_; lean_object* v___x_627_; 
v___x_625_ = 0;
v_v_626_ = lean_array_uget_borrowed(v_bs_615_, v_i_614_);
lean_inc(v___y_621_);
lean_inc_ref(v___y_620_);
lean_inc(v___y_619_);
lean_inc_ref(v___y_618_);
lean_inc(v___y_617_);
lean_inc(v_v_626_);
v___x_627_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_625_, v_v_626_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_629_; lean_object* v_bs_x27_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___x_627_);
v___x_629_ = lean_unsigned_to_nat(0u);
v_bs_x27_630_ = lean_array_uset(v_bs_615_, v_i_614_, v___x_629_);
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_614_, v___x_631_);
v___x_633_ = lean_array_uset(v_bs_x27_630_, v_i_614_, v_a_628_);
v_i_614_ = v___x_632_;
v_bs_615_ = v___x_633_;
goto _start;
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v_bs_615_);
v_a_635_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_627_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_627_);
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
size_t v_sz_boxed_653_; size_t v_i_boxed_654_; uint8_t v___y_5959__boxed_655_; lean_object* v_res_656_; 
v_sz_boxed_653_ = lean_unbox_usize(v_sz_643_);
lean_dec(v_sz_643_);
v_i_boxed_654_ = lean_unbox_usize(v_i_644_);
lean_dec(v_i_644_);
v___y_5959__boxed_655_ = lean_unbox(v___y_646_);
v_res_656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_boxed_653_, v_i_boxed_654_, v_bs_645_, v___y_5959__boxed_655_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
return v_res_656_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0(void){
_start:
{
uint8_t v___x_657_; lean_object* v___x_658_; 
v___x_657_ = 0;
v___x_658_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(lean_object* v_decls_664_, lean_object* v_params_665_, lean_object* v_targetParamIdx_666_, lean_object* v_fields_667_, lean_object* v_k_668_, uint8_t v_default_669_, uint8_t v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_fvarId_680_; lean_object* v___x_681_; lean_object* v_paramsNew_682_; uint8_t v___y_684_; lean_object* v_singleton_overap_738_; lean_object* v_singleton_739_; uint8_t v___x_740_; 
v___x_677_ = 0;
v___x_678_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0);
v___x_679_ = lean_array_get_borrowed(v___x_678_, v_params_665_, v_targetParamIdx_666_);
v_fvarId_680_ = lean_ctor_get(v___x_679_, 0);
v___x_681_ = lean_unsigned_to_nat(0u);
v_paramsNew_682_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
v_singleton_overap_738_ = l_Lean_instSingletonFVarIdFVarIdSet;
lean_inc(v_fvarId_680_);
v_singleton_739_ = lean_apply_1(v_singleton_overap_738_, v_fvarId_680_);
v___x_740_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_677_, v_k_668_, v_singleton_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_decls_664_);
v___x_742_ = lean_nat_dec_lt(v___x_681_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v_singleton_739_);
v___y_684_ = v___x_740_;
goto v___jp_683_;
}
else
{
if (v___x_742_ == 0)
{
lean_dec(v_singleton_739_);
v___y_684_ = v___x_740_;
goto v___jp_683_;
}
else
{
size_t v___x_743_; size_t v___x_744_; uint8_t v___x_745_; 
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_741_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_739_, v_decls_664_, v___x_743_, v___x_744_);
lean_dec(v_singleton_739_);
v___y_684_ = v___x_745_;
goto v___jp_683_;
}
}
}
else
{
lean_dec(v_singleton_739_);
v___y_684_ = v___x_740_;
goto v___jp_683_;
}
v___jp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_array_get_size(v_params_665_);
lean_inc(v_a_675_);
lean_inc_ref(v_a_674_);
lean_inc(v_a_673_);
lean_inc_ref(v_a_672_);
lean_inc(v_a_671_);
v___x_686_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v___x_685_, v_params_665_, v_targetParamIdx_666_, v___y_684_, v_fields_667_, v___x_681_, v_paramsNew_682_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; size_t v_sz_688_; size_t v___x_689_; lean_object* v___x_690_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v___x_686_);
v_sz_688_ = lean_array_size(v_decls_664_);
v___x_689_ = ((size_t)0ULL);
lean_inc(v_a_675_);
lean_inc_ref(v_a_674_);
lean_inc(v_a_673_);
lean_inc_ref(v_a_672_);
lean_inc(v_a_671_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_688_, v___x_689_, v_decls_664_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v___x_690_);
lean_inc(v_a_675_);
lean_inc_ref(v_a_674_);
lean_inc(v_a_673_);
lean_inc_ref(v_a_672_);
v___x_692_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(v___x_677_, v_k_668_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref(v___x_692_);
v___x_694_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_677_, v_a_691_, v_a_693_);
lean_dec(v_a_691_);
v___x_695_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3));
v___x_696_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(v___x_677_, v_a_687_, v___x_694_, v___x_695_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_705_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_701_, 0, v_a_697_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*1, v_default_669_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*1 + 1, v___y_684_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_696_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_696_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_a_691_);
lean_dec(v_a_687_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
v_a_714_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_692_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_692_);
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
lean_dec(v_a_687_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_k_668_);
v_a_722_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_690_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_690_);
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
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_k_668_);
lean_dec_ref(v_decls_664_);
v_a_730_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_686_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_686_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(lean_object* v_decls_746_, lean_object* v_params_747_, lean_object* v_targetParamIdx_748_, lean_object* v_fields_749_, lean_object* v_k_750_, lean_object* v_default_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
uint8_t v_default_boxed_759_; uint8_t v_a_6028__boxed_760_; lean_object* v_res_761_; 
v_default_boxed_759_ = lean_unbox(v_default_751_);
v_a_6028__boxed_760_ = lean_unbox(v_a_752_);
v_res_761_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_746_, v_params_747_, v_targetParamIdx_748_, v_fields_749_, v_k_750_, v_default_boxed_759_, v_a_6028__boxed_760_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_targetParamIdx_748_);
lean_dec_ref(v_params_747_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(lean_object* v_upperBound_762_, lean_object* v_params_763_, lean_object* v_targetParamIdx_764_, uint8_t v___y_765_, lean_object* v_fields_766_, lean_object* v_inst_767_, lean_object* v_R_768_, lean_object* v_a_769_, lean_object* v_b_770_, lean_object* v_c_771_, uint8_t v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_762_, v_params_763_, v_targetParamIdx_764_, v___y_765_, v_fields_766_, v_a_769_, v_b_770_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_780_ = _args[0];
lean_object* v_params_781_ = _args[1];
lean_object* v_targetParamIdx_782_ = _args[2];
lean_object* v___y_783_ = _args[3];
lean_object* v_fields_784_ = _args[4];
lean_object* v_inst_785_ = _args[5];
lean_object* v_R_786_ = _args[6];
lean_object* v_a_787_ = _args[7];
lean_object* v_b_788_ = _args[8];
lean_object* v_c_789_ = _args[9];
lean_object* v___y_790_ = _args[10];
lean_object* v___y_791_ = _args[11];
lean_object* v___y_792_ = _args[12];
lean_object* v___y_793_ = _args[13];
lean_object* v___y_794_ = _args[14];
lean_object* v___y_795_ = _args[15];
lean_object* v___y_796_ = _args[16];
_start:
{
uint8_t v___y_6184__boxed_797_; uint8_t v___y_6186__boxed_798_; lean_object* v_res_799_; 
v___y_6184__boxed_797_ = lean_unbox(v___y_783_);
v___y_6186__boxed_798_ = lean_unbox(v___y_790_);
v_res_799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(v_upperBound_780_, v_params_781_, v_targetParamIdx_782_, v___y_6184__boxed_797_, v_fields_784_, v_inst_785_, v_R_786_, v_a_787_, v_b_788_, v_c_789_, v___y_6186__boxed_798_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v_targetParamIdx_782_);
lean_dec_ref(v_params_781_);
lean_dec(v_upperBound_780_);
return v_res_799_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_box(0);
v___x_801_ = lean_unsigned_to_nat(16u);
v___x_802_ = lean_mk_array(v___x_801_, v___x_800_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(lean_object* v_decls_806_, lean_object* v_params_807_, lean_object* v_targetParamIdx_808_, lean_object* v_fields_809_, lean_object* v_k_810_, uint8_t v_default_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; 
v___x_817_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1);
v___x_818_ = lean_st_mk_ref(v___x_817_);
v___x_819_ = 0;
lean_inc(v___x_818_);
v___x_820_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_806_, v_params_807_, v_targetParamIdx_808_, v_fields_809_, v_k_810_, v_default_811_, v___x_819_, v___x_818_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_st_ref_get(v___x_818_);
lean_dec(v___x_818_);
lean_dec(v___x_825_);
if (v_isShared_824_ == 0)
{
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_821_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_dec(v___x_818_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(lean_object* v_decls_830_, lean_object* v_params_831_, lean_object* v_targetParamIdx_832_, lean_object* v_fields_833_, lean_object* v_k_834_, lean_object* v_default_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
uint8_t v_default_boxed_841_; lean_object* v_res_842_; 
v_default_boxed_841_ = lean_unbox(v_default_835_);
v_res_842_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_decls_830_, v_params_831_, v_targetParamIdx_832_, v_fields_833_, v_k_834_, v_default_boxed_841_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
lean_dec(v_targetParamIdx_832_);
lean_dec_ref(v_params_831_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(lean_object* v_args_843_, lean_object* v_targetParamIdx_844_, lean_object* v_fields_845_, uint8_t v_dependsOnTarget_846_){
_start:
{
if (v_dependsOnTarget_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_lower_852_; lean_object* v_upper_853_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_847_ = lean_unsigned_to_nat(0u);
lean_inc(v_targetParamIdx_844_);
lean_inc_ref(v_args_843_);
v___x_848_ = l_Array_toSubarray___redArg(v_args_843_, v___x_847_, v_targetParamIdx_844_);
v___x_849_ = l_Subarray_copy___redArg(v___x_848_);
v___x_850_ = l_Array_append___redArg(v___x_849_, v_fields_845_);
v___x_857_ = lean_array_get_size(v_args_843_);
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_nat_add(v_targetParamIdx_844_, v___x_858_);
lean_dec(v_targetParamIdx_844_);
v___x_860_ = lean_nat_dec_le(v___x_859_, v___x_847_);
if (v___x_860_ == 0)
{
v_lower_852_ = v___x_859_;
v_upper_853_ = v___x_857_;
goto v___jp_851_;
}
else
{
lean_dec(v___x_859_);
v_lower_852_ = v___x_847_;
v_upper_853_ = v___x_857_;
goto v___jp_851_;
}
v___jp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = l_Array_toSubarray___redArg(v_args_843_, v_lower_852_, v_upper_853_);
v___x_855_ = l_Subarray_copy___redArg(v___x_854_);
v___x_856_ = l_Array_append___redArg(v___x_850_, v___x_855_);
lean_dec_ref(v___x_855_);
return v___x_856_;
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_lower_868_; lean_object* v_upper_869_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_targetParamIdx_844_, v___x_862_);
lean_dec(v_targetParamIdx_844_);
lean_inc(v___x_863_);
lean_inc_ref(v_args_843_);
v___x_864_ = l_Array_toSubarray___redArg(v_args_843_, v___x_861_, v___x_863_);
v___x_865_ = l_Subarray_copy___redArg(v___x_864_);
v___x_866_ = l_Array_append___redArg(v___x_865_, v_fields_845_);
v___x_873_ = lean_array_get_size(v_args_843_);
v___x_874_ = lean_nat_dec_le(v___x_863_, v___x_861_);
if (v___x_874_ == 0)
{
v_lower_868_ = v___x_863_;
v_upper_869_ = v___x_873_;
goto v___jp_867_;
}
else
{
lean_dec(v___x_863_);
v_lower_868_ = v___x_861_;
v_upper_869_ = v___x_873_;
goto v___jp_867_;
}
v___jp_867_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = l_Array_toSubarray___redArg(v_args_843_, v_lower_868_, v_upper_869_);
v___x_871_ = l_Subarray_copy___redArg(v___x_870_);
v___x_872_ = l_Array_append___redArg(v___x_866_, v___x_871_);
lean_dec_ref(v___x_871_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(lean_object* v_args_875_, lean_object* v_targetParamIdx_876_, lean_object* v_fields_877_, lean_object* v_dependsOnTarget_878_){
_start:
{
uint8_t v_dependsOnTarget_boxed_879_; lean_object* v_res_880_; 
v_dependsOnTarget_boxed_879_ = lean_unbox(v_dependsOnTarget_878_);
v_res_880_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_875_, v_targetParamIdx_876_, v_fields_877_, v_dependsOnTarget_boxed_879_);
lean_dec_ref(v_fields_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(size_t v_sz_881_, size_t v_i_882_, lean_object* v_bs_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = lean_usize_dec_lt(v_i_882_, v_sz_881_);
if (v___x_884_ == 0)
{
return v_bs_883_;
}
else
{
lean_object* v_v_885_; lean_object* v_fvarId_886_; lean_object* v___x_887_; lean_object* v_bs_x27_888_; lean_object* v___x_889_; size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v_v_885_ = lean_array_uget_borrowed(v_bs_883_, v_i_882_);
v_fvarId_886_ = lean_ctor_get(v_v_885_, 0);
lean_inc(v_fvarId_886_);
v___x_887_ = lean_unsigned_to_nat(0u);
v_bs_x27_888_ = lean_array_uset(v_bs_883_, v_i_882_, v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_889_, 0, v_fvarId_886_);
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_add(v_i_882_, v___x_890_);
v___x_892_ = lean_array_uset(v_bs_x27_888_, v_i_882_, v___x_889_);
v_i_882_ = v___x_891_;
v_bs_883_ = v___x_892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_bs_896_){
_start:
{
size_t v_sz_boxed_897_; size_t v_i_boxed_898_; lean_object* v_res_899_; 
v_sz_boxed_897_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_898_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_boxed_897_, v_i_boxed_898_, v_bs_896_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(size_t v_sz_900_, size_t v_i_901_, lean_object* v_bs_902_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_903_ == 0)
{
return v_bs_902_;
}
else
{
lean_object* v_v_904_; lean_object* v_fvarId_905_; lean_object* v___x_906_; lean_object* v_bs_x27_907_; lean_object* v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_v_904_ = lean_array_uget_borrowed(v_bs_902_, v_i_901_);
v_fvarId_905_ = lean_ctor_get(v_v_904_, 0);
lean_inc(v_fvarId_905_);
v___x_906_ = lean_unsigned_to_nat(0u);
v_bs_x27_907_ = lean_array_uset(v_bs_902_, v_i_901_, v___x_906_);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v_fvarId_905_);
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_901_, v___x_909_);
v___x_911_ = lean_array_uset(v_bs_x27_907_, v_i_901_, v___x_908_);
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_900_, v___x_910_, v___x_911_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(lean_object* v_sz_913_, lean_object* v_i_914_, lean_object* v_bs_915_){
_start:
{
size_t v_sz_boxed_916_; size_t v_i_boxed_917_; lean_object* v_res_918_; 
v_sz_boxed_916_ = lean_unbox_usize(v_sz_913_);
lean_dec(v_sz_913_);
v_i_boxed_917_ = lean_unbox_usize(v_i_914_);
lean_dec(v_i_914_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_boxed_916_, v_i_boxed_917_, v_bs_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(lean_object* v_params_919_, lean_object* v_targetParamIdx_920_, lean_object* v_fields_921_, uint8_t v_dependsOnTarget_922_){
_start:
{
size_t v_sz_923_; size_t v___x_924_; lean_object* v___x_925_; size_t v_sz_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_sz_923_ = lean_array_size(v_params_919_);
v___x_924_ = ((size_t)0ULL);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_923_, v___x_924_, v_params_919_);
v_sz_926_ = lean_array_size(v_fields_921_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_926_, v___x_924_, v_fields_921_);
v___x_928_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v___x_925_, v_targetParamIdx_920_, v___x_927_, v_dependsOnTarget_922_);
lean_dec_ref(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(lean_object* v_params_929_, lean_object* v_targetParamIdx_930_, lean_object* v_fields_931_, lean_object* v_dependsOnTarget_932_){
_start:
{
uint8_t v_dependsOnTarget_boxed_933_; lean_object* v_res_934_; 
v_dependsOnTarget_boxed_933_ = lean_unbox(v_dependsOnTarget_932_);
v_res_934_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_929_, v_targetParamIdx_930_, v_fields_931_, v_dependsOnTarget_boxed_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(lean_object* v_fvarId_940_, lean_object* v_args_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_st_ref_get(v_a_943_);
v___x_951_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_950_, v_fvarId_940_);
lean_dec(v___x_950_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_1134_; 
v_val_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_1134_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_1134_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_942_, v_fvarId_940_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_954_);
v_val_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_1129_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1129_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_paramIdx_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1127_; 
v_paramIdx_961_ = lean_ctor_get(v_val_957_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_val_957_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_val_957_, 1);
lean_dec(v_unused_1128_);
v___x_963_ = v_val_957_;
v_isShared_964_ = v_isSharedCheck_1127_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_paramIdx_961_);
lean_dec(v_val_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1127_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_box(0);
v___x_966_ = lean_array_get(v___x_965_, v_args_941_, v_paramIdx_961_);
if (lean_obj_tag(v___x_966_) == 1)
{
lean_object* v_fvarId_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1122_; 
lean_del_object(v___x_959_);
v_fvarId_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_1122_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_fvarId_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1122_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_967_, v_a_944_, v_a_946_, v_a_948_);
lean_dec(v_fvarId_967_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1113_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_1113_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1113_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
if (lean_obj_tag(v_a_972_) == 1)
{
lean_object* v_val_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1108_; 
v_val_976_ = lean_ctor_get(v_a_972_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_978_ = v_a_972_;
v_isShared_979_ = v_isSharedCheck_1108_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_val_976_);
lean_dec(v_a_972_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1108_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_976_);
v___x_981_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_952_, v___x_980_);
lean_dec(v___x_980_);
lean_dec(v_val_952_);
if (lean_obj_tag(v___x_981_) == 1)
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1103_; 
v_val_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1103_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1103_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
uint8_t v_default_986_; 
v_default_986_ = lean_ctor_get_uint8(v_val_982_, sizeof(void*)*1);
if (v_default_986_ == 0)
{
if (lean_obj_tag(v_val_976_) == 0)
{
lean_object* v_decl_987_; uint8_t v_dependsOnDiscr_988_; lean_object* v_val_989_; lean_object* v_args_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1025_; 
lean_del_object(v___x_978_);
lean_del_object(v___x_969_);
lean_del_object(v___x_963_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
v_decl_987_ = lean_ctor_get(v_val_982_, 0);
lean_inc_ref(v_decl_987_);
v_dependsOnDiscr_988_ = lean_ctor_get_uint8(v_val_982_, sizeof(void*)*1 + 1);
lean_dec(v_val_982_);
v_val_989_ = lean_ctor_get(v_val_976_, 0);
v_args_990_ = lean_ctor_get(v_val_976_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_val_976_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_992_ = v_val_976_;
v_isShared_993_ = v_isSharedCheck_1025_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_args_990_);
lean_inc(v_val_989_);
lean_dec(v_val_976_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1025_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___y_995_; lean_object* v_numParams_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_numParams_1015_ = lean_ctor_get(v_val_989_, 3);
lean_inc(v_numParams_1015_);
lean_dec_ref(v_val_989_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_array_get_size(v_args_990_);
v___x_1018_ = lean_nat_dec_le(v_numParams_1015_, v___x_1016_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1020_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_1017_);
lean_ctor_set(v___x_992_, 0, v_numParams_1015_);
v___x_1020_ = v___x_992_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_numParams_1015_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1017_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
v___y_995_ = v___x_1020_;
goto v___jp_994_;
}
}
else
{
lean_object* v___x_1023_; 
lean_dec(v_numParams_1015_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_1017_);
lean_ctor_set(v___x_992_, 0, v___x_1016_);
v___x_1023_ = v___x_992_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_1017_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v___y_995_ = v___x_1023_;
goto v___jp_994_;
}
}
v___jp_994_:
{
lean_object* v_fvarId_996_; lean_object* v_lower_997_; lean_object* v_upper_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1014_; 
v_fvarId_996_ = lean_ctor_get(v_decl_987_, 0);
lean_inc(v_fvarId_996_);
lean_dec_ref(v_decl_987_);
v_lower_997_ = lean_ctor_get(v___y_995_, 0);
v_upper_998_ = lean_ctor_get(v___y_995_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___y_995_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1000_ = v___y_995_;
v_isShared_1001_ = v_isSharedCheck_1014_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_upper_998_);
lean_inc(v_lower_997_);
lean_dec(v___y_995_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1014_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1002_ = l_Array_toSubarray___redArg(v_args_990_, v_lower_997_, v_upper_998_);
v___x_1003_ = l_Subarray_copy___redArg(v___x_1002_);
v___x_1004_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_941_, v_paramIdx_961_, v___x_1003_, v_dependsOnDiscr_988_);
lean_dec_ref(v___x_1003_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 3);
lean_ctor_set(v___x_1000_, 1, v___x_1004_);
lean_ctor_set(v___x_1000_, 0, v_fvarId_996_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_fvarId_996_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_1006_);
v___x_1008_ = v___x_984_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_1008_);
v___x_1010_ = v___x_974_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
}
else
{
lean_object* v_decl_1026_; uint8_t v_dependsOnDiscr_1027_; lean_object* v_n_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1088_; 
v_decl_1026_ = lean_ctor_get(v_val_982_, 0);
lean_inc_ref(v_decl_1026_);
v_dependsOnDiscr_1027_ = lean_ctor_get_uint8(v_val_982_, sizeof(void*)*1 + 1);
lean_dec(v_val_982_);
v_n_1028_ = lean_ctor_get(v_val_976_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_val_976_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1030_ = v_val_976_;
v_isShared_1031_ = v_isSharedCheck_1088_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_n_1028_);
lean_dec(v_val_976_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1088_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_zero_1032_; uint8_t v_isZero_1033_; 
v_zero_1032_ = lean_unsigned_to_nat(0u);
v_isZero_1033_ = lean_nat_dec_eq(v_n_1028_, v_zero_1032_);
if (v_isZero_1033_ == 1)
{
lean_object* v_fvarId_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_del_object(v___x_1030_);
lean_dec(v_n_1028_);
lean_del_object(v___x_978_);
lean_del_object(v___x_969_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
v_fvarId_1034_ = lean_ctor_get(v_decl_1026_, 0);
lean_inc(v_fvarId_1034_);
lean_dec_ref(v_decl_1026_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1036_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_941_, v_paramIdx_961_, v___x_1035_, v_dependsOnDiscr_1027_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 3);
lean_ctor_set(v___x_963_, 1, v___x_1036_);
lean_ctor_set(v___x_963_, 0, v_fvarId_1034_);
v___x_1038_ = v___x_963_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_fvarId_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_1038_);
v___x_1040_ = v___x_984_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_1040_);
v___x_1042_ = v___x_974_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
uint8_t v___x_1046_; lean_object* v_one_1047_; lean_object* v_n_1048_; lean_object* v___x_1050_; 
lean_del_object(v___x_974_);
v___x_1046_ = 0;
v_one_1047_ = lean_unsigned_to_nat(1u);
v_n_1048_ = lean_nat_sub(v_n_1028_, v_one_1047_);
lean_dec(v_n_1028_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
lean_ctor_set(v___x_1030_, 0, v_n_1048_);
v___x_1050_ = v___x_1030_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_n_1048_);
v___x_1050_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 0);
lean_ctor_set(v___x_978_, 0, v___x_1050_);
v___x_1052_ = v___x_978_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2));
v___x_1054_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1046_, v___x_1052_, v___x_1053_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1077_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1077_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1077_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_fvarId_1059_; lean_object* v_fvarId_1060_; lean_object* v___x_1062_; 
v_fvarId_1059_ = lean_ctor_get(v_decl_1026_, 0);
lean_inc(v_fvarId_1059_);
lean_dec_ref(v_decl_1026_);
v_fvarId_1060_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_fvarId_1060_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_fvarId_1060_);
v___x_1062_ = v___x_969_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_fvarId_1060_);
v___x_1062_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1063_ = lean_mk_empty_array_with_capacity(v_one_1047_);
v___x_1064_ = lean_array_push(v___x_1063_, v___x_1062_);
v___x_1065_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_941_, v_paramIdx_961_, v___x_1064_, v_dependsOnDiscr_1027_);
lean_dec_ref(v___x_1064_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 3);
lean_ctor_set(v___x_963_, 1, v___x_1065_);
lean_ctor_set(v___x_963_, 0, v_fvarId_1059_);
v___x_1067_ = v___x_963_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_fvarId_1059_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_a_1055_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_1068_);
v___x_1070_ = v___x_984_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1070_);
v___x_1072_ = v___x_1057_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_decl_1026_);
lean_del_object(v___x_984_);
lean_del_object(v___x_969_);
lean_del_object(v___x_963_);
lean_dec(v_paramIdx_961_);
lean_dec_ref(v_args_941_);
v_a_1078_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1054_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1054_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
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
lean_object* v_decl_1089_; uint8_t v_dependsOnDiscr_1090_; lean_object* v_fvarId_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_del_object(v___x_978_);
lean_dec(v_val_976_);
lean_del_object(v___x_969_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
v_decl_1089_ = lean_ctor_get(v_val_982_, 0);
lean_inc_ref(v_decl_1089_);
v_dependsOnDiscr_1090_ = lean_ctor_get_uint8(v_val_982_, sizeof(void*)*1 + 1);
lean_dec(v_val_982_);
v_fvarId_1091_ = lean_ctor_get(v_decl_1089_, 0);
lean_inc(v_fvarId_1091_);
lean_dec_ref(v_decl_1089_);
v___x_1092_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0));
v___x_1093_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_941_, v_paramIdx_961_, v___x_1092_, v_dependsOnDiscr_1090_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 3);
lean_ctor_set(v___x_963_, 1, v___x_1093_);
lean_ctor_set(v___x_963_, 0, v_fvarId_1091_);
v___x_1095_ = v___x_963_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_fvarId_1091_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_1095_);
v___x_1097_ = v___x_984_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_1097_);
v___x_1099_ = v___x_974_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v___x_981_);
lean_del_object(v___x_978_);
lean_dec(v_val_976_);
lean_del_object(v___x_969_);
lean_del_object(v___x_963_);
lean_dec(v_paramIdx_961_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_args_941_);
v___x_1104_ = lean_box(0);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_1104_);
v___x_1106_ = v___x_974_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
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
else
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
lean_dec(v_a_972_);
lean_del_object(v___x_969_);
lean_del_object(v___x_963_);
lean_dec(v_paramIdx_961_);
lean_dec(v_val_952_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_args_941_);
v___x_1109_ = lean_box(0);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_1109_);
v___x_1111_ = v___x_974_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_del_object(v___x_969_);
lean_del_object(v___x_963_);
lean_dec(v_paramIdx_961_);
lean_dec(v_val_952_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_args_941_);
v_a_1114_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_971_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_971_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_dec(v___x_966_);
lean_del_object(v___x_963_);
lean_dec(v_paramIdx_961_);
lean_dec(v_val_952_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_args_941_);
v___x_1123_ = lean_box(0);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 0);
lean_ctor_set(v___x_959_, 0, v___x_1123_);
v___x_1125_ = v___x_959_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v___x_956_);
lean_dec(v_val_952_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_args_941_);
v___x_1130_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 0);
lean_ctor_set(v___x_954_, 0, v___x_1130_);
v___x_1132_ = v___x_954_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v___x_951_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_args_941_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(lean_object* v_fvarId_1137_, lean_object* v_args_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1137_, v_args_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec(v_fvarId_1137_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(lean_object* v___x_1148_, lean_object* v_init_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
lean_object* v_k_1151_; lean_object* v_l_1152_; lean_object* v_r_1153_; lean_object* v___x_1154_; 
v_k_1151_ = lean_ctor_get(v_x_1150_, 1);
v_l_1152_ = lean_ctor_get(v_x_1150_, 3);
v_r_1153_ = lean_ctor_get(v_x_1150_, 4);
v___x_1154_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1148_, v_init_1149_, v_l_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
return v___x_1154_;
}
else
{
uint8_t v___x_1155_; 
lean_dec_ref(v___x_1154_);
v___x_1155_ = l_Lean_NameSet_contains(v___x_1148_, v_k_1151_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2));
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v_init_1149_ = v___x_1157_;
v_x_1150_ = v_r_1153_;
goto _start;
}
}
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v_init_1149_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(lean_object* v___x_1160_, lean_object* v_init_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1160_, v_init_1161_, v_x_1162_);
lean_dec(v_x_1162_);
lean_dec(v___x_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(lean_object* v___x_1164_, lean_object* v_a_1165_, lean_object* v_init_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v_d_1170_; 
if (lean_obj_tag(v_x_1167_) == 0)
{
lean_object* v_k_1173_; lean_object* v_l_1174_; lean_object* v_r_1175_; lean_object* v___x_1176_; lean_object* v_a_1177_; 
v_k_1173_ = lean_ctor_get(v_x_1167_, 1);
lean_inc(v_k_1173_);
v_l_1174_ = lean_ctor_get(v_x_1167_, 3);
lean_inc(v_l_1174_);
v_r_1175_ = lean_ctor_get(v_x_1167_, 4);
lean_inc(v_r_1175_);
lean_dec_ref(v_x_1167_);
lean_inc_ref(v_a_1165_);
v___x_1176_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1164_, v_a_1165_, v_init_1166_, v_l_1174_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
if (lean_obj_tag(v_a_1177_) == 0)
{
lean_object* v_a_1178_; 
lean_dec_ref(v___x_1176_);
lean_dec(v_r_1175_);
lean_dec(v_k_1173_);
lean_dec_ref(v_a_1165_);
v_a_1178_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v_a_1177_);
v_d_1170_ = v_a_1178_;
goto v___jp_1169_;
}
else
{
lean_object* v_a_1179_; uint8_t v___x_1180_; 
v_a_1179_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v_a_1177_);
v___x_1180_ = l_Lean_NameSet_contains(v___x_1164_, v_k_1173_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec_ref(v___x_1176_);
lean_inc_ref(v_a_1165_);
v___x_1181_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1173_, v_a_1165_, v_a_1179_);
v_init_1166_ = v___x_1181_;
v_x_1167_ = v_r_1175_;
goto _start;
}
else
{
lean_object* v_a_1183_; 
lean_dec(v_a_1179_);
lean_dec(v_k_1173_);
v_a_1183_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1176_);
if (lean_obj_tag(v_a_1183_) == 0)
{
lean_object* v_a_1184_; 
lean_dec(v_r_1175_);
lean_dec_ref(v_a_1165_);
v_a_1184_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref(v_a_1183_);
v_d_1170_ = v_a_1184_;
goto v___jp_1169_;
}
else
{
lean_object* v_a_1185_; 
v_a_1185_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v_a_1183_);
v_init_1166_ = v_a_1185_;
v_x_1167_ = v_r_1175_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_a_1165_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_init_1166_);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
v___jp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_d_1170_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(lean_object* v___x_1189_, lean_object* v_a_1190_, lean_object* v_init_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1189_, v_a_1190_, v_init_1191_, v_x_1192_);
lean_dec(v___x_1189_);
return v_res_1194_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0));
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0);
v___x_1198_ = lean_box(1);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(lean_object* v_discr_1200_, lean_object* v___x_1201_, lean_object* v_val_1202_, lean_object* v_fst_1203_, lean_object* v_params_1204_, lean_object* v_snd_1205_, lean_object* v_as_1206_, size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_a_1219_; uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_b_1209_);
return v___x_1224_;
}
else
{
lean_object* v_snd_1225_; lean_object* v_fst_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1384_; 
v_snd_1225_ = lean_ctor_get(v_b_1209_, 1);
v_fst_1226_ = lean_ctor_get(v_b_1209_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_b_1209_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1228_ = v_b_1209_;
v_isShared_1229_ = v_isSharedCheck_1384_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_snd_1225_);
lean_inc(v_fst_1226_);
lean_dec(v_b_1209_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1384_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_fst_1230_; lean_object* v_snd_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1383_; 
v_fst_1230_ = lean_ctor_get(v_snd_1225_, 0);
v_snd_1231_ = lean_ctor_get(v_snd_1225_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_snd_1225_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1233_ = v_snd_1225_;
v_isShared_1234_ = v_isSharedCheck_1383_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snd_1231_);
lean_inc(v_fst_1230_);
lean_dec(v_snd_1225_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1383_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___x_1235_; lean_object* v_a_1236_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v_a_1243_; 
v___x_1235_ = 0;
v_a_1236_ = lean_array_uget_borrowed(v_as_1206_, v_i_1208_);
if (lean_obj_tag(v_a_1236_) == 0)
{
lean_object* v_ctorName_1255_; lean_object* v_params_1256_; lean_object* v_code_1257_; lean_object* v___x_1258_; 
lean_del_object(v___x_1233_);
lean_del_object(v___x_1228_);
v_ctorName_1255_ = lean_ctor_get(v_a_1236_, 0);
v_params_1256_ = lean_ctor_get(v_a_1236_, 1);
v_code_1257_ = lean_ctor_get(v_a_1236_, 2);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc_ref(v_params_1256_);
lean_inc(v_ctorName_1255_);
lean_inc(v_discr_1200_);
v___x_1258_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1200_, v_ctorName_1255_, v_params_1256_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc_ref(v_code_1257_);
v___x_1260_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1257_, v___y_1210_, v___y_1211_, v_a_1259_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; uint8_t v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = l_Lean_NameSet_contains(v___x_1201_, v_ctorName_1255_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_inc_ref(v_a_1236_);
v___x_1263_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1236_, v_a_1261_);
v___x_1264_ = lean_array_push(v_snd_1231_, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_fst_1230_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_fst_1226_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v_a_1219_ = v___x_1266_;
goto v___jp_1218_;
}
else
{
lean_object* v_paramIdx_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; 
v_paramIdx_1267_ = lean_ctor_get(v_val_1202_, 0);
v___x_1268_ = 0;
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc(v_a_1261_);
lean_inc_ref(v_params_1256_);
lean_inc_ref(v_fst_1203_);
v___x_1269_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1203_, v_params_1204_, v_paramIdx_1267_, v_params_1256_, v_a_1261_, v___x_1268_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v_decl_1271_; uint8_t v_dependsOnDiscr_1272_; lean_object* v___x_1273_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v_decl_1271_ = lean_ctor_get(v_a_1270_, 0);
v_dependsOnDiscr_1272_ = lean_ctor_get_uint8(v_a_1270_, sizeof(void*)*1 + 1);
v___x_1273_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1235_, v_a_1261_, v___y_1214_);
lean_dec(v_a_1261_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_fvarId_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec_ref(v___x_1273_);
v_fvarId_1274_ = lean_ctor_get(v_decl_1271_, 0);
lean_inc(v_fvarId_1274_);
lean_inc_ref(v_decl_1271_);
v___x_1275_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_decl_1271_);
v___x_1276_ = lean_array_push(v_fst_1230_, v___x_1275_);
lean_inc(v_ctorName_1255_);
v___x_1277_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_ctorName_1255_, v_a_1270_, v_fst_1226_);
lean_inc_ref(v_params_1256_);
lean_inc(v_paramIdx_1267_);
lean_inc_ref(v_params_1204_);
v___x_1278_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1204_, v_paramIdx_1267_, v_params_1256_, v_dependsOnDiscr_1272_);
v___x_1279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_fvarId_1274_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
lean_inc_ref(v_a_1236_);
v___x_1280_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1236_, v___x_1279_);
v___x_1281_ = lean_array_push(v_snd_1231_, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1276_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1277_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v_a_1219_ = v___x_1283_;
goto v___jp_1218_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_a_1270_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec(v_fst_1226_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1284_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1273_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1273_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_a_1261_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec(v_fst_1226_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1292_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1269_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1269_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec(v_fst_1226_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1300_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1260_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1260_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_dec(v_fst_1226_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1308_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1258_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1258_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_code_1316_; lean_object* v___x_1317_; 
v_code_1316_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc_ref(v_code_1316_);
v___x_1317_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1316_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1324_; lean_object* v___y_1326_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_a_1374_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref(v___x_1317_);
v___x_1324_ = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(v_snd_1205_);
v___x_1372_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3));
v___x_1373_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_1324_, v___x_1372_, v___x_1201_);
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
v___y_1326_ = v_a_1374_;
goto v___jp_1325_;
v___jp_1319_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_inc_ref(v_a_1236_);
v___x_1320_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1236_, v_a_1318_);
v___x_1321_ = lean_array_push(v_snd_1231_, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_fst_1230_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_fst_1226_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v_a_1219_ = v___x_1323_;
goto v___jp_1218_;
}
v___jp_1325_:
{
lean_object* v_fst_1327_; 
v_fst_1327_ = lean_ctor_get(v___y_1326_, 0);
lean_inc(v_fst_1327_);
lean_dec_ref(v___y_1326_);
if (lean_obj_tag(v_fst_1327_) == 0)
{
lean_dec(v___x_1324_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1228_);
goto v___jp_1319_;
}
else
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1371_; 
v_val_1328_ = lean_ctor_get(v_fst_1327_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_fst_1327_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1330_ = v_fst_1327_;
v_isShared_1331_ = v_isSharedCheck_1371_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v_fst_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1371_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_unbox(v_val_1328_);
lean_dec(v_val_1328_);
if (v___x_1332_ == 0)
{
lean_del_object(v___x_1330_);
lean_dec(v___x_1324_);
lean_del_object(v___x_1233_);
lean_del_object(v___x_1228_);
goto v___jp_1319_;
}
else
{
lean_object* v_paramIdx_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_paramIdx_1333_ = lean_ctor_get(v_val_1202_, 0);
v___x_1334_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1));
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
lean_inc(v_a_1318_);
lean_inc_ref(v_fst_1203_);
v___x_1335_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_1203_, v_params_1204_, v_paramIdx_1333_, v___x_1334_, v_a_1318_, v___x_1223_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_decl_1337_; uint8_t v_dependsOnDiscr_1338_; lean_object* v___x_1339_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref(v___x_1335_);
v_decl_1337_ = lean_ctor_get(v_a_1336_, 0);
lean_inc_ref(v_decl_1337_);
v_dependsOnDiscr_1338_ = lean_ctor_get_uint8(v_a_1336_, sizeof(void*)*1 + 1);
v___x_1339_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1235_, v_a_1318_, v___y_1214_);
lean_dec(v_a_1318_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref(v___x_1339_);
lean_inc(v___x_1201_);
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1324_, v_a_1336_, v_fst_1226_, v___x_1201_);
lean_dec(v___x_1324_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1340_);
lean_inc_ref(v_decl_1337_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 2);
lean_ctor_set(v___x_1330_, 0, v_decl_1337_);
v___x_1343_ = v___x_1330_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_decl_1337_);
v___x_1343_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v_a_1345_; 
v___x_1344_ = lean_array_push(v_fst_1230_, v___x_1343_);
v_a_1345_ = lean_ctor_get(v_a_1341_, 0);
lean_inc(v_a_1345_);
lean_dec(v_a_1341_);
lean_inc(v_paramIdx_1333_);
v___y_1238_ = v_paramIdx_1333_;
v___y_1239_ = v___x_1334_;
v___y_1240_ = v_decl_1337_;
v___y_1241_ = v___x_1344_;
v___y_1242_ = v_dependsOnDiscr_1338_;
v_a_1243_ = v_a_1345_;
goto v___jp_1237_;
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec_ref(v_decl_1337_);
lean_del_object(v___x_1330_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_del_object(v___x_1228_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1347_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1340_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1340_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v_decl_1337_);
lean_dec(v_a_1336_);
lean_del_object(v___x_1330_);
lean_dec(v___x_1324_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_del_object(v___x_1228_);
lean_dec(v_fst_1226_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1355_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1339_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1339_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_del_object(v___x_1330_);
lean_dec(v___x_1324_);
lean_dec(v_a_1318_);
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_del_object(v___x_1228_);
lean_dec(v_fst_1226_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1363_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1335_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1335_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
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
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_del_object(v___x_1233_);
lean_dec(v_snd_1231_);
lean_dec(v_fst_1230_);
lean_del_object(v___x_1228_);
lean_dec(v_fst_1226_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_params_1204_);
lean_dec_ref(v_fst_1203_);
lean_dec_ref(v_val_1202_);
lean_dec(v___x_1201_);
lean_dec(v_discr_1200_);
v_a_1375_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1317_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1317_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
v___jp_1237_:
{
lean_object* v_fvarId_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_fvarId_1244_ = lean_ctor_get(v___y_1240_, 0);
lean_inc(v_fvarId_1244_);
lean_dec_ref(v___y_1240_);
lean_inc_ref(v_params_1204_);
v___x_1245_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_1204_, v___y_1238_, v___y_1239_, v___y_1242_);
v___x_1246_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_fvarId_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
lean_inc(v_a_1236_);
v___x_1247_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1236_, v___x_1246_);
v___x_1248_ = lean_array_push(v_snd_1231_, v___x_1247_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1248_);
lean_ctor_set(v___x_1233_, 0, v___y_1241_);
v___x_1250_ = v___x_1233_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___y_1241_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1250_);
lean_ctor_set(v___x_1228_, 0, v_a_1243_);
v___x_1252_ = v___x_1228_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v_a_1219_ = v___x_1252_;
goto v___jp_1218_;
}
}
}
}
}
}
v___jp_1218_:
{
size_t v___x_1220_; size_t v___x_1221_; 
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_add(v_i_1208_, v___x_1220_);
v_i_1208_ = v___x_1221_;
v_b_1209_ = v_a_1219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(lean_object* v_decl_1385_, lean_object* v_k_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_fvarId_1395_; lean_object* v_params_1396_; lean_object* v_type_1397_; lean_object* v_value_1398_; lean_object* v___x_1399_; 
v_fvarId_1395_ = lean_ctor_get(v_decl_1385_, 0);
v_params_1396_ = lean_ctor_get(v_decl_1385_, 2);
lean_inc_ref(v_params_1396_);
v_type_1397_ = lean_ctor_get(v_decl_1385_, 3);
lean_inc_ref(v_type_1397_);
v_value_1398_ = lean_ctor_get(v_decl_1385_, 4);
v___x_1399_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_1387_, v_fvarId_1395_);
if (lean_obj_tag(v___x_1399_) == 1)
{
lean_object* v_val_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1476_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1476_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_val_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1476_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_ctorNames_1404_; 
v_ctorNames_1404_ = lean_ctor_get(v_val_1400_, 1);
lean_inc(v_ctorNames_1404_);
if (lean_obj_tag(v_ctorNames_1404_) == 0)
{
lean_object* v___x_1405_; lean_object* v_snd_1406_; lean_object* v_fst_1407_; lean_object* v_typeName_1408_; lean_object* v_resultType_1409_; lean_object* v_discr_1410_; lean_object* v_alts_1411_; lean_object* v___x_1412_; size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1405_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_value_1398_);
v_snd_1406_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_snd_1406_);
v_fst_1407_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_fst_1407_);
lean_dec_ref(v___x_1405_);
v_typeName_1408_ = lean_ctor_get(v_snd_1406_, 0);
lean_inc(v_typeName_1408_);
v_resultType_1409_ = lean_ctor_get(v_snd_1406_, 1);
lean_inc_ref(v_resultType_1409_);
v_discr_1410_ = lean_ctor_get(v_snd_1406_, 2);
lean_inc(v_discr_1410_);
v_alts_1411_ = lean_ctor_get(v_snd_1406_, 3);
lean_inc_ref(v_alts_1411_);
v___x_1412_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1, &l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1);
v_sz_1413_ = lean_array_size(v_alts_1411_);
v___x_1414_ = ((size_t)0ULL);
lean_inc(v_a_1393_);
lean_inc_ref(v_a_1392_);
lean_inc(v_a_1391_);
lean_inc_ref(v_a_1390_);
lean_inc_ref(v_a_1389_);
lean_inc_ref(v_params_1396_);
lean_inc(v_fst_1407_);
lean_inc(v_discr_1410_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1410_, v_ctorNames_1404_, v_val_1400_, v_fst_1407_, v_params_1396_, v_snd_1406_, v_alts_1411_, v_sz_1413_, v___x_1414_, v___x_1412_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec_ref(v_alts_1411_);
lean_dec(v_snd_1406_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_fst_1422_; lean_object* v_snd_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1465_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = lean_st_ref_take(v_a_1388_);
v_fst_1418_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_fst_1418_);
v_snd_1419_ = lean_ctor_get(v_a_1416_, 1);
lean_inc(v_snd_1419_);
lean_dec(v_a_1416_);
lean_inc(v_fvarId_1395_);
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_1395_, v_fst_1418_, v___x_1417_);
v___x_1421_ = lean_st_ref_set(v_a_1388_, v___x_1420_);
v_fst_1422_ = lean_ctor_get(v_snd_1419_, 0);
v_snd_1423_ = lean_ctor_get(v_snd_1419_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_snd_1419_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1425_ = v_snd_1419_;
v_isShared_1426_ = v_isSharedCheck_1465_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_snd_1423_);
lean_inc(v_fst_1422_);
lean_dec(v_snd_1419_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1465_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1427_ = 0;
v___x_1428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1428_, 0, v_typeName_1408_);
lean_ctor_set(v___x_1428_, 1, v_resultType_1409_);
lean_ctor_set(v___x_1428_, 2, v_discr_1410_);
lean_ctor_set(v___x_1428_, 3, v_snd_1423_);
v___x_1429_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
v___x_1430_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1427_, v_fst_1407_, v___x_1429_);
lean_dec(v_fst_1407_);
v___x_1431_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1427_, v_decl_1385_, v_type_1397_, v_params_1396_, v___x_1430_, v_a_1391_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1448_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1448_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set_tag(v___x_1425_, 2);
lean_ctor_set(v___x_1425_, 1, v_a_1434_);
lean_ctor_set(v___x_1425_, 0, v_a_1432_);
v___x_1439_ = v___x_1425_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1432_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1427_, v_fst_1422_, v___x_1439_);
lean_dec(v_fst_1422_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1440_);
v___x_1442_ = v___x_1402_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1442_);
v___x_1444_ = v___x_1436_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
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
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_a_1432_);
lean_del_object(v___x_1425_);
lean_dec(v_fst_1422_);
lean_del_object(v___x_1402_);
v_a_1449_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1433_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1433_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_del_object(v___x_1425_);
lean_dec(v_fst_1422_);
lean_del_object(v___x_1402_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec_ref(v_k_1386_);
v_a_1457_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1431_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1431_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_discr_1410_);
lean_dec_ref(v_resultType_1409_);
lean_dec(v_typeName_1408_);
lean_dec(v_fst_1407_);
lean_del_object(v___x_1402_);
lean_dec_ref(v_type_1397_);
lean_dec_ref(v_params_1396_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec_ref(v_k_1386_);
lean_dec_ref(v_decl_1385_);
v_a_1466_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1415_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1415_);
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
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_del_object(v___x_1402_);
lean_dec(v_val_1400_);
lean_dec_ref(v_type_1397_);
lean_dec_ref(v_params_1396_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec_ref(v_k_1386_);
lean_dec_ref(v_decl_1385_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v___x_1399_);
lean_dec_ref(v_type_1397_);
lean_dec_ref(v_params_1396_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec_ref(v_k_1386_);
lean_dec_ref(v_decl_1385_);
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(lean_object* v_code_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
switch(lean_obj_tag(v_code_1479_))
{
case 0:
{
lean_object* v_decl_1488_; lean_object* v_k_1489_; lean_object* v___x_1490_; 
v_decl_1488_ = lean_ctor_get(v_code_1479_, 0);
v_k_1489_ = lean_ctor_get(v_code_1479_, 1);
lean_inc_ref(v_k_1489_);
v___x_1490_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1489_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1517_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1517_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1517_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
uint8_t v___y_1496_; size_t v___x_1512_; size_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = lean_ptr_addr(v_k_1489_);
v___x_1513_ = lean_ptr_addr(v_a_1491_);
v___x_1514_ = lean_usize_dec_eq(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
v___y_1496_ = v___x_1514_;
goto v___jp_1495_;
}
else
{
size_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_ptr_addr(v_decl_1488_);
v___x_1516_ = lean_usize_dec_eq(v___x_1515_, v___x_1515_);
v___y_1496_ = v___x_1516_;
goto v___jp_1495_;
}
v___jp_1495_:
{
if (v___y_1496_ == 0)
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1506_; 
lean_inc_ref(v_decl_1488_);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_code_1479_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; lean_object* v_unused_1508_; 
v_unused_1507_ = lean_ctor_get(v_code_1479_, 1);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_code_1479_, 0);
lean_dec(v_unused_1508_);
v___x_1498_ = v_code_1479_;
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v_code_1479_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_a_1491_);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_decl_1488_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_a_1491_);
v___x_1501_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1501_);
v___x_1503_ = v___x_1493_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_a_1491_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v_code_1479_);
v___x_1510_ = v___x_1493_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_code_1479_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_1479_);
return v___x_1490_;
}
}
case 1:
{
lean_object* v_decl_1518_; lean_object* v_k_1519_; lean_object* v_params_1520_; lean_object* v_type_1521_; lean_object* v_value_1522_; lean_object* v___x_1523_; 
v_decl_1518_ = lean_ctor_get(v_code_1479_, 0);
v_k_1519_ = lean_ctor_get(v_code_1479_, 1);
v_params_1520_ = lean_ctor_get(v_decl_1518_, 2);
v_type_1521_ = lean_ctor_get(v_decl_1518_, 3);
v_value_1522_ = lean_ctor_get(v_decl_1518_, 4);
lean_inc(v_a_1486_);
lean_inc_ref(v_a_1485_);
lean_inc(v_a_1484_);
lean_inc_ref(v_a_1483_);
lean_inc_ref(v_a_1482_);
lean_inc_ref(v_value_1522_);
v___x_1523_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1522_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = 0;
lean_inc_ref(v_params_1520_);
lean_inc_ref(v_type_1521_);
lean_inc_ref(v_decl_1518_);
v___x_1526_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1525_, v_decl_1518_, v_type_1521_, v_params_1520_, v_a_1524_, v_a_1484_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
lean_inc_ref(v_k_1519_);
v___x_1528_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1519_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1556_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1556_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1556_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
uint8_t v___y_1534_; size_t v___x_1550_; size_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1550_ = lean_ptr_addr(v_k_1519_);
v___x_1551_ = lean_ptr_addr(v_a_1529_);
v___x_1552_ = lean_usize_dec_eq(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
v___y_1534_ = v___x_1552_;
goto v___jp_1533_;
}
else
{
size_t v___x_1553_; size_t v___x_1554_; uint8_t v___x_1555_; 
v___x_1553_ = lean_ptr_addr(v_decl_1518_);
v___x_1554_ = lean_ptr_addr(v_a_1527_);
v___x_1555_ = lean_usize_dec_eq(v___x_1553_, v___x_1554_);
v___y_1534_ = v___x_1555_;
goto v___jp_1533_;
}
v___jp_1533_:
{
if (v___y_1534_ == 0)
{
lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v_code_1479_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; lean_object* v_unused_1546_; 
v_unused_1545_ = lean_ctor_get(v_code_1479_, 1);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_code_1479_, 0);
lean_dec(v_unused_1546_);
v___x_1536_ = v_code_1479_;
v_isShared_1537_ = v_isSharedCheck_1544_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v_code_1479_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1544_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v_a_1529_);
lean_ctor_set(v___x_1536_, 0, v_a_1527_);
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1527_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_a_1529_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1541_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1539_);
v___x_1541_ = v___x_1531_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v___x_1548_; 
lean_dec(v_a_1529_);
lean_dec(v_a_1527_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v_code_1479_);
v___x_1548_ = v___x_1531_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_code_1479_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_dec(v_a_1527_);
lean_dec_ref(v_code_1479_);
return v___x_1528_;
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_code_1479_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_a_1482_);
v_a_1557_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1526_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1526_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_dec_ref(v_code_1479_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_a_1482_);
return v___x_1523_;
}
}
case 2:
{
lean_object* v_decl_1565_; lean_object* v_k_1566_; lean_object* v___x_1567_; 
v_decl_1565_ = lean_ctor_get(v_code_1479_, 0);
v_k_1566_ = lean_ctor_get(v_code_1479_, 1);
lean_inc(v_a_1486_);
lean_inc_ref(v_a_1485_);
lean_inc(v_a_1484_);
lean_inc_ref(v_a_1483_);
lean_inc_ref(v_a_1482_);
lean_inc_ref(v_k_1566_);
lean_inc_ref(v_decl_1565_);
v___x_1567_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1565_, v_k_1566_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1621_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1621_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1621_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
if (lean_obj_tag(v_a_1568_) == 1)
{
lean_object* v_val_1572_; lean_object* v___x_1574_; 
lean_dec_ref(v_code_1479_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_a_1482_);
v_val_1572_ = lean_ctor_get(v_a_1568_, 0);
lean_inc(v_val_1572_);
lean_dec_ref(v_a_1568_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_val_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_val_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
else
{
lean_object* v_params_1576_; lean_object* v_type_1577_; lean_object* v_value_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1570_);
lean_dec(v_a_1568_);
v_params_1576_ = lean_ctor_get(v_decl_1565_, 2);
v_type_1577_ = lean_ctor_get(v_decl_1565_, 3);
v_value_1578_ = lean_ctor_get(v_decl_1565_, 4);
lean_inc(v_a_1486_);
lean_inc_ref(v_a_1485_);
lean_inc(v_a_1484_);
lean_inc_ref(v_a_1483_);
lean_inc_ref(v_a_1482_);
lean_inc_ref(v_value_1578_);
v___x_1579_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_1578_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = 0;
lean_inc_ref(v_params_1576_);
lean_inc_ref(v_type_1577_);
lean_inc_ref(v_decl_1565_);
v___x_1582_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1581_, v_decl_1565_, v_type_1577_, v_params_1576_, v_a_1580_, v_a_1484_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
lean_inc_ref(v_k_1566_);
v___x_1584_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_1566_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1612_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1612_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1612_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
uint8_t v___y_1590_; size_t v___x_1606_; size_t v___x_1607_; uint8_t v___x_1608_; 
v___x_1606_ = lean_ptr_addr(v_k_1566_);
v___x_1607_ = lean_ptr_addr(v_a_1585_);
v___x_1608_ = lean_usize_dec_eq(v___x_1606_, v___x_1607_);
if (v___x_1608_ == 0)
{
v___y_1590_ = v___x_1608_;
goto v___jp_1589_;
}
else
{
size_t v___x_1609_; size_t v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = lean_ptr_addr(v_decl_1565_);
v___x_1610_ = lean_ptr_addr(v_a_1583_);
v___x_1611_ = lean_usize_dec_eq(v___x_1609_, v___x_1610_);
v___y_1590_ = v___x_1611_;
goto v___jp_1589_;
}
v___jp_1589_:
{
if (v___y_1590_ == 0)
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_isSharedCheck_1600_ = !lean_is_exclusive(v_code_1479_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; lean_object* v_unused_1602_; 
v_unused_1601_ = lean_ctor_get(v_code_1479_, 1);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_code_1479_, 0);
lean_dec(v_unused_1602_);
v___x_1592_ = v_code_1479_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_code_1479_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v_a_1585_);
lean_ctor_set(v___x_1592_, 0, v_a_1583_);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1583_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_a_1585_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1595_);
v___x_1597_ = v___x_1587_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v___x_1604_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1583_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_code_1479_);
v___x_1604_ = v___x_1587_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_code_1479_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
else
{
lean_dec(v_a_1583_);
lean_dec_ref(v_code_1479_);
return v___x_1584_;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_code_1479_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_a_1482_);
v_a_1613_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1582_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1582_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_dec_ref(v_code_1479_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_a_1482_);
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_code_1479_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_a_1482_);
v_a_1622_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1567_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1567_);
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
case 3:
{
lean_object* v_fvarId_1630_; lean_object* v_args_1631_; lean_object* v___x_1632_; 
v_fvarId_1630_ = lean_ctor_get(v_code_1479_, 0);
v_args_1631_ = lean_ctor_get(v_code_1479_, 1);
lean_inc_ref(v_args_1631_);
v___x_1632_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_1630_, v_args_1631_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec_ref(v_a_1482_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1644_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
if (lean_obj_tag(v_a_1633_) == 1)
{
lean_object* v_val_1637_; lean_object* v___x_1639_; 
lean_dec_ref(v_code_1479_);
v_val_1637_ = lean_ctor_get(v_a_1633_, 0);
lean_inc(v_val_1637_);
lean_dec_ref(v_a_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_val_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_val_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_a_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v_code_1479_);
v___x_1642_ = v___x_1635_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_code_1479_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec_ref(v_code_1479_);
v_a_1645_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1632_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1632_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
case 4:
{
lean_object* v_cases_1653_; lean_object* v_typeName_1654_; lean_object* v_resultType_1655_; lean_object* v_discr_1656_; lean_object* v_alts_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1696_; 
v_cases_1653_ = lean_ctor_get(v_code_1479_, 0);
lean_inc_ref(v_cases_1653_);
v_typeName_1654_ = lean_ctor_get(v_cases_1653_, 0);
v_resultType_1655_ = lean_ctor_get(v_cases_1653_, 1);
v_discr_1656_ = lean_ctor_get(v_cases_1653_, 2);
v_alts_1657_ = lean_ctor_get(v_cases_1653_, 3);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_cases_1653_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1659_ = v_cases_1653_;
v_isShared_1660_ = v_isSharedCheck_1696_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_alts_1657_);
lean_inc(v_discr_1656_);
lean_inc(v_resultType_1655_);
lean_inc(v_typeName_1654_);
lean_dec(v_cases_1653_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1696_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1657_);
lean_inc(v_discr_1656_);
v___x_1662_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1656_, v___x_1661_, v_alts_1657_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1687_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1687_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1687_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
size_t v___x_1667_; size_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1667_ = lean_ptr_addr(v_alts_1657_);
lean_dec_ref(v_alts_1657_);
v___x_1668_ = lean_ptr_addr(v_a_1663_);
v___x_1669_ = lean_usize_dec_eq(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1682_; 
v_isSharedCheck_1682_ = !lean_is_exclusive(v_code_1479_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v_code_1479_, 0);
lean_dec(v_unused_1683_);
v___x_1671_ = v_code_1479_;
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
else
{
lean_dec(v_code_1479_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 3, v_a_1663_);
v___x_1674_ = v___x_1659_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_typeName_1654_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_resultType_1655_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_discr_1656_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_a_1663_);
v___x_1674_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1676_);
v___x_1678_ = v___x_1665_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
else
{
lean_object* v___x_1685_; 
lean_dec(v_a_1663_);
lean_del_object(v___x_1659_);
lean_dec(v_discr_1656_);
lean_dec_ref(v_resultType_1655_);
lean_dec(v_typeName_1654_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v_code_1479_);
v___x_1685_ = v___x_1665_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_code_1479_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1659_);
lean_dec_ref(v_alts_1657_);
lean_dec(v_discr_1656_);
lean_dec_ref(v_resultType_1655_);
lean_dec(v_typeName_1654_);
lean_dec_ref(v_code_1479_);
v_a_1688_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1662_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1662_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
default: 
{
lean_object* v___x_1697_; 
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec_ref(v_a_1482_);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_code_1479_);
return v___x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(lean_object* v_discr_1698_, lean_object* v_i_1699_, lean_object* v_as_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = lean_array_get_size(v_as_1700_);
v___x_1710_ = lean_nat_dec_lt(v_i_1699_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v_i_1699_);
lean_dec(v_discr_1698_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_as_1700_);
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; lean_object* v_a_1714_; 
v_a_1712_ = lean_array_fget_borrowed(v_as_1700_, v_i_1699_);
if (lean_obj_tag(v_a_1712_) == 0)
{
lean_object* v_ctorName_1725_; lean_object* v_params_1726_; lean_object* v_code_1727_; lean_object* v___x_1728_; 
v_ctorName_1725_ = lean_ctor_get(v_a_1712_, 0);
v_params_1726_ = lean_ctor_get(v_a_1712_, 1);
v_code_1727_ = lean_ctor_get(v_a_1712_, 2);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc_ref(v_params_1726_);
lean_inc(v_ctorName_1725_);
lean_inc(v_discr_1698_);
v___x_1728_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_1698_, v_ctorName_1725_, v_params_1726_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc_ref(v_code_1727_);
v___x_1730_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1727_, v___y_1701_, v___y_1702_, v_a_1729_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1730_);
lean_inc_ref(v_a_1712_);
v___x_1732_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1712_, v_a_1731_);
v_a_1714_ = v___x_1732_;
goto v___jp_1713_;
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v_as_1700_);
lean_dec(v_i_1699_);
lean_dec(v_discr_1698_);
v_a_1733_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1730_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1730_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v_as_1700_);
lean_dec(v_i_1699_);
lean_dec(v_discr_1698_);
v_a_1741_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1728_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1728_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_code_1749_; lean_object* v___x_1750_; 
v_code_1749_ = lean_ctor_get(v_a_1712_, 0);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc_ref(v_code_1749_);
v___x_1750_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1749_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
lean_inc_ref(v_a_1712_);
v___x_1752_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1712_, v_a_1751_);
v_a_1714_ = v___x_1752_;
goto v___jp_1713_;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v_as_1700_);
lean_dec(v_i_1699_);
lean_dec(v_discr_1698_);
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
v___jp_1713_:
{
size_t v___x_1715_; size_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1715_ = lean_ptr_addr(v_a_1712_);
v___x_1716_ = lean_ptr_addr(v_a_1714_);
v___x_1717_ = lean_usize_dec_eq(v___x_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_add(v_i_1699_, v___x_1718_);
v___x_1720_ = lean_array_fset(v_as_1700_, v_i_1699_, v_a_1714_);
lean_dec(v_i_1699_);
v_i_1699_ = v___x_1719_;
v_as_1700_ = v___x_1720_;
goto _start;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec_ref(v_a_1714_);
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = lean_nat_add(v_i_1699_, v___x_1722_);
lean_dec(v_i_1699_);
v_i_1699_ = v___x_1723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(lean_object* v_discr_1761_, lean_object* v_i_1762_, lean_object* v_as_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_1761_, v_i_1762_, v_as_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1765_);
lean_dec(v___y_1764_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(lean_object* v_decl_1773_, lean_object* v_k_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_1773_, v_k_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
lean_dec(v_a_1776_);
lean_dec(v_a_1775_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(lean_object** _args){
lean_object* v_discr_1784_ = _args[0];
lean_object* v___x_1785_ = _args[1];
lean_object* v_val_1786_ = _args[2];
lean_object* v_fst_1787_ = _args[3];
lean_object* v_params_1788_ = _args[4];
lean_object* v_snd_1789_ = _args[5];
lean_object* v_as_1790_ = _args[6];
lean_object* v_sz_1791_ = _args[7];
lean_object* v_i_1792_ = _args[8];
lean_object* v_b_1793_ = _args[9];
lean_object* v___y_1794_ = _args[10];
lean_object* v___y_1795_ = _args[11];
lean_object* v___y_1796_ = _args[12];
lean_object* v___y_1797_ = _args[13];
lean_object* v___y_1798_ = _args[14];
lean_object* v___y_1799_ = _args[15];
lean_object* v___y_1800_ = _args[16];
lean_object* v___y_1801_ = _args[17];
_start:
{
size_t v_sz_boxed_1802_; size_t v_i_boxed_1803_; lean_object* v_res_1804_; 
v_sz_boxed_1802_ = lean_unbox_usize(v_sz_1791_);
lean_dec(v_sz_1791_);
v_i_boxed_1803_ = lean_unbox_usize(v_i_1792_);
lean_dec(v_i_1792_);
v_res_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_1784_, v___x_1785_, v_val_1786_, v_fst_1787_, v_params_1788_, v_snd_1789_, v_as_1790_, v_sz_boxed_1802_, v_i_boxed_1803_, v_b_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v_as_1790_);
lean_dec_ref(v_snd_1789_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(lean_object* v_code_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1807_);
lean_dec(v_a_1806_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(lean_object* v___x_1815_, lean_object* v_a_1816_, lean_object* v_init_1817_, lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_1815_, v_a_1816_, v_init_1817_, v_x_1818_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(lean_object* v___x_1828_, lean_object* v_a_1829_, lean_object* v_init_1830_, lean_object* v_x_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(v___x_1828_, v_a_1829_, v_init_1830_, v_x_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec(v___x_1828_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(lean_object* v_cls_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_options_1847_; uint8_t v_hasTrace_1848_; 
v_options_1847_ = lean_ctor_get(v___y_1845_, 2);
v_hasTrace_1848_ = lean_ctor_get_uint8(v_options_1847_, sizeof(void*)*1);
if (v_hasTrace_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_dec(v_cls_1844_);
v___x_1849_ = lean_box(v_hasTrace_1848_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
return v___x_1850_;
}
else
{
lean_object* v_inheritedTraceOptions_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_inheritedTraceOptions_1851_ = lean_ctor_get(v___y_1845_, 13);
v___x_1852_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___closed__1));
v___x_1853_ = l_Lean_Name_append(v___x_1852_, v_cls_1844_);
v___x_1854_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1851_, v_options_1847_, v___x_1853_);
lean_dec(v___x_1853_);
v___x_1855_ = lean_box(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg___boxed(lean_object* v_cls_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(v_cls_1857_, v___y_1858_);
lean_dec_ref(v___y_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(lean_object* v_cls_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(v_cls_1861_, v___y_1864_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(lean_object* v_cls_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_cls_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__1);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
lean_ctor_set(v___x_1880_, 2, v___x_1879_);
lean_ctor_set(v___x_1880_, 3, v___x_1878_);
lean_ctor_set(v___x_1880_, 4, v___x_1878_);
lean_ctor_set(v___x_1880_, 5, v___x_1878_);
lean_ctor_set(v___x_1880_, 6, v___x_1878_);
lean_ctor_set(v___x_1880_, 7, v___x_1878_);
lean_ctor_set(v___x_1880_, 8, v___x_1878_);
return v___x_1880_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1881_; double v___x_1882_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = lean_float_of_nat(v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(lean_object* v_cls_1886_, lean_object* v_msg_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
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
v___x_1907_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__2);
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
v___x_1932_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__3);
v___x_1933_ = 0;
v___x_1934_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__4));
v___x_1935_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1935_, 0, v_cls_1886_);
lean_ctor_set(v___x_1935_, 1, v___x_1931_);
lean_ctor_set(v___x_1935_, 2, v___x_1934_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3, v___x_1932_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3 + 8, v___x_1932_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*3 + 16, v___x_1933_);
v___x_1936_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___closed__5));
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5___boxed(lean_object* v_cls_1965_, lean_object* v_msg_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(v_cls_1965_, v_msg_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
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
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__0));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(lean_object* v_as_x27_2001_, lean_object* v_b_2002_){
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
lean_object* v_head_2005_; lean_object* v_snd_2006_; lean_object* v_tail_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2041_; 
v_head_2005_ = lean_ctor_get(v_as_x27_2001_, 0);
lean_inc(v_head_2005_);
v_snd_2006_ = lean_ctor_get(v_head_2005_, 1);
lean_inc(v_snd_2006_);
v_tail_2007_ = lean_ctor_get(v_as_x27_2001_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_as_x27_2001_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_as_x27_2001_, 0);
lean_dec(v_unused_2042_);
v___x_2009_ = v_as_x27_2001_;
v_isShared_2010_ = v_isSharedCheck_2041_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_tail_2007_);
lean_dec(v_as_x27_2001_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2041_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_fst_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2039_; 
v_fst_2011_ = lean_ctor_get(v_head_2005_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_head_2005_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v_head_2005_, 1);
lean_dec(v_unused_2040_);
v___x_2013_ = v_head_2005_;
v_isShared_2014_ = v_isSharedCheck_2039_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_fst_2011_);
lean_dec(v_head_2005_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2039_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_ctorNames_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2037_; 
v_ctorNames_2015_ = lean_ctor_get(v_snd_2006_, 1);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_snd_2006_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v_snd_2006_, 0);
lean_dec(v_unused_2038_);
v___x_2017_ = v_snd_2006_;
v_isShared_2018_ = v_isSharedCheck_2037_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_ctorNames_2015_);
lean_dec(v_snd_2006_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2037_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2019_ = l_Lean_mkFVar(v_fst_2011_);
v___x_2020_ = l_Lean_MessageData_ofExpr(v___x_2019_);
v___x_2021_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___closed__1);
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 7);
lean_ctor_set(v___x_2017_, 1, v___x_2021_);
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2023_ = v___x_2017_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2024_ = lean_box(0);
v___x_2025_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v___x_2024_, v_ctorNames_2015_);
lean_dec(v_ctorNames_2015_);
v___x_2026_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(v___x_2025_, v___x_2024_);
v___x_2027_ = l_Lean_MessageData_ofList(v___x_2026_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 7);
lean_ctor_set(v___x_2013_, 1, v___x_2027_);
lean_ctor_set(v___x_2013_, 0, v___x_2023_);
v___x_2029_ = v___x_2013_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = l_Lean_indentD(v___x_2029_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 7);
lean_ctor_set(v___x_2009_, 1, v___x_2030_);
lean_ctor_set(v___x_2009_, 0, v_b_2002_);
v___x_2032_ = v___x_2009_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_b_2002_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
v_as_x27_2001_ = v_tail_2007_;
v_b_2002_ = v___x_2032_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg___boxed(lean_object* v_as_x27_2043_, lean_object* v_b_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(v_as_x27_2043_, v_b_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(lean_object* v_init_2047_, lean_object* v_x_2048_){
_start:
{
if (lean_obj_tag(v_x_2048_) == 0)
{
lean_object* v_k_2049_; lean_object* v_v_2050_; lean_object* v_l_2051_; lean_object* v_r_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_k_2049_ = lean_ctor_get(v_x_2048_, 1);
v_v_2050_ = lean_ctor_get(v_x_2048_, 2);
v_l_2051_ = lean_ctor_get(v_x_2048_, 3);
v_r_2052_ = lean_ctor_get(v_x_2048_, 4);
v___x_2053_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v_init_2047_, v_r_2052_);
lean_inc(v_v_2050_);
lean_inc(v_k_2049_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_k_2049_);
lean_ctor_set(v___x_2054_, 1, v_v_2050_);
v___x_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v___x_2053_);
v_init_2047_ = v___x_2055_;
v_x_2048_ = v_l_2051_;
goto _start;
}
else
{
return v_init_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(lean_object* v_init_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v_init_2057_, v_x_2058_);
lean_dec(v_x_2058_);
return v_res_2059_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5));
v___x_2071_ = l_Lean_MessageData_ofFormat(v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object* v_code_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2078_; 
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
lean_inc(v_a_2074_);
lean_inc_ref(v_a_2073_);
lean_inc_ref(v_code_2072_);
v___x_2078_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(v_code_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2129_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2129_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2129_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
uint8_t v___x_2106_; 
v___x_2106_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_a_2079_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec(v_a_2079_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec_ref(v_code_2072_);
v___x_2107_ = lean_box(0);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2107_);
v___x_2109_ = v___x_2081_;
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
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_a_2113_; uint8_t v___x_2114_; 
lean_del_object(v___x_2081_);
v___x_2111_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2112_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___redArg(v___x_2111_, v_a_2075_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
if (v___x_2114_ == 0)
{
goto v___jp_2083_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_a_2119_; lean_object* v___x_2120_; 
v___x_2115_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6, &l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6);
v___x_2116_ = lean_box(0);
v___x_2117_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(v___x_2116_, v_a_2079_);
v___x_2118_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(v___x_2117_, v___x_2115_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__5(v___x_2111_, v_a_2119_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_dec_ref(v___x_2120_);
goto v___jp_2083_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_a_2079_);
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec_ref(v_code_2072_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2084_ = lean_box(1);
v___x_2085_ = lean_st_mk_ref(v___x_2084_);
v___x_2086_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2, &l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2);
v___x_2087_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_2072_, v_a_2079_, v___x_2085_, v___x_2086_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
lean_dec(v_a_2079_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2097_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2097_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2097_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2092_ = lean_st_ref_get(v___x_2085_);
lean_dec(v___x_2085_);
lean_dec(v___x_2092_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_a_2088_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2093_);
v___x_2095_ = v___x_2090_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v___x_2085_);
v_a_2098_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2087_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2087_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2076_);
lean_dec_ref(v_a_2075_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec_ref(v_code_2072_);
v_a_2130_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2078_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2078_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(lean_object* v_code_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(v_code_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(lean_object* v_as_2145_, lean_object* v_as_x27_2146_, lean_object* v_b_2147_, lean_object* v_a_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___redArg(v_as_x27_2146_, v_b_2147_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(lean_object* v_as_2155_, lean_object* v_as_x27_2156_, lean_object* v_b_2157_, lean_object* v_a_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v_as_2155_, v_as_x27_2156_, v_b_2157_, v_a_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v_as_2155_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2238_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3));
v___x_2239_ = 0;
v___x_2240_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_));
v___x_2241_ = l_Lean_registerTraceClass(v___x_2238_, v___x_2239_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
return v_res_2243_;
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
