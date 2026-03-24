// Lean compiler output
// Module: Lean.Meta.MethodSpecs
// Imports: public import Lean.Meta.Tactic.Simp.SimpTheorems import Lean.Meta.Tactic.Simp.Main import Lean.Structure
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
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_getFieldInfo_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Meta_mkDSimpTheorem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addSimpTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSimprocs___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_isNat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "internal error: equation `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` does not hold definitionally"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "internal error: could not find field "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " in structure "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "function `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` does not take its arguments in the same order as the instance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` is called with universe parameters\n  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "\nwhich differs from the instances' universe parameters\n  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "field `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "` of the instance is not an application of a constant"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MethodSpecs"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 26, 7, 123, 178, 104, 28, 234)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "MethodSpecs for "};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nthms: "};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nprivateSpecs: "};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "the definition of `"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` does not have the expected shape"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a definition"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isDefn\?"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is not a structure"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expected `"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "` to be a type class instance, but its type"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "does not look like a class."};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMethodSpecsAttrData_default = (const lean_object*)&l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedMethodSpecsAttrData = (const lean_object*)&l_Lean_instInhabitedMethodSpecsAttrData_default___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7;
static const lean_array_object l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "methodSpecsAttr"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 147, 219, 183, 255, 218, 101, 198)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "method_specs"};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 159, 225, 215, 58, 146, 25, 204)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "generate method specification theorems"};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__1_value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__2_value),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__3_value),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 12, 62, 206, 89, 162, 192, 230)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(78, 38, 12, 94, 249, 31, 203, 80)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__5_value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 165, 203, 10, 103, 147, 118, 194)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__6_value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(115, 172, 90, 159, 97, 185, 62, 46)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__7_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 566, .m_capacity = 566, .m_length = 565, .m_data = "Generate method specification theorems for the methods of the given type class instance.\n\nThis expects all (non-proof) methods of the instance to be defined via separate helper functions,\nwhich must take the same arguments as the instance itself, in the same order.\n\nIf it is applied to an instance\n```\ninstance instClsT : Cls T where op := opImpl\n```\nit produces a theorem `instClsT.op_spec` based on `opImpl.eq_def`, but phrased in terms of the\noverloaded `Cls.op` operation, and similarly `instClsT.op_spec_<n>` based on the equational theorems\n`opImpl.eq_<n>`.\n"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "method_specs_simp"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 101, 98, 30, 138, 15, 29, 180)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "simp lemma used to post-process the theorem created by `@[method_specs]`."};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "methodSpecsSimpExtension"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 171, 16, 183, 21, 229, 232, 208)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_spec"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_spec_"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__7_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__8_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "type for "};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "failed to generate unfolding theorem for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "adding simp theorem for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getMethodSpecTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getMethodSpecTheorems___closed__0 = (const lean_object*)&l_Lean_getMethodSpecTheorems___closed__0_value;
static const lean_ctor_object l_Lean_getMethodSpecTheorems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_getMethodSpecTheorems___closed__0_value)}};
static const lean_object* l_Lean_getMethodSpecTheorems___closed__1 = (const lean_object*)&l_Lean_getMethodSpecTheorems___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__6_value),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 214, 187, 38, 55, 160, 65, 54)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 146, 220, 250, 255, 68, 126, 144)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__3_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 175, 227, 37, 209, 186, 195, 14)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 94, 80, 63, 233, 255, 44, 156)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__5_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 146, 66, 195, 240, 16, 69, 239)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, uint8_t v_whnfType_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_28_, 0, v_k_20_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_19_, v___f_28_, v_cleanupAnnotations_21_, v_whnfType_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___boxed(lean_object* v_type_46_, lean_object* v_k_47_, lean_object* v_cleanupAnnotations_48_, lean_object* v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; uint8_t v_whnfType_boxed_56_; lean_object* v_res_57_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_48_);
v_whnfType_boxed_56_ = lean_unbox(v_whnfType_49_);
v_res_57_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_46_, v_k_47_, v_cleanupAnnotations_boxed_55_, v_whnfType_boxed_56_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1(lean_object* v_00_u03b1_58_, lean_object* v_type_59_, lean_object* v_k_60_, uint8_t v_cleanupAnnotations_61_, uint8_t v_whnfType_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_59_, v_k_60_, v_cleanupAnnotations_61_, v_whnfType_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___boxed(lean_object* v_00_u03b1_69_, lean_object* v_type_70_, lean_object* v_k_71_, lean_object* v_cleanupAnnotations_72_, lean_object* v_whnfType_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_79_; uint8_t v_whnfType_boxed_80_; lean_object* v_res_81_; 
v_cleanupAnnotations_boxed_79_ = lean_unbox(v_cleanupAnnotations_72_);
v_whnfType_boxed_80_ = lean_unbox(v_whnfType_73_);
v_res_81_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1(v_00_u03b1_69_, v_type_70_, v_k_71_, v_cleanupAnnotations_boxed_79_, v_whnfType_boxed_80_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg(lean_object* v_cls_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_options_88_; uint8_t v_hasTrace_89_; 
v_options_88_ = lean_ctor_get(v___y_86_, 2);
v_hasTrace_89_ = lean_ctor_get_uint8(v_options_88_, sizeof(void*)*1);
if (v_hasTrace_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_cls_85_);
v___x_90_ = lean_box(v_hasTrace_89_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
else
{
lean_object* v_inheritedTraceOptions_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_inheritedTraceOptions_92_ = lean_ctor_get(v___y_86_, 13);
v___x_93_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___closed__1));
v___x_94_ = l_Lean_Name_append(v___x_93_, v_cls_85_);
v___x_95_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_92_, v_options_88_, v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_box(v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg___boxed(lean_object* v_cls_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg(v_cls_98_, v___y_99_);
lean_dec_ref(v___y_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(lean_object* v_cls_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg(v_cls_102_, v___y_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___boxed(lean_object* v_cls_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(v_cls_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___redArg(lean_object* v_e_116_, lean_object* v_k_117_, uint8_t v_cleanupAnnotations_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___f_124_; uint8_t v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___f_124_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_124_, 0, v_k_117_);
v___x_125_ = 1;
v___x_126_ = 0;
v___x_127_ = lean_box(0);
v___x_128_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_116_, v___x_125_, v___x_126_, v___x_125_, v___x_126_, v___x_127_, v___f_124_, v_cleanupAnnotations_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
v_a_137_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_128_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_128_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___redArg___boxed(lean_object* v_e_145_, lean_object* v_k_146_, lean_object* v_cleanupAnnotations_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_153_; lean_object* v_res_154_; 
v_cleanupAnnotations_boxed_153_ = lean_unbox(v_cleanupAnnotations_147_);
v_res_154_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___redArg(v_e_145_, v_k_146_, v_cleanupAnnotations_boxed_153_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13(lean_object* v_00_u03b1_155_, lean_object* v_e_156_, lean_object* v_k_157_, uint8_t v_cleanupAnnotations_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___redArg(v_e_156_, v_k_157_, v_cleanupAnnotations_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___boxed(lean_object* v_00_u03b1_165_, lean_object* v_e_166_, lean_object* v_k_167_, lean_object* v_cleanupAnnotations_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_174_; lean_object* v_res_175_; 
v_cleanupAnnotations_boxed_174_ = lean_unbox(v_cleanupAnnotations_168_);
v_res_175_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13(v_00_u03b1_165_, v_e_166_, v_k_167_, v_cleanupAnnotations_boxed_174_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(lean_object* v_xs_176_, lean_object* v_x_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_array_get_size(v_xs_176_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed(lean_object* v_xs_185_, lean_object* v_x_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(v_xs_185_, v_x_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec_ref(v_x_186_);
lean_dec_ref(v_xs_185_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(lean_object* v_msgData_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_env_200_; lean_object* v___x_201_; lean_object* v_mctx_202_; lean_object* v_lctx_203_; lean_object* v_options_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_199_ = lean_st_ref_get(v___y_197_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_env_200_);
lean_dec(v___x_199_);
v___x_201_ = lean_st_ref_get(v___y_195_);
v_mctx_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc_ref(v_mctx_202_);
lean_dec(v___x_201_);
v_lctx_203_ = lean_ctor_get(v___y_194_, 2);
v_options_204_ = lean_ctor_get(v___y_196_, 2);
lean_inc_ref(v_options_204_);
lean_inc_ref(v_lctx_203_);
v___x_205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_205_, 0, v_env_200_);
lean_ctor_set(v___x_205_, 1, v_mctx_202_);
lean_ctor_set(v___x_205_, 2, v_lctx_203_);
lean_ctor_set(v___x_205_, 3, v_options_204_);
v___x_206_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_msgData_193_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4___boxed(lean_object* v_msgData_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msgData_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(lean_object* v_msg_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_ref_221_; lean_object* v___x_222_; lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_ref_221_ = lean_ctor_get(v___y_218_, 5);
v___x_222_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
lean_inc(v_ref_221_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v_ref_221_);
lean_ctor_set(v___x_227_, 1, v_a_223_);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 1);
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg___boxed(lean_object* v_msg_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
if (lean_obj_tag(v_a_239_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = l_List_reverse___redArg(v_a_240_);
return v___x_241_;
}
else
{
lean_object* v_head_242_; lean_object* v_tail_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
v_head_242_ = lean_ctor_get(v_a_239_, 0);
v_tail_243_ = lean_ctor_get(v_a_239_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_239_);
if (v_isSharedCheck_252_ == 0)
{
v___x_245_ = v_a_239_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_tail_243_);
lean_inc(v_head_242_);
lean_dec(v_a_239_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = l_Lean_MessageData_ofExpr(v_head_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_a_240_);
lean_ctor_set(v___x_245_, 0, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_a_240_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
v_a_239_ = v_tail_243_;
v_a_240_ = v___x_249_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__0(void){
_start:
{
lean_object* v___x_253_; double v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_float_of_nat(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(lean_object* v_cls_258_, lean_object* v_msg_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_ref_265_; lean_object* v___x_266_; lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_311_; 
v_ref_265_ = lean_ctor_get(v___y_262_, 5);
v___x_266_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_311_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_311_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_311_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v_traceState_272_; lean_object* v_env_273_; lean_object* v_nextMacroScope_274_; lean_object* v_ngen_275_; lean_object* v_auxDeclNGen_276_; lean_object* v_cache_277_; lean_object* v_messages_278_; lean_object* v_infoState_279_; lean_object* v_snapshotTasks_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_310_; 
v___x_271_ = lean_st_ref_take(v___y_263_);
v_traceState_272_ = lean_ctor_get(v___x_271_, 4);
v_env_273_ = lean_ctor_get(v___x_271_, 0);
v_nextMacroScope_274_ = lean_ctor_get(v___x_271_, 1);
v_ngen_275_ = lean_ctor_get(v___x_271_, 2);
v_auxDeclNGen_276_ = lean_ctor_get(v___x_271_, 3);
v_cache_277_ = lean_ctor_get(v___x_271_, 5);
v_messages_278_ = lean_ctor_get(v___x_271_, 6);
v_infoState_279_ = lean_ctor_get(v___x_271_, 7);
v_snapshotTasks_280_ = lean_ctor_get(v___x_271_, 8);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_310_ == 0)
{
v___x_282_ = v___x_271_;
v_isShared_283_ = v_isSharedCheck_310_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_snapshotTasks_280_);
lean_inc(v_infoState_279_);
lean_inc(v_messages_278_);
lean_inc(v_cache_277_);
lean_inc(v_traceState_272_);
lean_inc(v_auxDeclNGen_276_);
lean_inc(v_ngen_275_);
lean_inc(v_nextMacroScope_274_);
lean_inc(v_env_273_);
lean_dec(v___x_271_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_310_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
uint64_t v_tid_284_; lean_object* v_traces_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_309_; 
v_tid_284_ = lean_ctor_get_uint64(v_traceState_272_, sizeof(void*)*1);
v_traces_285_ = lean_ctor_get(v_traceState_272_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_traceState_272_);
if (v_isSharedCheck_309_ == 0)
{
v___x_287_ = v_traceState_272_;
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_traces_285_);
lean_dec(v_traceState_272_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; double v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__0);
v___x_291_ = 0;
v___x_292_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__1));
v___x_293_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_293_, 0, v_cls_258_);
lean_ctor_set(v___x_293_, 1, v___x_289_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
lean_ctor_set_float(v___x_293_, sizeof(void*)*3, v___x_290_);
lean_ctor_set_float(v___x_293_, sizeof(void*)*3 + 8, v___x_290_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 16, v___x_291_);
v___x_294_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___closed__2));
v___x_295_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v_a_267_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
lean_inc(v_ref_265_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_ref_265_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_PersistentArray_push___redArg(v_traces_285_, v___x_296_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_297_);
v___x_299_ = v___x_287_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_297_);
lean_ctor_set_uint64(v_reuseFailAlloc_308_, sizeof(void*)*1, v_tid_284_);
v___x_299_ = v_reuseFailAlloc_308_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v___x_299_);
v___x_301_ = v___x_282_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_env_273_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_nextMacroScope_274_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_ngen_275_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_auxDeclNGen_276_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_cache_277_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v_messages_278_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v_infoState_279_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_snapshotTasks_280_);
v___x_301_ = v_reuseFailAlloc_307_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = lean_st_ref_set(v___y_263_, v___x_301_);
v___x_303_ = lean_box(0);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_303_);
v___x_305_ = v___x_269_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___boxed(lean_object* v_cls_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(v_cls_312_, v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__1));
v___x_324_ = l_Lean_MessageData_ofFormat(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_box(1);
v___x_326_ = l_Lean_MessageData_ofFormat(v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
if (lean_obj_tag(v_a_327_) == 0)
{
lean_object* v___x_329_; 
v___x_329_ = l_List_reverse___redArg(v_a_328_);
return v___x_329_;
}
else
{
lean_object* v_head_330_; lean_object* v_tail_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_355_; 
v_head_330_ = lean_ctor_get(v_a_327_, 0);
v_tail_331_ = lean_ctor_get(v_a_327_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_a_327_);
if (v_isSharedCheck_355_ == 0)
{
v___x_333_ = v_a_327_;
v_isShared_334_ = v_isSharedCheck_355_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_tail_331_);
lean_inc(v_head_330_);
lean_dec(v_a_327_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_355_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_354_; 
v_fst_335_ = lean_ctor_get(v_head_330_, 0);
v_snd_336_ = lean_ctor_get(v_head_330_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_head_330_);
if (v_isSharedCheck_354_ == 0)
{
v___x_338_ = v_head_330_;
v_isShared_339_ = v_isSharedCheck_354_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snd_336_);
lean_inc(v_fst_335_);
lean_dec(v_head_330_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_354_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_340_ = l_Lean_MessageData_ofName(v_fst_335_);
v___x_341_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__2);
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 7);
lean_ctor_set(v___x_338_, 1, v___x_341_);
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_343_ = v___x_338_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_353_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_344_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___closed__3);
v___x_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = l_Lean_MessageData_ofName(v_snd_336_);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = l_Lean_MessageData_paren(v___x_347_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_a_328_);
lean_ctor_set(v___x_333_, 0, v___x_348_);
v___x_350_ = v___x_333_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_a_328_);
v___x_350_ = v_reuseFailAlloc_352_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
v_a_327_ = v_tail_331_;
v_a_328_ = v___x_350_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(size_t v_sz_356_, size_t v_i_357_, lean_object* v_bs_358_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_lt(v_i_357_, v_sz_356_);
if (v___x_359_ == 0)
{
return v_bs_358_;
}
else
{
lean_object* v_v_360_; lean_object* v_type_361_; lean_object* v___x_362_; lean_object* v_bs_x27_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v___x_366_; 
v_v_360_ = lean_array_uget_borrowed(v_bs_358_, v_i_357_);
v_type_361_ = lean_ctor_get(v_v_360_, 2);
lean_inc_ref(v_type_361_);
v___x_362_ = lean_unsigned_to_nat(0u);
v_bs_x27_363_ = lean_array_uset(v_bs_358_, v_i_357_, v___x_362_);
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_357_, v___x_364_);
v___x_366_ = lean_array_uset(v_bs_x27_363_, v_i_357_, v_type_361_);
v_i_357_ = v___x_365_;
v_bs_358_ = v___x_366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10___boxed(lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_bs_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_372_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(v_sz_boxed_371_, v_i_boxed_372_, v_bs_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
if (lean_obj_tag(v_a_374_) == 0)
{
lean_object* v___x_376_; 
v___x_376_ = l_List_reverse___redArg(v_a_375_);
return v___x_376_;
}
else
{
lean_object* v_head_377_; lean_object* v_tail_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_387_; 
v_head_377_ = lean_ctor_get(v_a_374_, 0);
v_tail_378_ = lean_ctor_get(v_a_374_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_a_374_);
if (v_isSharedCheck_387_ == 0)
{
v___x_380_ = v_a_374_;
v_isShared_381_ = v_isSharedCheck_387_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_tail_378_);
lean_inc(v_head_377_);
lean_dec(v_a_374_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_387_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = l_Lean_mkLevelParam(v_head_377_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v_a_375_);
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_a_375_);
v___x_384_ = v_reuseFailAlloc_386_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
v_a_374_ = v_tail_378_;
v_a_375_ = v___x_384_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(lean_object* v_xs_388_, lean_object* v_ys_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_zero_391_; uint8_t v_isZero_392_; 
v_zero_391_ = lean_unsigned_to_nat(0u);
v_isZero_392_ = lean_nat_dec_eq(v_x_390_, v_zero_391_);
if (v_isZero_392_ == 1)
{
lean_dec(v_x_390_);
return v_isZero_392_;
}
else
{
lean_object* v_one_393_; lean_object* v_n_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_one_393_ = lean_unsigned_to_nat(1u);
v_n_394_ = lean_nat_sub(v_x_390_, v_one_393_);
lean_dec(v_x_390_);
v___x_395_ = lean_array_fget_borrowed(v_xs_388_, v_n_394_);
v___x_396_ = lean_array_fget_borrowed(v_ys_389_, v_n_394_);
v___x_397_ = lean_expr_eqv(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v_n_394_);
return v___x_397_;
}
else
{
v_x_390_ = v_n_394_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg___boxed(lean_object* v_xs_399_, lean_object* v_ys_400_, lean_object* v_x_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_399_, v_ys_400_, v_x_401_);
lean_dec_ref(v_ys_400_);
lean_dec_ref(v_xs_399_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
if (lean_obj_tag(v_a_404_) == 0)
{
lean_object* v___x_406_; 
v___x_406_ = l_List_reverse___redArg(v_a_405_);
return v___x_406_;
}
else
{
lean_object* v_head_407_; lean_object* v_tail_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
v_head_407_ = lean_ctor_get(v_a_404_, 0);
v_tail_408_ = lean_ctor_get(v_a_404_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_417_ == 0)
{
v___x_410_ = v_a_404_;
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_tail_408_);
lean_inc(v_head_407_);
lean_dec(v_a_404_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = l_Lean_MessageData_ofLevel(v_head_407_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v_a_405_);
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_a_405_);
v___x_414_ = v_reuseFailAlloc_416_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
v_a_404_ = v_tail_408_;
v_a_405_ = v___x_414_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
if (lean_obj_tag(v_x_419_) == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 1;
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
}
else
{
if (lean_obj_tag(v_x_419_) == 0)
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
else
{
lean_object* v_head_423_; lean_object* v_tail_424_; lean_object* v_head_425_; lean_object* v_tail_426_; uint8_t v___x_427_; 
v_head_423_ = lean_ctor_get(v_x_418_, 0);
v_tail_424_ = lean_ctor_get(v_x_418_, 1);
v_head_425_ = lean_ctor_get(v_x_419_, 0);
v_tail_426_ = lean_ctor_get(v_x_419_, 1);
v___x_427_ = lean_level_eq(v_head_423_, v_head_425_);
if (v___x_427_ == 0)
{
return v___x_427_;
}
else
{
v_x_418_ = v_tail_424_;
v_x_419_ = v_tail_426_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5___boxed(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(v_x_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec(v_x_429_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_433_; lean_object* v_dummy_434_; 
v___x_433_ = lean_box(0);
v_dummy_434_ = l_Lean_Expr_sort___override(v___x_433_);
return v_dummy_434_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1));
v___x_437_ = l_Lean_stringToMessageData(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3));
v___x_440_ = l_Lean_stringToMessageData(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11));
v___x_452_ = l_Lean_stringToMessageData(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15));
v___x_458_ = l_Lean_stringToMessageData(v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(lean_object* v_val_465_, lean_object* v_a_466_, lean_object* v___x_467_, lean_object* v_xs_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v_as_471_, size_t v_sz_472_, size_t v_i_473_, lean_object* v_b_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_a_481_; uint8_t v___x_485_; 
v___x_485_ = lean_usize_dec_lt(v_i_473_, v_sz_472_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_474_);
return v___x_486_;
}
else
{
lean_object* v_snd_487_; lean_object* v_snd_488_; lean_object* v_snd_489_; lean_object* v_fst_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_763_; 
v_snd_487_ = lean_ctor_get(v_b_474_, 1);
lean_inc(v_snd_487_);
v_snd_488_ = lean_ctor_get(v_snd_487_, 1);
lean_inc(v_snd_488_);
v_snd_489_ = lean_ctor_get(v_snd_488_, 1);
lean_inc(v_snd_489_);
v_fst_490_ = lean_ctor_get(v_b_474_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v_b_474_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_b_474_, 1);
lean_dec(v_unused_764_);
v___x_492_ = v_b_474_;
v_isShared_493_ = v_isSharedCheck_763_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_fst_490_);
lean_dec(v_b_474_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_763_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_fst_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_761_; 
v_fst_494_ = lean_ctor_get(v_snd_487_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_snd_487_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v_snd_487_, 1);
lean_dec(v_unused_762_);
v___x_496_ = v_snd_487_;
v_isShared_497_ = v_isSharedCheck_761_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_fst_494_);
lean_dec(v_snd_487_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_761_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_fst_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_759_; 
v_fst_498_ = lean_ctor_get(v_snd_488_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v_snd_488_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v_snd_488_, 1);
lean_dec(v_unused_760_);
v___x_500_ = v_snd_488_;
v_isShared_501_ = v_isSharedCheck_759_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_fst_498_);
lean_dec(v_snd_488_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_759_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_array_502_; lean_object* v_start_503_; lean_object* v_stop_504_; uint8_t v___x_505_; 
v_array_502_ = lean_ctor_get(v_snd_489_, 0);
v_start_503_ = lean_ctor_get(v_snd_489_, 1);
v_stop_504_ = lean_ctor_get(v_snd_489_, 2);
v___x_505_ = lean_nat_dec_lt(v_start_503_, v_stop_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_507_; 
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
if (v_isShared_501_ == 0)
{
v___x_507_ = v___x_500_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_fst_498_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_489_);
v___x_507_ = v_reuseFailAlloc_515_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_507_);
v___x_509_ = v___x_496_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_fst_494_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_507_);
v___x_509_ = v_reuseFailAlloc_514_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_509_);
v___x_511_ = v___x_492_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_fst_490_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
}
else
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_755_; 
lean_inc(v_stop_504_);
lean_inc(v_start_503_);
lean_inc_ref(v_array_502_);
v_isSharedCheck_755_ = !lean_is_exclusive(v_snd_489_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; 
v_unused_756_ = lean_ctor_get(v_snd_489_, 2);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_snd_489_, 1);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_snd_489_, 0);
lean_dec(v_unused_758_);
v___x_517_ = v_snd_489_;
v_isShared_518_ = v_isSharedCheck_755_;
goto v_resetjp_516_;
}
else
{
lean_dec(v_snd_489_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_755_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_array_fget(v_array_502_, v_start_503_);
lean_inc(v___x_519_);
v___x_520_ = l_Lean_Meta_isProof(v___x_519_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_start_503_, v___x_522_);
lean_dec(v_start_503_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v___x_523_);
v___x_525_ = v___x_517_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_array_502_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_stop_504_);
v___x_525_ = v_reuseFailAlloc_746_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
uint8_t v___x_526_; 
v___x_526_ = lean_unbox(v_a_521_);
if (v___x_526_ == 0)
{
lean_object* v_a_527_; uint8_t v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___x_546_; lean_object* v___y_548_; uint8_t v_privateSpecs_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___x_638_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v_dummy_678_; lean_object* v_nargs_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___x_722_; 
v_a_527_ = lean_array_uget_borrowed(v_as_471_, v_i_473_);
v___x_546_ = l_Lean_Expr_eta(v___x_519_);
v___x_638_ = l_Lean_Expr_getAppFn(v___x_546_);
v_dummy_678_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
v_nargs_679_ = l_Lean_Expr_getAppNumArgs(v___x_546_);
lean_inc(v_nargs_679_);
v___x_680_ = lean_mk_array(v_nargs_679_, v_dummy_678_);
v___x_681_ = lean_nat_sub(v_nargs_679_, v___x_522_);
lean_dec(v_nargs_679_);
lean_inc_ref(v___x_546_);
v___x_682_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_546_, v___x_680_, v___x_681_);
v___x_722_ = l_Lean_Expr_isConst(v___x_638_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_723_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18);
lean_inc(v_a_527_);
v___x_724_ = l_Lean_MessageData_ofName(v_a_527_);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_727_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_dec_ref(v___x_728_);
v___y_693_ = v___y_475_;
v___y_694_ = v___y_476_;
v___y_695_ = v___y_477_;
v___y_696_ = v___y_478_;
goto v___jp_692_;
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_525_);
lean_dec(v_a_521_);
lean_del_object(v___x_500_);
lean_dec(v_fst_498_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
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
v___y_693_ = v___y_475_;
v___y_694_ = v___y_476_;
v___y_695_ = v___y_477_;
v___y_696_ = v___y_478_;
goto v___jp_692_;
}
v___jp_528_:
{
lean_object* v___x_533_; 
lean_inc(v___y_531_);
lean_inc(v_a_527_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___y_531_);
lean_ctor_set(v___x_500_, 0, v_a_527_);
v___x_533_ = v___x_500_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___y_531_);
v___x_533_ = v_reuseFailAlloc_545_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_534_ = lean_array_push(v_fst_490_, v___x_533_);
lean_inc(v___x_469_);
v___x_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_535_, 0, v___y_531_);
lean_ctor_set(v___x_535_, 1, v___x_469_);
lean_ctor_set(v___x_535_, 2, v___y_530_);
v___x_536_ = lean_array_push(v_fst_494_, v___x_535_);
v___x_537_ = lean_box(v___y_529_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_525_);
lean_ctor_set(v___x_496_, 0, v___x_537_);
v___x_539_ = v___x_496_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_525_);
v___x_539_ = v_reuseFailAlloc_544_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_539_);
lean_ctor_set(v___x_492_, 0, v___x_536_);
v___x_541_ = v___x_492_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_539_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_534_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v_a_481_ = v___x_542_;
goto v___jp_480_;
}
}
}
}
v___jp_547_:
{
lean_object* v___x_554_; lean_object* v_env_555_; lean_object* v___x_556_; 
v___x_554_ = lean_st_ref_get(v___y_553_);
v_env_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc_ref(v_env_555_);
lean_dec(v___x_554_);
lean_inc(v_a_527_);
lean_inc(v_val_465_);
v___x_556_ = l_Lean_getFieldInfo_x3f(v_env_555_, v_val_465_, v_a_527_);
if (lean_obj_tag(v___x_556_) == 1)
{
lean_object* v_val_557_; lean_object* v_projFn_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_dummy_562_; lean_object* v_nargs_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_val_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_val_557_);
lean_dec_ref(v___x_556_);
v_projFn_558_ = lean_ctor_get(v_val_557_, 1);
lean_inc(v_projFn_558_);
lean_dec(v_val_557_);
v___x_559_ = l_Lean_Expr_getAppFn(v_a_466_);
v___x_560_ = l_Lean_Expr_constLevels_x21(v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = l_Lean_mkConst(v_projFn_558_, v___x_560_);
v_dummy_562_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
v_nargs_563_ = l_Lean_Expr_getAppNumArgs(v_a_466_);
lean_inc(v_nargs_563_);
v___x_564_ = lean_mk_array(v_nargs_563_, v_dummy_562_);
v___x_565_ = lean_nat_sub(v_nargs_563_, v___x_522_);
lean_dec(v_nargs_563_);
lean_inc_ref(v_a_466_);
v___x_566_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_466_, v___x_564_, v___x_565_);
v___x_567_ = lean_mk_empty_array_with_capacity(v___x_522_);
lean_inc_ref(v___x_467_);
v___x_568_ = lean_array_push(v___x_567_, v___x_467_);
v___x_569_ = l_Array_append___redArg(v___x_566_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = l_Lean_mkAppN(v___x_561_, v___x_569_);
lean_dec_ref(v___x_569_);
lean_inc_ref(v___x_570_);
lean_inc_ref(v___x_546_);
v___x_571_ = l_Lean_Meta_mkEq(v___x_546_, v___x_570_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; uint8_t v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_571_);
v___x_573_ = 1;
v___x_574_ = lean_unbox(v_a_521_);
lean_dec(v_a_521_);
lean_inc(v_a_572_);
v___x_575_ = l_Lean_Meta_mkForallFVars(v_xs_468_, v_a_572_, v___x_574_, v___x_505_, v___x_505_, v___x_573_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref(v___x_575_);
v___x_577_ = l_Lean_Meta_isExprDefEq(v___x_546_, v___x_570_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; uint8_t v___x_579_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___x_577_);
v___x_579_ = lean_unbox(v_a_578_);
lean_dec(v_a_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_580_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2);
v___x_581_ = l_Lean_MessageData_ofExpr(v_a_572_);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_584_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_dec_ref(v___x_585_);
v___y_529_ = v_privateSpecs_549_;
v___y_530_ = v_a_576_;
v___y_531_ = v___y_548_;
goto v___jp_528_;
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_576_);
lean_dec(v___y_548_);
lean_dec_ref(v___x_525_);
lean_del_object(v___x_500_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_dec(v_a_572_);
v___y_529_ = v_privateSpecs_549_;
v___y_530_ = v_a_576_;
v___y_531_ = v___y_548_;
goto v___jp_528_;
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_a_576_);
lean_dec(v_a_572_);
lean_dec(v___y_548_);
lean_dec_ref(v___x_525_);
lean_del_object(v___x_500_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_594_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_577_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_577_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_a_572_);
lean_dec_ref(v___x_570_);
lean_dec(v___y_548_);
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_525_);
lean_del_object(v___x_500_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_602_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_575_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_575_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v___x_570_);
lean_dec(v___y_548_);
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_525_);
lean_dec(v_a_521_);
lean_del_object(v___x_500_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_610_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_571_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_571_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_556_);
lean_dec(v___y_548_);
lean_dec_ref(v___x_546_);
lean_dec(v_a_521_);
lean_del_object(v___x_500_);
lean_del_object(v___x_496_);
lean_del_object(v___x_492_);
v___x_618_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6);
lean_inc(v_a_527_);
v___x_619_ = l_Lean_MessageData_ofName(v_a_527_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_inc(v_val_465_);
v___x_623_ = l_Lean_MessageData_ofName(v_val_465_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_624_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref(v___x_625_);
v___x_626_ = lean_box(v_privateSpecs_549_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_525_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_fst_494_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_fst_490_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v_a_481_ = v___x_629_;
goto v___jp_480_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v___x_525_);
lean_dec(v_fst_494_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_630_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_625_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_625_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
v___jp_639_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_env_646_; lean_object* v_env_647_; lean_object* v___x_648_; uint8_t v_isModule_649_; lean_object* v___x_650_; 
v___x_644_ = lean_st_ref_get(v___y_643_);
v___x_645_ = lean_st_ref_get(v___y_643_);
v_env_646_ = lean_ctor_get(v___x_644_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_644_);
v_env_647_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_647_);
lean_dec(v___x_645_);
v___x_648_ = l_Lean_Environment_header(v_env_646_);
lean_dec_ref(v_env_646_);
v_isModule_649_ = lean_ctor_get_uint8(v___x_648_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_648_);
v___x_650_ = l_Lean_Expr_constName_x21(v___x_638_);
lean_dec_ref(v___x_638_);
if (v_isModule_649_ == 0)
{
uint8_t v___x_651_; 
lean_dec_ref(v_env_647_);
v___x_651_ = lean_unbox(v_fst_498_);
lean_dec(v_fst_498_);
v___y_548_ = v___x_650_;
v_privateSpecs_549_ = v___x_651_;
v___y_550_ = v___y_640_;
v___y_551_ = v___y_641_;
v___y_552_ = v___y_642_;
v___y_553_ = v___y_643_;
goto v___jp_547_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; 
v___x_652_ = l_Lean_Environment_setExporting(v_env_647_, v___x_505_);
v___x_653_ = lean_unbox(v_a_521_);
lean_inc(v___x_650_);
v___x_654_ = l_Lean_Environment_find_x3f(v___x_652_, v___x_650_, v___x_653_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec(v_fst_498_);
v___y_548_ = v___x_650_;
v_privateSpecs_549_ = v___x_505_;
v___y_550_ = v___y_640_;
v___y_551_ = v___y_641_;
v___y_552_ = v___y_642_;
v___y_553_ = v___y_643_;
goto v___jp_547_;
}
else
{
lean_object* v_val_655_; uint8_t v___x_656_; uint8_t v___x_657_; 
v_val_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v___x_654_);
v___x_656_ = lean_unbox(v_a_521_);
v___x_657_ = l_Lean_ConstantInfo_hasValue(v_val_655_, v___x_656_);
lean_dec(v_val_655_);
if (v___x_657_ == 0)
{
lean_dec(v_fst_498_);
v___y_548_ = v___x_650_;
v_privateSpecs_549_ = v___x_505_;
v___y_550_ = v___y_640_;
v___y_551_ = v___y_641_;
v___y_552_ = v___y_642_;
v___y_553_ = v___y_643_;
goto v___jp_547_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_unbox(v_fst_498_);
lean_dec(v_fst_498_);
v___y_548_ = v___x_650_;
v_privateSpecs_549_ = v___x_658_;
v___y_550_ = v___y_640_;
v___y_551_ = v___y_641_;
v___y_552_ = v___y_642_;
v___y_553_ = v___y_643_;
goto v___jp_547_;
}
}
}
}
v___jp_659_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
lean_inc_ref(v___x_638_);
v___x_665_ = l_Lean_MessageData_ofExpr(v___x_638_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_668_, v___y_661_, v___y_662_, v___y_663_, v___y_660_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_dec_ref(v___x_669_);
v___y_640_ = v___y_661_;
v___y_641_ = v___y_662_;
v___y_642_ = v___y_663_;
v___y_643_ = v___y_660_;
goto v___jp_639_;
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_525_);
lean_dec(v_a_521_);
lean_del_object(v___x_500_);
lean_dec(v_fst_498_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
v___jp_683_:
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_array_get_size(v_xs_468_);
v___x_689_ = lean_array_get_size(v___x_682_);
v___x_690_ = lean_nat_dec_eq(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec_ref(v___x_682_);
v___y_660_ = v___y_687_;
v___y_661_ = v___y_684_;
v___y_662_ = v___y_685_;
v___y_663_ = v___y_686_;
goto v___jp_659_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_468_, v___x_682_, v___x_688_);
lean_dec_ref(v___x_682_);
if (v___x_691_ == 0)
{
v___y_660_ = v___y_687_;
v___y_661_ = v___y_684_;
v___y_662_ = v___y_685_;
v___y_663_ = v___y_686_;
goto v___jp_659_;
}
else
{
v___y_640_ = v___y_684_;
v___y_641_ = v___y_685_;
v___y_642_ = v___y_686_;
v___y_643_ = v___y_687_;
goto v___jp_639_;
}
}
}
v___jp_692_:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = l_Lean_Expr_constLevels_x21(v___x_638_);
v___x_698_ = l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(v___x_697_, v___x_470_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
lean_inc_ref(v___x_638_);
v___x_700_ = l_Lean_MessageData_ofExpr(v___x_638_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_box(0);
v___x_705_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_697_, v___x_704_);
v___x_706_ = l_Lean_MessageData_ofList(v___x_705_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_703_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
lean_inc(v___x_470_);
v___x_710_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_470_, v___x_704_);
v___x_711_ = l_Lean_MessageData_ofList(v___x_710_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_709_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_712_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_dec_ref(v___x_713_);
v___y_684_ = v___y_693_;
v___y_685_ = v___y_694_;
v___y_686_ = v___y_695_;
v___y_687_ = v___y_696_;
goto v___jp_683_;
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v___x_682_);
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_525_);
lean_dec(v_a_521_);
lean_del_object(v___x_500_);
lean_dec(v_fst_498_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
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
lean_dec(v___x_697_);
v___y_684_ = v___y_693_;
v___y_685_ = v___y_694_;
v___y_686_ = v___y_695_;
v___y_687_ = v___y_696_;
goto v___jp_683_;
}
}
}
else
{
lean_object* v___x_738_; 
lean_dec(v_a_521_);
lean_dec(v___x_519_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_525_);
v___x_738_ = v___x_500_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_498_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_525_);
v___x_738_ = v_reuseFailAlloc_745_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_738_);
v___x_740_ = v___x_496_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_fst_494_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_740_);
v___x_742_ = v___x_492_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_490_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
v_a_481_ = v___x_742_;
goto v___jp_480_;
}
}
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v___x_519_);
lean_del_object(v___x_517_);
lean_dec(v_stop_504_);
lean_dec(v_start_503_);
lean_dec_ref(v_array_502_);
lean_del_object(v___x_500_);
lean_dec(v_fst_498_);
lean_del_object(v___x_496_);
lean_dec(v_fst_494_);
lean_del_object(v___x_492_);
lean_dec(v_fst_490_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_val_465_);
v_a_747_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_520_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_520_);
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
}
}
}
v___jp_480_:
{
size_t v___x_482_; size_t v___x_483_; 
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_473_, v___x_482_);
v_i_473_ = v___x_483_;
v_b_474_ = v_a_481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___boxed(lean_object* v_val_765_, lean_object* v_a_766_, lean_object* v___x_767_, lean_object* v_xs_768_, lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v_as_771_, lean_object* v_sz_772_, lean_object* v_i_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
size_t v_sz_boxed_780_; size_t v_i_boxed_781_; lean_object* v_res_782_; 
v_sz_boxed_780_ = lean_unbox_usize(v_sz_772_);
lean_dec(v_sz_772_);
v_i_boxed_781_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_765_, v_a_766_, v___x_767_, v_xs_768_, v___x_769_, v___x_770_, v_as_771_, v_sz_boxed_780_, v_i_boxed_781_, v_b_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec_ref(v_as_771_);
lean_dec_ref(v_xs_768_);
return v_res_782_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(lean_object* v_type_810_, lean_object* v_val_811_, lean_object* v_levelParams_812_, lean_object* v_name_813_, lean_object* v_val_814_, uint8_t v___x_815_, lean_object* v_instName_816_, lean_object* v_a_817_, lean_object* v_xs_818_, lean_object* v_body_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_instantiateForall(v_type_810_, v_xs_818_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
lean_inc_ref(v_body_819_);
v___x_857_ = l_Lean_Meta_isConstructorApp(v_body_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
v___x_859_ = lean_box(0);
lean_inc(v_levelParams_812_);
v___x_860_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_812_, v___x_859_);
lean_inc(v___x_860_);
v___x_861_ = l_Lean_mkConst(v_name_813_, v___x_860_);
v___x_862_ = l_Lean_mkAppN(v___x_861_, v_xs_818_);
v___x_963_ = lean_array_get_size(v_xs_818_);
v___x_964_ = lean_nat_dec_eq(v___x_963_, v_a_817_);
if (v___x_964_ == 0)
{
lean_dec_ref(v___x_862_);
lean_dec(v___x_860_);
lean_dec(v_a_858_);
lean_dec(v_a_856_);
lean_dec_ref(v_body_819_);
lean_dec(v_levelParams_812_);
lean_dec(v_val_811_);
goto v___jp_948_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = lean_unbox(v_a_858_);
lean_dec(v_a_858_);
if (v___x_965_ == 0)
{
lean_dec_ref(v___x_862_);
lean_dec(v___x_860_);
lean_dec(v_a_856_);
lean_dec_ref(v_body_819_);
lean_dec(v_levelParams_812_);
lean_dec(v_val_811_);
goto v___jp_948_;
}
else
{
v___y_864_ = v___y_820_;
v___y_865_ = v___y_821_;
v___y_866_ = v___y_822_;
v___y_867_ = v___y_823_;
goto v___jp_863_;
}
}
v___jp_863_:
{
lean_object* v_fieldNames_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_dummy_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; 
v_fieldNames_868_ = lean_ctor_get(v_val_814_, 1);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0));
v___x_871_ = lean_array_get_size(v_fieldNames_868_);
v_dummy_872_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
v___x_873_ = lean_mk_array(v___x_871_, v_dummy_872_);
v___x_874_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v___x_871_, v_body_819_, v___x_873_);
v___x_875_ = lean_array_get_size(v___x_874_);
v___x_876_ = l_Array_toSubarray___redArg(v___x_874_, v___x_869_, v___x_875_);
v___x_877_ = lean_box(v___x_815_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_876_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_870_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_870_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v_sz_881_ = lean_array_size(v_fieldNames_868_);
v___x_882_ = ((size_t)0ULL);
lean_inc(v_val_811_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_811_, v_a_856_, v___x_862_, v_xs_818_, v_levelParams_812_, v___x_860_, v_fieldNames_868_, v_sz_881_, v___x_882_, v___x_880_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_snd_887_; lean_object* v_snd_888_; lean_object* v_a_889_; uint8_t v___x_890_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_886_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg(v___x_885_, v___y_866_);
v_snd_887_ = lean_ctor_get(v_a_884_, 1);
lean_inc(v_snd_887_);
v_snd_888_ = lean_ctor_get(v_snd_887_, 1);
lean_inc(v_snd_888_);
v_a_889_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_886_);
v___x_890_ = lean_unbox(v_a_889_);
lean_dec(v_a_889_);
if (v___x_890_ == 0)
{
lean_object* v_fst_891_; lean_object* v_fst_892_; lean_object* v_fst_893_; 
lean_dec(v_instName_816_);
v_fst_891_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_fst_891_);
lean_dec(v_a_884_);
v_fst_892_ = lean_ctor_get(v_snd_887_, 0);
lean_inc(v_fst_892_);
lean_dec(v_snd_887_);
v_fst_893_ = lean_ctor_get(v_snd_888_, 0);
lean_inc(v_fst_893_);
lean_dec(v_snd_888_);
v___y_826_ = v_fst_891_;
v___y_827_ = v_fst_892_;
v___y_828_ = v_fst_893_;
goto v___jp_825_;
}
else
{
lean_object* v_fst_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_938_; 
v_fst_894_ = lean_ctor_get(v_a_884_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_a_884_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_a_884_, 1);
lean_dec(v_unused_939_);
v___x_896_ = v_a_884_;
v_isShared_897_ = v_isSharedCheck_938_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_fst_894_);
lean_dec(v_a_884_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_938_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_fst_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_936_; 
v_fst_898_ = lean_ctor_get(v_snd_887_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_snd_887_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_snd_887_, 1);
lean_dec(v_unused_937_);
v___x_900_ = v_snd_887_;
v_isShared_901_ = v_isSharedCheck_936_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_fst_898_);
lean_dec(v_snd_887_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_936_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_fst_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_934_; 
v_fst_902_ = lean_ctor_get(v_snd_888_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_snd_888_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_snd_888_, 1);
lean_dec(v_unused_935_);
v___x_904_ = v_snd_888_;
v_isShared_905_ = v_isSharedCheck_934_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_fst_902_);
lean_dec(v_snd_888_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_934_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_906_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5);
v___x_907_ = l_Lean_MessageData_ofName(v_instName_816_);
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 7);
lean_ctor_set(v___x_904_, 1, v___x_907_);
lean_ctor_set(v___x_904_, 0, v___x_906_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_933_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 7);
lean_ctor_set(v___x_900_, 1, v___x_910_);
lean_ctor_set(v___x_900_, 0, v___x_909_);
v___x_912_ = v___x_900_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_932_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
lean_inc(v_fst_894_);
v___x_913_ = lean_array_to_list(v_fst_894_);
v___x_914_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(v___x_913_, v___x_859_);
v___x_915_ = l_Lean_MessageData_ofList(v___x_914_);
if (v_isShared_897_ == 0)
{
lean_ctor_set_tag(v___x_896_, 7);
lean_ctor_set(v___x_896_, 1, v___x_915_);
lean_ctor_set(v___x_896_, 0, v___x_912_);
v___x_917_ = v___x_896_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_915_);
v___x_917_ = v_reuseFailAlloc_931_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; size_t v_sz_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_918_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v_sz_920_ = lean_array_size(v_fst_898_);
lean_inc(v_fst_898_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(v_sz_920_, v___x_882_, v_fst_898_);
v___x_922_ = lean_array_to_list(v___x_921_);
v___x_923_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___x_922_, v___x_859_);
v___x_924_ = l_Lean_MessageData_ofList(v___x_923_);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_919_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_unbox(v_fst_902_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12));
v___y_833_ = v_fst_894_;
v___y_834_ = v_fst_898_;
v___y_835_ = v___y_866_;
v___y_836_ = v___y_864_;
v___y_837_ = v_fst_902_;
v___y_838_ = v___y_865_;
v___y_839_ = v___x_927_;
v___y_840_ = v___y_867_;
v___y_841_ = v___x_885_;
v___y_842_ = v___x_929_;
goto v___jp_832_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13));
v___y_833_ = v_fst_894_;
v___y_834_ = v_fst_898_;
v___y_835_ = v___y_866_;
v___y_836_ = v___y_864_;
v___y_837_ = v_fst_902_;
v___y_838_ = v___y_865_;
v___y_839_ = v___x_927_;
v___y_840_ = v___y_867_;
v___y_841_ = v___x_885_;
v___y_842_ = v___x_930_;
goto v___jp_832_;
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
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_instName_816_);
lean_dec(v_val_811_);
v_a_940_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_883_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_883_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
v___jp_948_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v___x_949_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15);
v___x_950_ = l_Lean_MessageData_ofConstName(v_instName_816_, v___x_815_);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_953_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_856_);
lean_dec_ref(v_body_819_);
lean_dec(v_instName_816_);
lean_dec(v_name_813_);
lean_dec(v_levelParams_812_);
lean_dec(v_val_811_);
v_a_966_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_857_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_857_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v_body_819_);
lean_dec(v_instName_816_);
lean_dec(v_name_813_);
lean_dec(v_levelParams_812_);
lean_dec(v_val_811_);
v_a_974_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_855_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_855_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
v___jp_825_:
{
lean_object* v___x_829_; uint8_t v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_829_, 0, v_val_811_);
lean_ctor_set(v___x_829_, 1, v___y_826_);
lean_ctor_set(v___x_829_, 2, v___y_827_);
v___x_830_ = lean_unbox(v___y_828_);
lean_dec(v___y_828_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*3, v___x_830_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
return v___x_831_;
}
v___jp_832_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_843_, 0, v___y_842_);
v___x_844_ = l_Lean_MessageData_ofFormat(v___x_843_);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___y_839_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(v___y_841_, v___x_845_, v___y_836_, v___y_838_, v___y_835_, v___y_840_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_dec_ref(v___x_846_);
v___y_826_ = v___y_833_;
v___y_827_ = v___y_834_;
v___y_828_ = v___y_837_;
goto v___jp_825_;
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v___y_837_);
lean_dec(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v_val_811_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed(lean_object* v_type_982_, lean_object* v_val_983_, lean_object* v_levelParams_984_, lean_object* v_name_985_, lean_object* v_val_986_, lean_object* v___x_987_, lean_object* v_instName_988_, lean_object* v_a_989_, lean_object* v_xs_990_, lean_object* v_body_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v___x_19770__boxed_997_; lean_object* v_res_998_; 
v___x_19770__boxed_997_ = lean_unbox(v___x_987_);
v_res_998_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(v_type_982_, v_val_983_, v_levelParams_984_, v_name_985_, v_val_986_, v___x_19770__boxed_997_, v_instName_988_, v_a_989_, v_xs_990_, v_body_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_xs_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_val_986_);
return v_res_998_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_instMonadEIO(lean_box(0));
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_toApplicative_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1073_; 
v___x_1010_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0);
v___x_1011_ = l_StateRefT_x27_instMonad___redArg(v___x_1010_);
v_toApplicative_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v___x_1011_, 1);
lean_dec(v_unused_1074_);
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1073_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_toApplicative_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1073_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_toFunctor_1016_; lean_object* v_toSeq_1017_; lean_object* v_toSeqLeft_1018_; lean_object* v_toSeqRight_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1071_; 
v_toFunctor_1016_ = lean_ctor_get(v_toApplicative_1012_, 0);
v_toSeq_1017_ = lean_ctor_get(v_toApplicative_1012_, 2);
v_toSeqLeft_1018_ = lean_ctor_get(v_toApplicative_1012_, 3);
v_toSeqRight_1019_ = lean_ctor_get(v_toApplicative_1012_, 4);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_toApplicative_1012_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_toApplicative_1012_, 1);
lean_dec(v_unused_1072_);
v___x_1021_ = v_toApplicative_1012_;
v_isShared_1022_ = v_isSharedCheck_1071_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_toSeqRight_1019_);
lean_inc(v_toSeqLeft_1018_);
lean_inc(v_toSeq_1017_);
lean_inc(v_toFunctor_1016_);
lean_dec(v_toApplicative_1012_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1071_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_1032_; 
v___f_1023_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1));
v___f_1024_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1016_);
v___f_1025_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1025_, 0, v_toFunctor_1016_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toFunctor_1016_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___f_1025_);
lean_ctor_set(v___x_1027_, 1, v___f_1026_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toSeqRight_1019_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toSeqLeft_1018_);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toSeq_1017_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 4, v___f_1028_);
lean_ctor_set(v___x_1021_, 3, v___f_1029_);
lean_ctor_set(v___x_1021_, 2, v___f_1030_);
lean_ctor_set(v___x_1021_, 1, v___f_1023_);
lean_ctor_set(v___x_1021_, 0, v___x_1027_);
v___x_1032_ = v___x_1021_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___f_1023_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v___f_1029_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___f_1028_);
v___x_1032_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___f_1024_);
lean_ctor_set(v___x_1014_, 0, v___x_1032_);
v___x_1034_ = v___x_1014_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1024_);
v___x_1034_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v_toApplicative_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1067_; 
v___x_1035_ = l_StateRefT_x27_instMonad___redArg(v___x_1034_);
v_toApplicative_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1035_, 1);
lean_dec(v_unused_1068_);
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1067_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_toApplicative_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1067_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_toFunctor_1040_; lean_object* v_toSeq_1041_; lean_object* v_toSeqLeft_1042_; lean_object* v_toSeqRight_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1065_; 
v_toFunctor_1040_ = lean_ctor_get(v_toApplicative_1036_, 0);
v_toSeq_1041_ = lean_ctor_get(v_toApplicative_1036_, 2);
v_toSeqLeft_1042_ = lean_ctor_get(v_toApplicative_1036_, 3);
v_toSeqRight_1043_ = lean_ctor_get(v_toApplicative_1036_, 4);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_toApplicative_1036_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v_toApplicative_1036_, 1);
lean_dec(v_unused_1066_);
v___x_1045_ = v_toApplicative_1036_;
v_isShared_1046_ = v_isSharedCheck_1065_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_toSeqRight_1043_);
lean_inc(v_toSeqLeft_1042_);
lean_inc(v_toSeq_1041_);
lean_inc(v_toFunctor_1040_);
lean_dec(v_toApplicative_1036_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1065_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1056_; 
v___f_1047_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3));
v___f_1048_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1040_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toFunctor_1040_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toFunctor_1040_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___f_1049_);
lean_ctor_set(v___x_1051_, 1, v___f_1050_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toSeqRight_1043_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toSeqLeft_1042_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toSeq_1041_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 4, v___f_1052_);
lean_ctor_set(v___x_1045_, 3, v___f_1053_);
lean_ctor_set(v___x_1045_, 2, v___f_1054_);
lean_ctor_set(v___x_1045_, 1, v___f_1047_);
lean_ctor_set(v___x_1045_, 0, v___x_1051_);
v___x_1056_ = v___x_1045_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___f_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v___f_1054_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v___f_1053_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___f_1052_);
v___x_1056_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___f_1048_);
lean_ctor_set(v___x_1038_, 0, v___x_1056_);
v___x_1058_ = v___x_1038_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___f_1048_);
v___x_1058_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_17446__overap_1061_; lean_object* v___x_1062_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = l_instInhabitedOfMonad___redArg(v___x_1058_, v___x_1059_);
v___x_17446__overap_1061_ = lean_panic_fn(v___x_1060_, v_msg_1004_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
v___x_1062_ = lean_apply_5(v___x_17446__overap_1061_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, lean_box(0));
return v___x_1062_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___boxed(lean_object* v_msg_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v_msg_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1091_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6));
v___x_1092_ = lean_unsigned_to_nat(11u);
v___x_1093_ = lean_unsigned_to_nat(115u);
v___x_1094_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5));
v___x_1095_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4));
v___x_1096_ = l_mkPanicMessageWithDecl(v___x_1095_, v___x_1094_, v___x_1093_, v___x_1092_, v___x_1091_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(lean_object* v_constName_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1111_ = lean_st_ref_get(v___y_1101_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = 0;
lean_inc(v_constName_1097_);
v___x_1114_ = l_Lean_Environment_findAsync_x3f(v_env_1112_, v_constName_1097_, v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 1)
{
lean_object* v_val_1115_; uint8_t v_kind_1116_; 
v_val_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1115_);
lean_dec_ref(v___x_1114_);
v_kind_1116_ = lean_ctor_get_uint8(v_val_1115_, sizeof(void*)*3);
if (v_kind_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1115_);
if (lean_obj_tag(v___x_1117_) == 1)
{
lean_object* v_val_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_constName_1097_);
v_val_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_val_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 0);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_val_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref(v___x_1117_);
v___x_1126_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7);
v___x_1127_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v___x_1126_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
if (lean_obj_tag(v_a_1128_) == 0)
{
lean_del_object(v___x_1130_);
goto v___jp_1103_;
}
else
{
lean_object* v_val_1132_; lean_object* v___x_1134_; 
lean_dec(v_constName_1097_);
v_val_1132_ = lean_ctor_get(v_a_1128_, 0);
lean_inc(v_val_1132_);
lean_dec_ref(v_a_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v_val_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_val_1132_);
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
lean_dec(v_constName_1097_);
v_a_1137_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1127_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1127_);
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
lean_dec(v_val_1115_);
goto v___jp_1103_;
}
}
else
{
lean_dec(v___x_1114_);
goto v___jp_1103_;
}
v___jp_1103_:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1104_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
v___x_1105_ = 0;
v___x_1106_ = l_Lean_MessageData_ofConstName(v_constName_1097_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_1109_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___boxed(lean_object* v_constName_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_constName_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1151_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3));
v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
return v___x_1158_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5));
v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(lean_object* v_instName_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; 
lean_inc(v_instName_1165_);
v___x_1171_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_instName_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_toConstantVal_1173_; lean_object* v_value_1174_; lean_object* v_name_1175_; lean_object* v_levelParams_1176_; lean_object* v_type_1177_; lean_object* v___x_1178_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref(v___x_1171_);
v_toConstantVal_1173_ = lean_ctor_get(v_a_1172_, 0);
lean_inc_ref(v_toConstantVal_1173_);
v_value_1174_ = lean_ctor_get(v_a_1172_, 1);
lean_inc_ref(v_value_1174_);
lean_dec(v_a_1172_);
v_name_1175_ = lean_ctor_get(v_toConstantVal_1173_, 0);
lean_inc(v_name_1175_);
v_levelParams_1176_ = lean_ctor_get(v_toConstantVal_1173_, 1);
lean_inc(v_levelParams_1176_);
v_type_1177_ = lean_ctor_get(v_toConstantVal_1173_, 2);
lean_inc_ref(v_type_1177_);
lean_dec_ref(v_toConstantVal_1173_);
lean_inc_ref(v_type_1177_);
v___x_1178_ = l_Lean_Meta_isClass_x3f(v_type_1177_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref(v___x_1178_);
if (lean_obj_tag(v_a_1179_) == 1)
{
lean_object* v_val_1180_; lean_object* v___f_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v_val_1180_ = lean_ctor_get(v_a_1179_, 0);
lean_inc(v_val_1180_);
lean_dec_ref(v_a_1179_);
v___f_1181_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0));
v___x_1182_ = 0;
lean_inc_ref(v_type_1177_);
v___x_1183_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_1177_, v___f_1181_, v___x_1182_, v___x_1182_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v___x_1187_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = lean_st_ref_get(v_a_1169_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
lean_inc(v_val_1180_);
v___x_1187_ = l_Lean_getStructureInfo_x3f(v_env_1186_, v_val_1180_);
if (lean_obj_tag(v___x_1187_) == 1)
{
lean_object* v_val_1188_; lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; 
v_val_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_val_1188_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = lean_box(v___x_1182_);
v___f_1190_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1190_, 0, v_type_1177_);
lean_closure_set(v___f_1190_, 1, v_val_1180_);
lean_closure_set(v___f_1190_, 2, v_levelParams_1176_);
lean_closure_set(v___f_1190_, 3, v_name_1175_);
lean_closure_set(v___f_1190_, 4, v_val_1188_);
lean_closure_set(v___f_1190_, 5, v___x_1189_);
lean_closure_set(v___f_1190_, 6, v_instName_1165_);
lean_closure_set(v___f_1190_, 7, v_a_1184_);
v___x_1191_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__13___redArg(v_value_1174_, v___f_1190_, v___x_1182_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec(v___x_1187_);
lean_dec(v_a_1184_);
lean_dec_ref(v_type_1177_);
lean_dec(v_levelParams_1176_);
lean_dec(v_name_1175_);
lean_dec_ref(v_value_1174_);
lean_dec(v_instName_1165_);
v___x_1192_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
v___x_1193_ = l_Lean_MessageData_ofConstName(v_val_1180_, v___x_1182_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_1196_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1197_;
}
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v_val_1180_);
lean_dec_ref(v_type_1177_);
lean_dec(v_levelParams_1176_);
lean_dec(v_name_1175_);
lean_dec_ref(v_value_1174_);
lean_dec(v_instName_1165_);
v_a_1198_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1183_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1183_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v_a_1179_);
lean_dec(v_levelParams_1176_);
lean_dec(v_name_1175_);
lean_dec_ref(v_value_1174_);
v___x_1206_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4);
v___x_1207_ = 0;
v___x_1208_ = l_Lean_MessageData_ofConstName(v_instName_1165_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1206_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(30u);
v___x_1213_ = l_Lean_inlineExpr(v_type_1177_, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1211_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_1216_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1217_;
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v_type_1177_);
lean_dec(v_levelParams_1176_);
lean_dec(v_name_1175_);
lean_dec_ref(v_value_1174_);
lean_dec(v_instName_1165_);
v_a_1218_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1178_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1178_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_instName_1165_);
v_a_1226_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1171_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1171_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___boxed(lean_object* v_instName_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(lean_object* v_00_u03b1_1241_, lean_object* v_msg_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(v_00_u03b1_1249_, v_msg_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1256_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(lean_object* v_xs_1257_, lean_object* v_ys_1258_, lean_object* v_hsz_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_1257_, v_ys_1258_, v_x_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___boxed(lean_object* v_xs_1263_, lean_object* v_ys_1264_, lean_object* v_hsz_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(v_xs_1263_, v_ys_1264_, v_hsz_1265_, v_x_1266_, v_x_1267_);
lean_dec_ref(v_ys_1264_);
lean_dec_ref(v_xs_1263_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
static uint64_t _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_1281_; uint64_t v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0));
v___x_1282_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1281_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2(void){
_start:
{
uint64_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_uint64_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1);
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0));
v___x_1285_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set_uint64(v___x_1285_, sizeof(void*)*1, v___x_1283_);
return v___x_1285_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_unsigned_to_nat(32u);
v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6(void){
_start:
{
size_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((size_t)5ULL);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_unsigned_to_nat(32u);
v___x_1295_ = lean_mk_empty_array_with_capacity(v___x_1294_);
v___x_1296_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5);
v___x_1297_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v___x_1295_);
lean_ctor_set(v___x_1297_, 2, v___x_1293_);
lean_ctor_set(v___x_1297_, 3, v___x_1293_);
lean_ctor_set_usize(v___x_1297_, 4, v___x_1292_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_box(1);
v___x_1299_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_1300_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
lean_ctor_set(v___x_1301_, 2, v___x_1298_);
return v___x_1301_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9(void){
_start:
{
uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1304_ = 1;
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_box(0);
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8));
v___x_1308_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7);
v___x_1309_ = lean_box(1);
v___x_1310_ = 0;
v___x_1311_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2);
v___x_1312_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1309_);
lean_ctor_set(v___x_1312_, 2, v___x_1308_);
lean_ctor_set(v___x_1312_, 3, v___x_1307_);
lean_ctor_set(v___x_1312_, 4, v___x_1306_);
lean_ctor_set(v___x_1312_, 5, v___x_1305_);
lean_ctor_set(v___x_1312_, 6, v___x_1306_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*7, v___x_1310_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*7 + 1, v___x_1310_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*7 + 2, v___x_1310_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*7 + 3, v___x_1304_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set(v___x_1315_, 2, v___x_1314_);
lean_ctor_set(v___x_1315_, 3, v___x_1313_);
lean_ctor_set(v___x_1315_, 4, v___x_1313_);
lean_ctor_set(v___x_1315_, 5, v___x_1313_);
lean_ctor_set(v___x_1315_, 6, v___x_1313_);
lean_ctor_set(v___x_1315_, 7, v___x_1313_);
lean_ctor_set(v___x_1315_, 8, v___x_1313_);
return v___x_1315_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1317_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
lean_ctor_set(v___x_1317_, 2, v___x_1316_);
lean_ctor_set(v___x_1317_, 3, v___x_1316_);
lean_ctor_set(v___x_1317_, 4, v___x_1316_);
lean_ctor_set(v___x_1317_, 5, v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
lean_ctor_set(v___x_1319_, 2, v___x_1318_);
lean_ctor_set(v___x_1319_, 3, v___x_1318_);
lean_ctor_set(v___x_1319_, 4, v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1320_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12);
v___x_1321_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_1322_ = lean_box(1);
v___x_1323_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11);
v___x_1324_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10);
v___x_1325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
lean_ctor_set(v___x_1325_, 2, v___x_1322_);
lean_ctor_set(v___x_1325_, 3, v___x_1321_);
lean_ctor_set(v___x_1325_, 4, v___x_1320_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(lean_object* v_instName_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_a_1331_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1336_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9);
v___x_1337_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13);
v___x_1338_ = lean_st_mk_ref(v___x_1337_);
v___x_1339_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_1326_, v___x_1336_, v___x_1338_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_st_ref_get(v___x_1338_);
lean_dec(v___x_1338_);
lean_dec(v___x_1341_);
v_a_1331_ = v_a_1340_;
goto v___jp_1330_;
}
else
{
lean_dec(v___x_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1342_; 
v_a_1342_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1339_);
v_a_1331_ = v_a_1342_;
goto v___jp_1330_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1339_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1339_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
v___jp_1330_:
{
lean_object* v_clsName_1332_; uint8_t v_privateSpecs_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_clsName_1332_ = lean_ctor_get(v_a_1331_, 0);
lean_inc(v_clsName_1332_);
v_privateSpecs_1333_ = lean_ctor_get_uint8(v_a_1331_, sizeof(void*)*3);
lean_dec_ref(v_a_1331_);
v___x_1334_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1334_, 0, v_clsName_1332_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*1, v_privateSpecs_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___boxed(lean_object* v_instName_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(v_instName_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(lean_object* v_instName_1356_, lean_object* v___stx_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(v_instName_1356_, v_a_1358_, v_a_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed(lean_object* v_instName_1362_, lean_object* v___stx_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(v_instName_1362_, v___stx_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v___stx_1363_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v_x_1375_, v_x_1376_, v_x_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v_x_1377_);
lean_dec_ref(v_x_1376_);
lean_dec(v_x_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT uint8_t l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(uint8_t v___x_1381_, lean_object* v_env_1382_, lean_object* v_n_1383_, lean_object* v_x_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = l_Lean_Environment_contains(v_env_1382_, v_n_1383_, v___x_1381_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object* v___x_1386_, lean_object* v_env_1387_, lean_object* v_n_1388_, lean_object* v_x_1389_){
_start:
{
uint8_t v___x_98__boxed_1390_; uint8_t v_res_1391_; lean_object* v_r_1392_; 
v___x_98__boxed_1390_ = lean_unbox(v___x_1386_);
v_res_1391_ = l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v___x_98__boxed_1390_, v_env_1387_, v_n_1388_, v_x_1389_);
lean_dec_ref(v_x_1389_);
v_r_1392_ = lean_box(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_));
v___x_1420_ = l_Lean_registerParametricAttribute___redArg(v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1(){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__7));
v___x_1448_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__8));
v___x_1449_ = l_Lean_addBuiltinDocString(v___x_1447_, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___boxed(lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1461_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_));
v___x_1462_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_));
v___x_1463_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_));
v___x_1464_ = l_Lean_Meta_registerSimpAttr(v___x_1461_, v___x_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2____boxed(lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(lean_object* v_env_1467_, lean_object* v_instName_1468_, uint8_t v_privateSpecs_1469_, lean_object* v_suffix_1470_){
_start:
{
lean_object* v_thmName_1471_; 
v_thmName_1471_ = l_Lean_Name_str___override(v_instName_1468_, v_suffix_1470_);
if (v_privateSpecs_1469_ == 0)
{
return v_thmName_1471_;
}
else
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_mkPrivateName(v_env_1467_, v_thmName_1471_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName___boxed(lean_object* v_env_1473_, lean_object* v_instName_1474_, lean_object* v_privateSpecs_1475_, lean_object* v_suffix_1476_){
_start:
{
uint8_t v_privateSpecs_boxed_1477_; lean_object* v_res_1478_; 
v_privateSpecs_boxed_1477_ = lean_unbox(v_privateSpecs_1475_);
v_res_1478_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_1473_, v_instName_1474_, v_privateSpecs_boxed_1477_, v_suffix_1476_);
lean_dec_ref(v_env_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(lean_object* v_s_1479_, lean_object* v_p_1480_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = lean_string_utf8_byte_size(v_s_1479_);
v___x_1482_ = lean_string_utf8_byte_size(v_p_1480_);
v___x_1483_ = lean_nat_dec_le(v___x_1482_, v___x_1481_);
if (v___x_1483_ == 0)
{
lean_dec_ref(v_s_1479_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_string_memcmp(v_s_1479_, v_p_1480_, v___x_1484_, v___x_1484_, v___x_1482_);
if (v___x_1485_ == 0)
{
lean_dec_ref(v_s_1479_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1486_ = lean_string_length(v_p_1480_);
lean_inc_ref(v_s_1479_);
v___x_1487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1487_, 0, v_s_1479_);
lean_ctor_set(v___x_1487_, 1, v___x_1484_);
lean_ctor_set(v___x_1487_, 2, v___x_1481_);
v___x_1488_ = l_String_Slice_Pos_nextn(v___x_1487_, v___x_1484_, v___x_1486_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1489_, 0, v_s_1479_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_ctor_set(v___x_1489_, 2, v___x_1481_);
v___x_1490_ = l_String_Slice_isNat(v___x_1489_);
lean_dec_ref(v___x_1489_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber___boxed(lean_object* v_s_1491_, lean_object* v_p_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(v_s_1491_, v_p_1492_);
lean_dec_ref(v_p_1492_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(lean_object* v_fieldName_1497_, lean_object* v_s_1498_){
_start:
{
uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1499_ = 1;
v___x_1500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_1497_, v___x_1499_);
v___x_1501_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
lean_inc_ref(v___x_1500_);
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_string_dec_eq(v_s_1498_, v___x_1502_);
lean_dec_ref(v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1));
v___x_1505_ = lean_string_append(v___x_1500_, v___x_1504_);
v___x_1506_ = l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(v_s_1498_, v___x_1505_);
lean_dec_ref(v___x_1505_);
return v___x_1506_;
}
else
{
lean_dec_ref(v___x_1500_);
lean_dec_ref(v_s_1498_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___boxed(lean_object* v_fieldName_1507_, lean_object* v_s_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(v_fieldName_1507_, v_s_1508_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(lean_object* v_str_1514_, lean_object* v_val_1515_, lean_object* v_env_1516_, lean_object* v_p_1517_, lean_object* v_name_1518_, lean_object* v_as_1519_, size_t v_sz_1520_, size_t v_i_1521_, lean_object* v_b_1522_){
_start:
{
lean_object* v_a_1524_; uint8_t v___x_1528_; 
v___x_1528_ = lean_usize_dec_lt(v_i_1521_, v_sz_1520_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec(v_p_1517_);
lean_dec_ref(v_str_1514_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v_b_1522_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_a_1532_; uint8_t v___x_1533_; 
lean_dec_ref(v_b_1522_);
v___x_1530_ = lean_box(0);
v___x_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0));
v_a_1532_ = lean_array_uget_borrowed(v_as_1519_, v_i_1521_);
lean_inc_ref(v_str_1514_);
lean_inc(v_a_1532_);
v___x_1533_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(v_a_1532_, v_str_1514_);
if (v___x_1533_ == 0)
{
v_a_1524_ = v___x_1531_;
goto v___jp_1523_;
}
else
{
uint8_t v_privateSpecs_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_privateSpecs_1534_ = lean_ctor_get_uint8(v_val_1515_, sizeof(void*)*1);
lean_inc_ref(v_str_1514_);
lean_inc(v_p_1517_);
v___x_1535_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_1516_, v_p_1517_, v_privateSpecs_1534_, v_str_1514_);
v___x_1536_ = lean_name_eq(v_name_1518_, v___x_1535_);
lean_dec(v___x_1535_);
if (v___x_1536_ == 0)
{
v_a_1524_ = v___x_1531_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec_ref(v_str_1514_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_p_1517_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1530_);
v___x_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
}
v___jp_1523_:
{
size_t v___x_1525_; size_t v___x_1526_; 
v___x_1525_ = ((size_t)1ULL);
v___x_1526_ = lean_usize_add(v_i_1521_, v___x_1525_);
v_i_1521_ = v___x_1526_;
v_b_1522_ = v_a_1524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___boxed(lean_object* v_str_1540_, lean_object* v_val_1541_, lean_object* v_env_1542_, lean_object* v_p_1543_, lean_object* v_name_1544_, lean_object* v_as_1545_, lean_object* v_sz_1546_, lean_object* v_i_1547_, lean_object* v_b_1548_){
_start:
{
size_t v_sz_boxed_1549_; size_t v_i_boxed_1550_; lean_object* v_res_1551_; 
v_sz_boxed_1549_ = lean_unbox_usize(v_sz_1546_);
lean_dec(v_sz_1546_);
v_i_boxed_1550_ = lean_unbox_usize(v_i_1547_);
lean_dec(v_i_1547_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_1540_, v_val_1541_, v_env_1542_, v_p_1543_, v_name_1544_, v_as_1545_, v_sz_boxed_1549_, v_i_boxed_1550_, v_b_1548_);
lean_dec_ref(v_as_1545_);
lean_dec(v_name_1544_);
lean_dec_ref(v_env_1542_);
lean_dec_ref(v_val_1541_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(lean_object* v_env_1552_, lean_object* v_str_1553_, lean_object* v_name_1554_, lean_object* v_x_1555_){
_start:
{
if (lean_obj_tag(v_x_1555_) == 0)
{
lean_object* v___x_1556_; 
lean_dec_ref(v_str_1553_);
lean_dec_ref(v_env_1552_);
v___x_1556_ = lean_box(0);
return v___x_1556_;
}
else
{
lean_object* v_head_1557_; lean_object* v_tail_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_head_1557_ = lean_ctor_get(v_x_1555_, 0);
lean_inc(v_head_1557_);
v_tail_1558_ = lean_ctor_get(v_x_1555_, 1);
lean_inc(v_tail_1558_);
lean_dec_ref(v_x_1555_);
v___x_1559_ = ((lean_object*)(l_Lean_instInhabitedMethodSpecsAttrData_default));
v___x_1560_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
lean_inc(v_head_1557_);
lean_inc_ref(v_env_1552_);
v___x_1561_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1559_, v___x_1560_, v_env_1552_, v_head_1557_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_dec(v_head_1557_);
v_x_1555_ = v_tail_1558_;
goto _start;
}
else
{
lean_object* v_val_1563_; lean_object* v_clsName_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; size_t v_sz_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_val_1563_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_val_1563_);
lean_dec_ref(v___x_1561_);
v_clsName_1564_ = lean_ctor_get(v_val_1563_, 0);
lean_inc(v_clsName_1564_);
lean_inc_ref(v_env_1552_);
v___x_1565_ = l_Lean_getStructureFields(v_env_1552_, v_clsName_1564_);
v___x_1566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0));
v_sz_1567_ = lean_array_size(v___x_1565_);
v___x_1568_ = ((size_t)0ULL);
lean_inc_ref(v_str_1553_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_1553_, v_val_1563_, v_env_1552_, v_head_1557_, v_name_1554_, v___x_1565_, v_sz_1567_, v___x_1568_, v___x_1566_);
lean_dec_ref(v___x_1565_);
lean_dec(v_val_1563_);
if (lean_obj_tag(v___x_1569_) == 0)
{
v_x_1555_ = v_tail_1558_;
goto _start;
}
else
{
lean_object* v_val_1571_; lean_object* v_fst_1572_; 
v_val_1571_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1571_);
lean_dec_ref(v___x_1569_);
v_fst_1572_ = lean_ctor_get(v_val_1571_, 0);
lean_inc(v_fst_1572_);
lean_dec(v_val_1571_);
if (lean_obj_tag(v_fst_1572_) == 0)
{
v_x_1555_ = v_tail_1558_;
goto _start;
}
else
{
lean_dec(v_tail_1558_);
lean_dec_ref(v_str_1553_);
lean_dec_ref(v_env_1552_);
return v_fst_1572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1___boxed(lean_object* v_env_1574_, lean_object* v_str_1575_, lean_object* v_name_1576_, lean_object* v_x_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(v_env_1574_, v_str_1575_, v_name_1576_, v_x_1577_);
lean_dec(v_name_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(lean_object* v_env_1579_, lean_object* v_name_1580_){
_start:
{
if (lean_obj_tag(v_name_1580_) == 1)
{
lean_object* v_pre_1581_; lean_object* v_str_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_pre_1581_ = lean_ctor_get(v_name_1580_, 0);
v_str_1582_ = lean_ctor_get(v_name_1580_, 1);
lean_inc_ref(v_str_1582_);
lean_inc(v_pre_1581_);
v___x_1583_ = l_Lean_privateToUserName(v_pre_1581_);
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
lean_inc(v_pre_1581_);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_pre_1581_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(v_env_1579_, v_str_1582_, v_name_1580_, v___x_1586_);
lean_dec_ref(v_name_1580_);
return v___x_1587_;
}
else
{
lean_object* v___x_1588_; 
lean_dec(v_name_1580_);
lean_dec_ref(v_env_1579_);
v___x_1588_ = lean_box(0);
return v___x_1588_;
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
lean_ctor_set(v___x_1594_, 2, v___x_1593_);
lean_ctor_set(v___x_1594_, 3, v___x_1592_);
lean_ctor_set(v___x_1594_, 4, v___x_1592_);
lean_ctor_set(v___x_1594_, 5, v___x_1592_);
lean_ctor_set(v___x_1594_, 6, v___x_1592_);
lean_ctor_set(v___x_1594_, 7, v___x_1592_);
lean_ctor_set(v___x_1594_, 8, v___x_1592_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = lean_box(1);
v___x_1596_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_1597_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1596_);
lean_ctor_set(v___x_1598_, 2, v___x_1595_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1604_ = l_Lean_stringToMessageData(v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1619_ = l_Lean_stringToMessageData(v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1620_, lean_object* v_declHint_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; lean_object* v_env_1625_; uint8_t v___x_1626_; 
v___x_1624_ = lean_st_ref_get(v___y_1622_);
v_env_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc_ref(v_env_1625_);
lean_dec(v___x_1624_);
v___x_1626_ = l_Lean_Name_isAnonymous(v_declHint_1621_);
if (v___x_1626_ == 0)
{
uint8_t v_isExporting_1627_; 
v_isExporting_1627_ = lean_ctor_get_uint8(v_env_1625_, sizeof(void*)*8);
if (v_isExporting_1627_ == 0)
{
lean_object* v___x_1628_; 
lean_dec_ref(v_env_1625_);
lean_dec(v_declHint_1621_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v_msg_1620_);
return v___x_1628_;
}
else
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
lean_inc_ref(v_env_1625_);
v___x_1629_ = l_Lean_Environment_setExporting(v_env_1625_, v___x_1626_);
lean_inc(v_declHint_1621_);
lean_inc_ref(v___x_1629_);
v___x_1630_ = l_Lean_Environment_contains(v___x_1629_, v_declHint_1621_, v_isExporting_1627_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_dec_ref(v___x_1629_);
lean_dec_ref(v_env_1625_);
lean_dec(v_declHint_1621_);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_msg_1620_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_c_1637_; lean_object* v___x_1638_; 
v___x_1632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1633_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1634_ = l_Lean_Options_empty;
v___x_1635_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1629_);
lean_ctor_set(v___x_1635_, 1, v___x_1632_);
lean_ctor_set(v___x_1635_, 2, v___x_1633_);
lean_ctor_set(v___x_1635_, 3, v___x_1634_);
lean_inc(v_declHint_1621_);
v___x_1636_ = l_Lean_MessageData_ofConstName(v_declHint_1621_, v___x_1626_);
v_c_1637_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1637_, 0, v___x_1635_);
lean_ctor_set(v_c_1637_, 1, v___x_1636_);
v___x_1638_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1625_, v_declHint_1621_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec_ref(v_env_1625_);
lean_dec(v_declHint_1621_);
v___x_1639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_c_1637_);
v___x_1641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Lean_MessageData_note(v___x_1642_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_msg_1620_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
return v___x_1645_;
}
else
{
lean_object* v_val_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1681_; 
v_val_1646_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1648_ = v___x_1638_;
v_isShared_1649_ = v_isSharedCheck_1681_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_val_1646_);
lean_dec(v___x_1638_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1681_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_mod_1653_; uint8_t v___x_1654_; 
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Lean_Environment_header(v_env_1625_);
lean_dec_ref(v_env_1625_);
v___x_1652_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1651_);
v_mod_1653_ = lean_array_get(v___x_1650_, v___x_1652_, v_val_1646_);
lean_dec(v_val_1646_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = l_Lean_isPrivateName(v_declHint_1621_);
lean_dec(v_declHint_1621_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1655_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v_c_1637_);
v___x_1657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = l_Lean_MessageData_ofName(v_mod_1653_);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_MessageData_note(v___x_1662_);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_msg_1620_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1664_);
v___x_1666_ = v___x_1648_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v_c_1637_);
v___x_1670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_MessageData_ofName(v_mod_1653_);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_MessageData_note(v___x_1675_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_msg_1620_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1677_);
v___x_1679_ = v___x_1648_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1682_; 
lean_dec_ref(v_env_1625_);
lean_dec(v_declHint_1621_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_msg_1620_);
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1683_, lean_object* v_declHint_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1683_, v_declHint_1684_, v___y_1685_);
lean_dec(v___y_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1688_, lean_object* v_declHint_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1705_; 
v___x_1695_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1688_, v_declHint_1689_, v___y_1693_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1705_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1705_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1700_ = l_Lean_unknownIdentifierMessageTag;
v___x_1701_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v_a_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1701_);
v___x_1703_ = v___x_1698_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1706_, lean_object* v_declHint_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1706_, v_declHint_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1714_, lean_object* v_msg_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_fileName_1721_; lean_object* v_fileMap_1722_; lean_object* v_options_1723_; lean_object* v_currRecDepth_1724_; lean_object* v_maxRecDepth_1725_; lean_object* v_ref_1726_; lean_object* v_currNamespace_1727_; lean_object* v_openDecls_1728_; lean_object* v_initHeartbeats_1729_; lean_object* v_maxHeartbeats_1730_; lean_object* v_quotContext_1731_; lean_object* v_currMacroScope_1732_; uint8_t v_diag_1733_; lean_object* v_cancelTk_x3f_1734_; uint8_t v_suppressElabErrors_1735_; lean_object* v_inheritedTraceOptions_1736_; lean_object* v_ref_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_fileName_1721_ = lean_ctor_get(v___y_1718_, 0);
v_fileMap_1722_ = lean_ctor_get(v___y_1718_, 1);
v_options_1723_ = lean_ctor_get(v___y_1718_, 2);
v_currRecDepth_1724_ = lean_ctor_get(v___y_1718_, 3);
v_maxRecDepth_1725_ = lean_ctor_get(v___y_1718_, 4);
v_ref_1726_ = lean_ctor_get(v___y_1718_, 5);
v_currNamespace_1727_ = lean_ctor_get(v___y_1718_, 6);
v_openDecls_1728_ = lean_ctor_get(v___y_1718_, 7);
v_initHeartbeats_1729_ = lean_ctor_get(v___y_1718_, 8);
v_maxHeartbeats_1730_ = lean_ctor_get(v___y_1718_, 9);
v_quotContext_1731_ = lean_ctor_get(v___y_1718_, 10);
v_currMacroScope_1732_ = lean_ctor_get(v___y_1718_, 11);
v_diag_1733_ = lean_ctor_get_uint8(v___y_1718_, sizeof(void*)*14);
v_cancelTk_x3f_1734_ = lean_ctor_get(v___y_1718_, 12);
v_suppressElabErrors_1735_ = lean_ctor_get_uint8(v___y_1718_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1736_ = lean_ctor_get(v___y_1718_, 13);
v_ref_1737_ = l_Lean_replaceRef(v_ref_1714_, v_ref_1726_);
lean_inc_ref(v_inheritedTraceOptions_1736_);
lean_inc(v_cancelTk_x3f_1734_);
lean_inc(v_currMacroScope_1732_);
lean_inc(v_quotContext_1731_);
lean_inc(v_maxHeartbeats_1730_);
lean_inc(v_initHeartbeats_1729_);
lean_inc(v_openDecls_1728_);
lean_inc(v_currNamespace_1727_);
lean_inc(v_maxRecDepth_1725_);
lean_inc(v_currRecDepth_1724_);
lean_inc_ref(v_options_1723_);
lean_inc_ref(v_fileMap_1722_);
lean_inc_ref(v_fileName_1721_);
v___x_1738_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1738_, 0, v_fileName_1721_);
lean_ctor_set(v___x_1738_, 1, v_fileMap_1722_);
lean_ctor_set(v___x_1738_, 2, v_options_1723_);
lean_ctor_set(v___x_1738_, 3, v_currRecDepth_1724_);
lean_ctor_set(v___x_1738_, 4, v_maxRecDepth_1725_);
lean_ctor_set(v___x_1738_, 5, v_ref_1737_);
lean_ctor_set(v___x_1738_, 6, v_currNamespace_1727_);
lean_ctor_set(v___x_1738_, 7, v_openDecls_1728_);
lean_ctor_set(v___x_1738_, 8, v_initHeartbeats_1729_);
lean_ctor_set(v___x_1738_, 9, v_maxHeartbeats_1730_);
lean_ctor_set(v___x_1738_, 10, v_quotContext_1731_);
lean_ctor_set(v___x_1738_, 11, v_currMacroScope_1732_);
lean_ctor_set(v___x_1738_, 12, v_cancelTk_x3f_1734_);
lean_ctor_set(v___x_1738_, 13, v_inheritedTraceOptions_1736_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*14, v_diag_1733_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*14 + 1, v_suppressElabErrors_1735_);
v___x_1739_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_1715_, v___y_1716_, v___y_1717_, v___x_1738_, v___y_1719_);
lean_dec_ref(v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1740_, lean_object* v_msg_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1740_, v_msg_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v_ref_1740_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1748_, lean_object* v_msg_1749_, lean_object* v_declHint_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v_a_1757_; lean_object* v___x_1758_; 
v___x_1756_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1749_, v_declHint_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1748_, v_a_1757_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1759_, lean_object* v_msg_1760_, lean_object* v_declHint_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1759_, v_msg_1760_, v_declHint_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v_ref_1759_);
return v_res_1767_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1771_, lean_object* v_constName_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1778_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1779_ = 0;
lean_inc(v_constName_1772_);
v___x_1780_ = l_Lean_MessageData_ofConstName(v_constName_1772_, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1778_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1771_, v___x_1783_, v_constName_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1785_, lean_object* v_constName_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_1785_, v_constName_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v_ref_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(lean_object* v_constName_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_ref_1799_; lean_object* v___x_1800_; 
v_ref_1799_ = lean_ctor_get(v___y_1796_, 5);
v___x_1800_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_1799_, v_constName_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(lean_object* v_constName_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; lean_object* v_env_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1814_ = lean_st_ref_get(v___y_1812_);
v_env_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc_ref(v_env_1815_);
lean_dec(v___x_1814_);
v___x_1816_ = 0;
lean_inc(v_constName_1808_);
v___x_1817_ = l_Lean_Environment_findConstVal_x3f(v_env_1815_, v_constName_1808_, v___x_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
return v___x_1818_;
}
else
{
lean_object* v_val_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_constName_1808_);
v_val_1819_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1817_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_val_1819_);
lean_dec(v___x_1817_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 0);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_val_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0___boxed(lean_object* v_constName_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(v_constName_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1833_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0(void){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1834_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_unsigned_to_nat(32u);
v___x_1841_ = lean_mk_empty_array_with_capacity(v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4(void){
_start:
{
size_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1843_ = ((size_t)5ULL);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_unsigned_to_nat(32u);
v___x_1846_ = lean_mk_empty_array_with_capacity(v___x_1845_);
v___x_1847_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3);
v___x_1848_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1846_);
lean_ctor_set(v___x_1848_, 2, v___x_1844_);
lean_ctor_set(v___x_1848_, 3, v___x_1844_);
lean_ctor_set_usize(v___x_1848_, 4, v___x_1843_);
return v___x_1848_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4);
v___x_1850_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1);
v___x_1851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
lean_ctor_set(v___x_1851_, 2, v___x_1850_);
lean_ctor_set(v___x_1851_, 3, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5);
v___x_1853_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = l_Lean_Level_ofNat(v___x_1860_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1862_);
return v___x_1864_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11);
v___x_1866_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9));
v___x_1867_ = l_Lean_mkConst(v___x_1866_, v___x_1865_);
return v___x_1867_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13));
v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
return v___x_1870_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15));
v___x_1873_ = l_Lean_stringToMessageData(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(lean_object* v_ctx_1874_, lean_object* v_simprocs_1875_, lean_object* v_eqThmName_1876_, lean_object* v_destThmName_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1883_; 
lean_inc(v_eqThmName_1876_);
v___x_1883_ = l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(v_eqThmName_1876_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_levelParams_1885_; lean_object* v_type_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1961_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v_levelParams_1885_ = lean_ctor_get(v_a_1884_, 1);
v_type_1886_ = lean_ctor_get(v_a_1884_, 2);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v_a_1884_, 0);
lean_dec(v_unused_1962_);
v___x_1888_ = v_a_1884_;
v_isShared_1889_ = v_isSharedCheck_1961_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_type_1886_);
lean_inc(v_levelParams_1885_);
lean_dec(v_a_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1961_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_mk_empty_array_with_capacity(v___x_1890_);
v___x_1892_ = lean_array_push(v___x_1891_, v_simprocs_1875_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6);
lean_inc_ref(v_type_1886_);
v___x_1895_ = l_Lean_Meta_simp(v_type_1886_, v_ctx_1874_, v___x_1892_, v___x_1893_, v___x_1894_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v_fst_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1951_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v_fst_1897_ = lean_ctor_get(v_a_1896_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1896_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_a_1896_, 1);
lean_dec(v_unused_1952_);
v___x_1899_ = v_a_1896_;
v_isShared_1900_ = v_isSharedCheck_1951_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_fst_1897_);
lean_dec(v_a_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1951_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; uint8_t v___x_1941_; 
v___x_1938_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_1939_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg(v___x_1938_, v_a_1880_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v___x_1941_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
if (v___x_1941_ == 0)
{
v___y_1902_ = v_a_1878_;
v___y_1903_ = v_a_1879_;
v___y_1904_ = v_a_1880_;
v___y_1905_ = v_a_1881_;
goto v___jp_1901_;
}
else
{
lean_object* v_expr_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_expr_1942_ = lean_ctor_get(v_fst_1897_, 0);
v___x_1943_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14);
lean_inc(v_destThmName_1877_);
v___x_1944_ = l_Lean_MessageData_ofName(v_destThmName_1877_);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
lean_inc_ref(v_expr_1942_);
v___x_1948_ = l_Lean_indentExpr(v_expr_1942_);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(v___x_1938_, v___x_1949_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_dec_ref(v___x_1950_);
v___y_1902_ = v_a_1878_;
v___y_1903_ = v_a_1879_;
v___y_1904_ = v_a_1880_;
v___y_1905_ = v_a_1881_;
goto v___jp_1901_;
}
else
{
lean_del_object(v___x_1899_);
lean_dec(v_fst_1897_);
lean_del_object(v___x_1888_);
lean_dec_ref(v_type_1886_);
lean_dec(v_levelParams_1885_);
lean_dec(v_destThmName_1877_);
lean_dec(v_eqThmName_1876_);
return v___x_1950_;
}
}
v___jp_1901_:
{
lean_object* v___x_1906_; 
lean_inc(v_fst_1897_);
v___x_1906_ = l_Lean_Meta_Simp_Result_getProof(v_fst_1897_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v_expr_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1906_);
v_expr_1908_ = lean_ctor_get(v_fst_1897_, 0);
lean_inc_ref(v_expr_1908_);
lean_dec(v_fst_1897_);
v___x_1909_ = lean_box(0);
lean_inc(v_levelParams_1885_);
v___x_1910_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_1885_, v___x_1909_);
v___x_1911_ = l_Lean_mkConst(v_eqThmName_1876_, v___x_1910_);
v___x_1912_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12);
v___x_1913_ = lean_unsigned_to_nat(4u);
v___x_1914_ = lean_mk_empty_array_with_capacity(v___x_1913_);
v___x_1915_ = lean_array_push(v___x_1914_, v_type_1886_);
lean_inc_ref(v_expr_1908_);
v___x_1916_ = lean_array_push(v___x_1915_, v_expr_1908_);
v___x_1917_ = lean_array_push(v___x_1916_, v_a_1907_);
v___x_1918_ = lean_array_push(v___x_1917_, v___x_1911_);
v___x_1919_ = l_Lean_mkAppN(v___x_1912_, v___x_1918_);
lean_dec_ref(v___x_1918_);
lean_inc(v_destThmName_1877_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 2, v_expr_1908_);
lean_ctor_set(v___x_1888_, 0, v_destThmName_1877_);
v___x_1921_ = v___x_1888_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_destThmName_1877_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_levelParams_1885_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_expr_1908_);
v___x_1921_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 1);
lean_ctor_set(v___x_1899_, 1, v___x_1909_);
lean_ctor_set(v___x_1899_, 0, v_destThmName_1877_);
v___x_1923_ = v___x_1899_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_destThmName_1877_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1909_);
v___x_1923_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1921_);
lean_ctor_set(v___x_1924_, 1, v___x_1919_);
lean_ctor_set(v___x_1924_, 2, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
v___x_1926_ = 0;
v___x_1927_ = l_Lean_addDecl(v___x_1925_, v___x_1926_, v___y_1904_, v___y_1905_);
return v___x_1927_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_del_object(v___x_1899_);
lean_dec(v_fst_1897_);
lean_del_object(v___x_1888_);
lean_dec_ref(v_type_1886_);
lean_dec(v_levelParams_1885_);
lean_dec(v_destThmName_1877_);
lean_dec(v_eqThmName_1876_);
v_a_1930_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1906_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1906_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_del_object(v___x_1888_);
lean_dec_ref(v_type_1886_);
lean_dec(v_levelParams_1885_);
lean_dec(v_destThmName_1877_);
lean_dec(v_eqThmName_1876_);
v_a_1953_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1895_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1895_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_destThmName_1877_);
lean_dec(v_eqThmName_1876_);
lean_dec_ref(v_simprocs_1875_);
lean_dec_ref(v_ctx_1874_);
v_a_1963_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1883_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1883_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___boxed(lean_object* v_ctx_1971_, lean_object* v_simprocs_1972_, lean_object* v_eqThmName_1973_, lean_object* v_destThmName_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(v_ctx_1971_, v_simprocs_1972_, v_eqThmName_1973_, v_destThmName_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(lean_object* v_00_u03b1_1981_, lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1989_, lean_object* v_constName_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(v_00_u03b1_1989_, v_constName_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1997_, lean_object* v_ref_1998_, lean_object* v_constName_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_1998_, v_constName_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_ref_2007_, lean_object* v_constName_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(v_00_u03b1_2006_, v_ref_2007_, v_constName_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v_ref_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2015_, lean_object* v_ref_2016_, lean_object* v_msg_2017_, lean_object* v_declHint_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2016_, v_msg_2017_, v_declHint_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2025_, lean_object* v_ref_2026_, lean_object* v_msg_2027_, lean_object* v_declHint_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2025_, v_ref_2026_, v_msg_2027_, v_declHint_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v_ref_2026_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2035_, lean_object* v_declHint_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2035_, v_declHint_2036_, v___y_2040_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2043_, lean_object* v_declHint_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2043_, v_declHint_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2051_, lean_object* v_ref_2052_, lean_object* v_msg_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2052_, v_msg_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2060_, lean_object* v_ref_2061_, lean_object* v_msg_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2060_, v_ref_2061_, v_msg_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v_ref_2061_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(lean_object* v___x_2069_, lean_object* v___x_2070_, lean_object* v_instName_2071_, uint8_t v___x_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_as_2075_, size_t v_sz_2076_, size_t v_i_2077_, lean_object* v_b_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_lt(v_i_2077_, v_sz_2076_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_instName_2071_);
lean_dec_ref(v___x_2069_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_b_2078_);
return v___x_2085_;
}
else
{
lean_object* v_start_2086_; lean_object* v_stop_2087_; lean_object* v_step_2088_; uint8_t v___x_2089_; 
v_start_2086_ = lean_ctor_get(v_b_2078_, 0);
v_stop_2087_ = lean_ctor_get(v_b_2078_, 1);
v_step_2088_ = lean_ctor_get(v_b_2078_, 2);
v___x_2089_ = lean_nat_dec_lt(v_start_2086_, v_stop_2087_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec_ref(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_instName_2071_);
lean_dec_ref(v___x_2069_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_b_2078_);
return v___x_2090_;
}
else
{
lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2118_; 
lean_inc(v_step_2088_);
lean_inc(v_stop_2087_);
lean_inc(v_start_2086_);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_b_2078_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; lean_object* v_unused_2120_; lean_object* v_unused_2121_; 
v_unused_2119_ = lean_ctor_get(v_b_2078_, 2);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_b_2078_, 1);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_b_2078_, 0);
lean_dec(v_unused_2121_);
v___x_2092_ = v_b_2078_;
v_isShared_2093_ = v_isSharedCheck_2118_;
goto v_resetjp_2091_;
}
else
{
lean_dec(v_b_2078_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2118_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2094_ = lean_unsigned_to_nat(1u);
v_a_2095_ = lean_array_uget_borrowed(v_as_2075_, v_i_2077_);
v___x_2096_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1));
lean_inc_ref(v___x_2069_);
v___x_2097_ = lean_string_append(v___x_2069_, v___x_2096_);
v___x_2098_ = lean_nat_add(v_start_2086_, v___x_2094_);
v___x_2099_ = l_Nat_reprFast(v___x_2098_);
v___x_2100_ = lean_string_append(v___x_2097_, v___x_2099_);
lean_dec_ref(v___x_2099_);
lean_inc(v_instName_2071_);
v___x_2101_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v___x_2070_, v_instName_2071_, v___x_2072_, v___x_2100_);
lean_inc(v_a_2095_);
lean_inc_ref(v_a_2074_);
lean_inc_ref(v_a_2073_);
v___x_2102_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(v_a_2073_, v_a_2074_, v_a_2095_, v___x_2101_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
lean_dec_ref(v___x_2102_);
v___x_2103_ = lean_nat_add(v_start_2086_, v_step_2088_);
lean_dec(v_start_2086_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2103_);
v___x_2105_ = v___x_2092_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_stop_2087_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_step_2088_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
size_t v___x_2106_; size_t v___x_2107_; 
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_i_2077_, v___x_2106_);
v_i_2077_ = v___x_2107_;
v_b_2078_ = v___x_2105_;
goto _start;
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_del_object(v___x_2092_);
lean_dec(v_step_2088_);
lean_dec(v_stop_2087_);
lean_dec(v_start_2086_);
lean_dec_ref(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_instName_2071_);
lean_dec_ref(v___x_2069_);
v_a_2110_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2102_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2102_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1___boxed(lean_object* v___x_2122_, lean_object* v___x_2123_, lean_object* v_instName_2124_, lean_object* v___x_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_as_2128_, lean_object* v_sz_2129_, lean_object* v_i_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
uint8_t v___x_9106__boxed_2137_; size_t v_sz_boxed_2138_; size_t v_i_boxed_2139_; lean_object* v_res_2140_; 
v___x_9106__boxed_2137_ = lean_unbox(v___x_2125_);
v_sz_boxed_2138_ = lean_unbox_usize(v_sz_2129_);
lean_dec(v_sz_2129_);
v_i_boxed_2139_ = lean_unbox_usize(v_i_2130_);
lean_dec(v_i_2130_);
v_res_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_2122_, v___x_2123_, v_instName_2124_, v___x_9106__boxed_2137_, v_a_2126_, v_a_2127_, v_as_2128_, v_sz_boxed_2138_, v_i_boxed_2139_, v_b_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec_ref(v_as_2128_);
lean_dec_ref(v___x_2123_);
return v_res_2140_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0));
v___x_2143_ = l_Lean_stringToMessageData(v___x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(lean_object* v_a_2144_, lean_object* v___x_2145_, lean_object* v_instName_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_as_2149_, size_t v_sz_2150_, size_t v_i_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_a_2159_; uint8_t v___x_2163_; 
v___x_2163_ = lean_usize_dec_lt(v_i_2151_, v_sz_2150_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_instName_2146_);
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v_b_2152_);
return v___x_2164_;
}
else
{
lean_object* v_a_2165_; lean_object* v_fst_2166_; lean_object* v_snd_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2222_; 
v_a_2165_ = lean_array_uget(v_as_2149_, v_i_2151_);
v_fst_2166_ = lean_ctor_get(v_a_2165_, 0);
v_snd_2167_ = lean_ctor_get(v_a_2165_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_a_2165_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2169_ = v_a_2165_;
v_isShared_2170_ = v_isSharedCheck_2222_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_snd_2167_);
lean_inc(v_fst_2166_);
lean_dec(v_a_2165_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2222_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; 
lean_inc(v_snd_2167_);
v___x_2171_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_snd_2167_, v___x_2163_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = lean_box(0);
if (lean_obj_tag(v_a_2172_) == 1)
{
lean_object* v_val_2174_; uint8_t v_privateSpecs_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_del_object(v___x_2169_);
v_val_2174_ = lean_ctor_get(v_a_2172_, 0);
lean_inc(v_val_2174_);
lean_dec_ref(v_a_2172_);
v_privateSpecs_2175_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3);
v___x_2176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2166_, v___x_2163_);
v___x_2177_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
lean_inc_ref(v___x_2176_);
v___x_2178_ = lean_string_append(v___x_2176_, v___x_2177_);
lean_inc(v_instName_2146_);
v___x_2179_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v___x_2145_, v_instName_2146_, v_privateSpecs_2175_, v___x_2178_);
lean_inc_ref(v_a_2148_);
lean_inc_ref(v_a_2147_);
v___x_2180_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(v_a_2147_, v_a_2148_, v_val_2174_, v___x_2179_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v___x_2181_; 
lean_dec_ref(v___x_2180_);
v___x_2181_ = l_Lean_Meta_getEqnsFor_x3f(v_snd_2167_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
if (lean_obj_tag(v_a_2182_) == 1)
{
lean_object* v_val_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; size_t v_sz_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
v_val_2183_ = lean_ctor_get(v_a_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref(v_a_2182_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_array_get_size(v_val_2183_);
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2184_);
lean_ctor_set(v___x_2187_, 1, v___x_2185_);
lean_ctor_set(v___x_2187_, 2, v___x_2186_);
v_sz_2188_ = lean_array_size(v_val_2183_);
v___x_2189_ = ((size_t)0ULL);
lean_inc_ref(v_a_2148_);
lean_inc_ref(v_a_2147_);
lean_inc(v_instName_2146_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_2176_, v___x_2145_, v_instName_2146_, v_privateSpecs_2175_, v_a_2147_, v_a_2148_, v_val_2183_, v_sz_2188_, v___x_2189_, v___x_2187_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v_val_2183_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec_ref(v___x_2190_);
v_a_2159_ = v___x_2173_;
goto v___jp_2158_;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_instName_2146_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_dec(v_a_2182_);
lean_dec_ref(v___x_2176_);
v_a_2159_ = v___x_2173_;
goto v___jp_2158_;
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v___x_2176_);
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_instName_2146_);
v_a_2199_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2181_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2181_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_dec_ref(v___x_2176_);
lean_dec(v_snd_2167_);
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_instName_2146_);
return v___x_2180_;
}
}
else
{
uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
lean_dec(v_a_2172_);
lean_dec(v_fst_2166_);
v___x_2207_ = 0;
v___x_2208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1);
v___x_2209_ = l_Lean_MessageData_ofConstName(v_snd_2167_, v___x_2207_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set_tag(v___x_2169_, 7);
lean_ctor_set(v___x_2169_, 1, v___x_2209_);
lean_ctor_set(v___x_2169_, 0, v___x_2208_);
v___x_2211_ = v___x_2169_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_2211_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_dec_ref(v___x_2212_);
v_a_2159_ = v___x_2173_;
goto v___jp_2158_;
}
else
{
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_instName_2146_);
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_del_object(v___x_2169_);
lean_dec(v_snd_2167_);
lean_dec(v_fst_2166_);
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_instName_2146_);
v_a_2214_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2171_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2171_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
v___jp_2158_:
{
size_t v___x_2160_; size_t v___x_2161_; 
v___x_2160_ = ((size_t)1ULL);
v___x_2161_ = lean_usize_add(v_i_2151_, v___x_2160_);
v_i_2151_ = v___x_2161_;
v_b_2152_ = v_a_2159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___boxed(lean_object* v_a_2223_, lean_object* v___x_2224_, lean_object* v_instName_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_as_2228_, lean_object* v_sz_2229_, lean_object* v_i_2230_, lean_object* v_b_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
size_t v_sz_boxed_2237_; size_t v_i_boxed_2238_; lean_object* v_res_2239_; 
v_sz_boxed_2237_ = lean_unbox_usize(v_sz_2229_);
lean_dec(v_sz_2229_);
v_i_boxed_2238_ = lean_unbox_usize(v_i_2230_);
lean_dec(v_i_2230_);
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_2223_, v___x_2224_, v_instName_2225_, v_a_2226_, v_a_2227_, v_as_2228_, v_sz_boxed_2237_, v_i_boxed_2238_, v_b_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v_as_2228_);
lean_dec_ref(v___x_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2239_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(lean_object* v_as_2246_, size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_usize_dec_lt(v_i_2248_, v_sz_2247_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_b_2249_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_2258_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___redArg(v___x_2257_, v___y_2252_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v_a_2260_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; uint8_t v___x_2287_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2258_);
v_a_2260_ = lean_array_uget_borrowed(v_as_2246_, v_i_2248_);
v___x_2287_ = lean_unbox(v_a_2259_);
lean_dec(v_a_2259_);
if (v___x_2287_ == 0)
{
v___y_2262_ = v___y_2250_;
v___y_2263_ = v___y_2251_;
v___y_2264_ = v___y_2252_;
v___y_2265_ = v___y_2253_;
goto v___jp_2261_;
}
else
{
lean_object* v_name_2288_; lean_object* v_type_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_name_2288_ = lean_ctor_get(v_a_2260_, 0);
v_type_2289_ = lean_ctor_get(v_a_2260_, 2);
v___x_2290_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1);
lean_inc(v_name_2288_);
v___x_2291_ = l_Lean_MessageData_ofName(v_name_2288_);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
lean_inc_ref(v_type_2289_);
v___x_2295_ = l_Lean_MessageData_ofExpr(v_type_2289_);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(v___x_2257_, v___x_2296_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_dec_ref(v___x_2297_);
v___y_2262_ = v___y_2250_;
v___y_2263_ = v___y_2251_;
v___y_2264_ = v___y_2252_;
v___y_2265_ = v___y_2253_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_b_2249_);
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
v___jp_2261_:
{
lean_object* v_name_2266_; lean_object* v_levelParams_2267_; lean_object* v_type_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_name_2266_ = lean_ctor_get(v_a_2260_, 0);
v_levelParams_2267_ = lean_ctor_get(v_a_2260_, 1);
v_type_2268_ = lean_ctor_get(v_a_2260_, 2);
lean_inc(v_name_2266_);
v___x_2269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_name_2266_);
lean_inc(v_levelParams_2267_);
v___x_2270_ = lean_array_mk(v_levelParams_2267_);
v___x_2271_ = lean_unsigned_to_nat(1000u);
v___x_2272_ = l_Lean_Meta_simpGlobalConfig;
lean_inc_ref(v_type_2268_);
v___x_2273_ = l_Lean_Meta_mkDSimpTheorem(v___x_2269_, v___x_2270_, v_type_2268_, v___x_2255_, v___x_2271_, v___x_2272_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = l_Lean_Meta_SimpTheorems_addSimpTheorem(v_b_2249_, v_a_2274_);
v___x_2276_ = ((size_t)1ULL);
v___x_2277_ = lean_usize_add(v_i_2248_, v___x_2276_);
v_i_2248_ = v___x_2277_;
v_b_2249_ = v___x_2275_;
goto _start;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v_b_2249_);
v_a_2279_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2273_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2273_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_b_2249_);
v_a_2306_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2258_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2258_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___boxed(lean_object* v_as_2314_, lean_object* v_sz_2315_, lean_object* v_i_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
size_t v_sz_boxed_2323_; size_t v_i_boxed_2324_; lean_object* v_res_2325_; 
v_sz_boxed_2323_ = lean_unbox_usize(v_sz_2315_);
lean_dec(v_sz_2315_);
v_i_boxed_2324_ = lean_unbox_usize(v_i_2316_);
lean_dec(v_i_2316_);
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_as_2314_, v_sz_boxed_2323_, v_i_boxed_2324_, v_b_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_as_2314_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(lean_object* v___x_2333_, lean_object* v_thms_2334_, lean_object* v_fieldImpls_2335_, lean_object* v_a_2336_, lean_object* v_instName_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2333_, v___y_2341_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref(v___x_2343_);
v_sz_2345_ = lean_array_size(v_thms_2334_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_thms_2334_, v_sz_2345_, v___x_2346_, v_a_2344_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2347_);
v___x_2349_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2341_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0));
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_mk_empty_array_with_capacity(v___x_2352_);
v___x_2354_ = lean_array_push(v___x_2353_, v_a_2348_);
v___x_2355_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2351_, v___x_2354_, v_a_2350_, v___y_2338_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = l_Lean_Meta_Simp_getSimprocs___redArg(v___y_2341_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2359_; lean_object* v_env_2360_; lean_object* v___x_2361_; size_t v_sz_2362_; lean_object* v___x_2363_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v___x_2359_ = lean_st_ref_get(v___y_2341_);
v_env_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc_ref(v_env_2360_);
lean_dec(v___x_2359_);
v___x_2361_ = lean_box(0);
v_sz_2362_ = lean_array_size(v_fieldImpls_2335_);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_2336_, v_env_2360_, v_instName_2337_, v_a_2356_, v_a_2358_, v_fieldImpls_2335_, v_sz_2362_, v___x_2346_, v___x_2361_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec_ref(v_env_2360_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v___x_2363_, 0);
lean_dec(v_unused_2371_);
v___x_2365_ = v___x_2363_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_dec(v___x_2363_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2361_);
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2361_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
return v___x_2363_;
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2356_);
lean_dec(v_instName_2337_);
v_a_2372_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2357_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2357_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v_instName_2337_);
v_a_2380_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2355_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2355_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_a_2348_);
lean_dec(v_instName_2337_);
v_a_2388_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2349_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2349_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_instName_2337_);
v_a_2396_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2347_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2347_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_instName_2337_);
v_a_2404_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2343_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2343_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed(lean_object* v___x_2412_, lean_object* v_thms_2413_, lean_object* v_fieldImpls_2414_, lean_object* v_a_2415_, lean_object* v_instName_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(v___x_2412_, v_thms_2413_, v_fieldImpls_2414_, v_a_2415_, v_instName_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec_ref(v_a_2415_);
lean_dec_ref(v_fieldImpls_2414_);
lean_dec_ref(v_thms_2413_);
lean_dec_ref(v___x_2412_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(lean_object* v___y_2423_, uint8_t v_isExporting_2424_, lean_object* v___x_2425_, lean_object* v___y_2426_, lean_object* v___x_2427_, lean_object* v_a_x3f_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v_env_2431_; lean_object* v_nextMacroScope_2432_; lean_object* v_ngen_2433_; lean_object* v_auxDeclNGen_2434_; lean_object* v_traceState_2435_; lean_object* v_messages_2436_; lean_object* v_infoState_2437_; lean_object* v_snapshotTasks_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2463_; 
v___x_2430_ = lean_st_ref_take(v___y_2423_);
v_env_2431_ = lean_ctor_get(v___x_2430_, 0);
v_nextMacroScope_2432_ = lean_ctor_get(v___x_2430_, 1);
v_ngen_2433_ = lean_ctor_get(v___x_2430_, 2);
v_auxDeclNGen_2434_ = lean_ctor_get(v___x_2430_, 3);
v_traceState_2435_ = lean_ctor_get(v___x_2430_, 4);
v_messages_2436_ = lean_ctor_get(v___x_2430_, 6);
v_infoState_2437_ = lean_ctor_get(v___x_2430_, 7);
v_snapshotTasks_2438_ = lean_ctor_get(v___x_2430_, 8);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v___x_2430_, 5);
lean_dec(v_unused_2464_);
v___x_2440_ = v___x_2430_;
v_isShared_2441_ = v_isSharedCheck_2463_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_snapshotTasks_2438_);
lean_inc(v_infoState_2437_);
lean_inc(v_messages_2436_);
lean_inc(v_traceState_2435_);
lean_inc(v_auxDeclNGen_2434_);
lean_inc(v_ngen_2433_);
lean_inc(v_nextMacroScope_2432_);
lean_inc(v_env_2431_);
lean_dec(v___x_2430_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2463_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2442_ = l_Lean_Environment_setExporting(v_env_2431_, v_isExporting_2424_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 5, v___x_2425_);
lean_ctor_set(v___x_2440_, 0, v___x_2442_);
v___x_2444_ = v___x_2440_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_nextMacroScope_2432_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_ngen_2433_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_auxDeclNGen_2434_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_traceState_2435_);
lean_ctor_set(v_reuseFailAlloc_2462_, 5, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2462_, 6, v_messages_2436_);
lean_ctor_set(v_reuseFailAlloc_2462_, 7, v_infoState_2437_);
lean_ctor_set(v_reuseFailAlloc_2462_, 8, v_snapshotTasks_2438_);
v___x_2444_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_mctx_2447_; lean_object* v_zetaDeltaFVarIds_2448_; lean_object* v_postponed_2449_; lean_object* v_diag_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2460_; 
v___x_2445_ = lean_st_ref_set(v___y_2423_, v___x_2444_);
v___x_2446_ = lean_st_ref_take(v___y_2426_);
v_mctx_2447_ = lean_ctor_get(v___x_2446_, 0);
v_zetaDeltaFVarIds_2448_ = lean_ctor_get(v___x_2446_, 2);
v_postponed_2449_ = lean_ctor_get(v___x_2446_, 3);
v_diag_2450_ = lean_ctor_get(v___x_2446_, 4);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v___x_2446_, 1);
lean_dec(v_unused_2461_);
v___x_2452_ = v___x_2446_;
v_isShared_2453_ = v_isSharedCheck_2460_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_diag_2450_);
lean_inc(v_postponed_2449_);
lean_inc(v_zetaDeltaFVarIds_2448_);
lean_inc(v_mctx_2447_);
lean_dec(v___x_2446_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2460_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2427_);
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_mctx_2447_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_zetaDeltaFVarIds_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_postponed_2449_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_diag_2450_);
v___x_2455_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = lean_st_ref_set(v___y_2426_, v___x_2455_);
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v___y_2465_, lean_object* v_isExporting_2466_, lean_object* v___x_2467_, lean_object* v___y_2468_, lean_object* v___x_2469_, lean_object* v_a_x3f_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v_isExporting_boxed_2472_; lean_object* v_res_2473_; 
v_isExporting_boxed_2472_ = lean_unbox(v_isExporting_2466_);
v_res_2473_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_2465_, v_isExporting_boxed_2472_, v___x_2467_, v___y_2468_, v___x_2469_, v_a_x3f_2470_);
lean_dec(v_a_x3f_2470_);
lean_dec(v___y_2468_);
lean_dec(v___y_2465_);
return v_res_2473_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2474_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
v___x_2480_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
lean_ctor_set(v___x_2480_, 2, v___x_2479_);
lean_ctor_set(v___x_2480_, 3, v___x_2479_);
lean_ctor_set(v___x_2480_, 4, v___x_2479_);
lean_ctor_set(v___x_2480_, 5, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(lean_object* v_x_2481_, uint8_t v_isExporting_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v_env_2489_; uint8_t v_isExporting_2490_; lean_object* v___x_2491_; lean_object* v_env_2492_; lean_object* v_nextMacroScope_2493_; lean_object* v_ngen_2494_; lean_object* v_auxDeclNGen_2495_; lean_object* v_traceState_2496_; lean_object* v_messages_2497_; lean_object* v_infoState_2498_; lean_object* v_snapshotTasks_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2553_; 
v___x_2488_ = lean_st_ref_get(v___y_2486_);
v_env_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc_ref(v_env_2489_);
lean_dec(v___x_2488_);
v_isExporting_2490_ = lean_ctor_get_uint8(v_env_2489_, sizeof(void*)*8);
lean_dec_ref(v_env_2489_);
v___x_2491_ = lean_st_ref_take(v___y_2486_);
v_env_2492_ = lean_ctor_get(v___x_2491_, 0);
v_nextMacroScope_2493_ = lean_ctor_get(v___x_2491_, 1);
v_ngen_2494_ = lean_ctor_get(v___x_2491_, 2);
v_auxDeclNGen_2495_ = lean_ctor_get(v___x_2491_, 3);
v_traceState_2496_ = lean_ctor_get(v___x_2491_, 4);
v_messages_2497_ = lean_ctor_get(v___x_2491_, 6);
v_infoState_2498_ = lean_ctor_get(v___x_2491_, 7);
v_snapshotTasks_2499_ = lean_ctor_get(v___x_2491_, 8);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___x_2491_, 5);
lean_dec(v_unused_2554_);
v___x_2501_ = v___x_2491_;
v_isShared_2502_ = v_isSharedCheck_2553_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_snapshotTasks_2499_);
lean_inc(v_infoState_2498_);
lean_inc(v_messages_2497_);
lean_inc(v_traceState_2496_);
lean_inc(v_auxDeclNGen_2495_);
lean_inc(v_ngen_2494_);
lean_inc(v_nextMacroScope_2493_);
lean_inc(v_env_2492_);
lean_dec(v___x_2491_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2553_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2503_ = l_Lean_Environment_setExporting(v_env_2492_, v_isExporting_2482_);
v___x_2504_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 5, v___x_2504_);
lean_ctor_set(v___x_2501_, 0, v___x_2503_);
v___x_2506_ = v___x_2501_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_nextMacroScope_2493_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_ngen_2494_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_auxDeclNGen_2495_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_traceState_2496_);
lean_ctor_set(v_reuseFailAlloc_2552_, 5, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2552_, 6, v_messages_2497_);
lean_ctor_set(v_reuseFailAlloc_2552_, 7, v_infoState_2498_);
lean_ctor_set(v_reuseFailAlloc_2552_, 8, v_snapshotTasks_2499_);
v___x_2506_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_mctx_2509_; lean_object* v_zetaDeltaFVarIds_2510_; lean_object* v_postponed_2511_; lean_object* v_diag_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2550_; 
v___x_2507_ = lean_st_ref_set(v___y_2486_, v___x_2506_);
v___x_2508_ = lean_st_ref_take(v___y_2484_);
v_mctx_2509_ = lean_ctor_get(v___x_2508_, 0);
v_zetaDeltaFVarIds_2510_ = lean_ctor_get(v___x_2508_, 2);
v_postponed_2511_ = lean_ctor_get(v___x_2508_, 3);
v_diag_2512_ = lean_ctor_get(v___x_2508_, 4);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v___x_2508_, 1);
lean_dec(v_unused_2551_);
v___x_2514_ = v___x_2508_;
v_isShared_2515_ = v_isSharedCheck_2550_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_diag_2512_);
lean_inc(v_postponed_2511_);
lean_inc(v_zetaDeltaFVarIds_2510_);
lean_inc(v_mctx_2509_);
lean_dec(v___x_2508_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2550_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 1, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_mctx_2509_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_zetaDeltaFVarIds_2510_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_postponed_2511_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_diag_2512_);
v___x_2518_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; lean_object* v_r_2520_; 
v___x_2519_ = lean_st_ref_set(v___y_2484_, v___x_2518_);
lean_inc(v___y_2486_);
lean_inc_ref(v___y_2485_);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
v_r_2520_ = lean_apply_5(v_x_2481_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, lean_box(0));
if (lean_obj_tag(v_r_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2537_; 
v_a_2521_ = lean_ctor_get(v_r_2520_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_r_2520_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2523_ = v_r_2520_;
v_isShared_2524_ = v_isSharedCheck_2537_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v_r_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2537_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
lean_inc(v_a_2521_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set_tag(v___x_2523_, 1);
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v___x_2527_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_2486_, v_isExporting_2490_, v___x_2504_, v___y_2484_, v___x_2516_, v___x_2526_);
lean_dec_ref(v___x_2526_);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2527_, 0);
lean_dec(v_unused_2535_);
v___x_2529_ = v___x_2527_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_dec(v___x_2527_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v_a_2521_);
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2521_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2538_ = lean_ctor_get(v_r_2520_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v_r_2520_);
v___x_2539_ = lean_box(0);
v___x_2540_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_2486_, v_isExporting_2490_, v___x_2504_, v___y_2484_, v___x_2516_, v___x_2539_);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v___x_2540_, 0);
lean_dec(v_unused_2548_);
v___x_2542_ = v___x_2540_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_dec(v___x_2540_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 1);
lean_ctor_set(v___x_2542_, 0, v_a_2538_);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2538_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___boxed(lean_object* v_x_2555_, lean_object* v_isExporting_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
uint8_t v_isExporting_boxed_2562_; lean_object* v_res_2563_; 
v_isExporting_boxed_2562_ = lean_unbox(v_isExporting_2556_);
v_res_2563_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_2555_, v_isExporting_boxed_2562_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(lean_object* v_x_2564_, uint8_t v_when_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
if (v_when_2565_ == 0)
{
lean_object* v___x_2571_; 
lean_inc(v___y_2569_);
lean_inc_ref(v___y_2568_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
v___x_2571_ = lean_apply_5(v_x_2564_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, lean_box(0));
return v___x_2571_;
}
else
{
uint8_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = 0;
v___x_2573_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_2564_, v___x_2572_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg___boxed(lean_object* v_x_2574_, lean_object* v_when_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
uint8_t v_when_boxed_2581_; lean_object* v_res_2582_; 
v_when_boxed_2581_ = lean_unbox(v_when_2575_);
v_res_2582_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_2574_, v_when_boxed_2581_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(lean_object* v_instName_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v___x_2589_; 
lean_inc(v_instName_2583_);
v___x_2589_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v_privateSpecs_2591_; lean_object* v_fieldImpls_2592_; lean_object* v_thms_2593_; lean_object* v___x_2594_; lean_object* v___f_2595_; lean_object* v___x_2596_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___x_2589_);
v_privateSpecs_2591_ = lean_ctor_get_uint8(v_a_2590_, sizeof(void*)*3);
v_fieldImpls_2592_ = lean_ctor_get(v_a_2590_, 1);
lean_inc_ref(v_fieldImpls_2592_);
v_thms_2593_ = lean_ctor_get(v_a_2590_, 2);
lean_inc_ref(v_thms_2593_);
v___x_2594_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension;
v___f_2595_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2595_, 0, v___x_2594_);
lean_closure_set(v___f_2595_, 1, v_thms_2593_);
lean_closure_set(v___f_2595_, 2, v_fieldImpls_2592_);
lean_closure_set(v___f_2595_, 3, v_a_2590_);
lean_closure_set(v___f_2595_, 4, v_instName_2583_);
v___x_2596_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v___f_2595_, v_privateSpecs_2591_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
return v___x_2596_;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_instName_2583_);
v_a_2597_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2589_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2589_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed(lean_object* v_instName_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(v_instName_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(lean_object* v_00_u03b1_2612_, lean_object* v_x_2613_, uint8_t v_isExporting_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_2613_, v_isExporting_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_x_2622_, lean_object* v_isExporting_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
uint8_t v_isExporting_boxed_2629_; lean_object* v_res_2630_; 
v_isExporting_boxed_2629_ = lean_unbox(v_isExporting_2623_);
v_res_2630_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(v_00_u03b1_2621_, v_x_2622_, v_isExporting_boxed_2629_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(lean_object* v_00_u03b1_2631_, lean_object* v_x_2632_, uint8_t v_when_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_2632_, v_when_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_x_2641_, lean_object* v_when_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
uint8_t v_when_boxed_2648_; lean_object* v_res_2649_; 
v_when_boxed_2648_ = lean_unbox(v_when_2642_);
v_res_2649_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(v_00_u03b1_2640_, v_x_2641_, v_when_boxed_2648_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(lean_object* v_instName_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0));
lean_inc(v_instName_2652_);
v___x_2659_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; lean_object* v_env_2662_; uint8_t v_privateSpecs_2663_; lean_object* v_fieldImpls_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v_fst_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
v___x_2661_ = lean_st_ref_get(v_a_2656_);
v_env_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc_ref(v_env_2662_);
lean_dec(v___x_2661_);
v_privateSpecs_2663_ = lean_ctor_get_uint8(v_a_2660_, sizeof(void*)*3);
v_fieldImpls_2664_ = lean_ctor_get(v_a_2660_, 1);
lean_inc_ref(v_fieldImpls_2664_);
lean_dec(v_a_2660_);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get(v___x_2658_, v_fieldImpls_2664_, v___x_2665_);
lean_dec_ref(v_fieldImpls_2664_);
v_fst_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_fst_2667_);
lean_dec(v___x_2666_);
v___x_2668_ = 1;
v___x_2669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2667_, v___x_2668_);
v___x_2670_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
v___x_2671_ = lean_string_append(v___x_2669_, v___x_2670_);
lean_inc(v_instName_2652_);
v___x_2672_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2662_, v_instName_2652_, v_privateSpecs_2663_, v___x_2671_);
lean_dec_ref(v_env_2662_);
lean_inc(v_instName_2652_);
v___x_2673_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed), 6, 1);
lean_closure_set(v___x_2673_, 0, v_instName_2652_);
lean_inc_ref(v_a_2655_);
v___x_2674_ = l_Lean_Meta_realizeConst(v_instName_2652_, v___x_2672_, v___x_2673_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
return v___x_2674_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_instName_2652_);
v_a_2675_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2659_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2659_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___boxed(lean_object* v_instName_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(v_instName_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___redArg(lean_object* v_instName_2690_, lean_object* v_op_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v___x_2695_; lean_object* v_env_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2695_ = lean_st_ref_get(v_a_2693_);
v_env_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc_ref(v_env_2696_);
lean_dec(v___x_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_instInhabitedMethodSpecsAttrData_default));
v___x_2698_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
lean_inc(v_instName_2690_);
lean_inc_ref(v_env_2696_);
v___x_2699_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_2697_, v___x_2698_, v_env_2696_, v_instName_2690_);
if (lean_obj_tag(v___x_2699_) == 1)
{
lean_object* v_val_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2728_; 
v_val_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2728_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_val_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2728_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
uint8_t v_privateSpecs_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_privateSpecs_2704_ = lean_ctor_get_uint8(v_val_2700_, sizeof(void*)*1);
lean_dec(v_val_2700_);
v___x_2705_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
v___x_2706_ = lean_string_append(v_op_2691_, v___x_2705_);
v___x_2707_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2696_, v_instName_2690_, v_privateSpecs_2704_, v___x_2706_);
lean_dec_ref(v_env_2696_);
v___x_2708_ = l_Lean_realizeGlobalConstNoOverloadCore(v___x_2707_, v_a_2692_, v_a_2693_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2719_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2719_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2719_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v_a_2709_);
v___x_2714_ = v___x_2702_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2716_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2714_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_del_object(v___x_2702_);
v_a_2720_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2708_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2708_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec(v___x_2699_);
lean_dec_ref(v_env_2696_);
lean_dec_ref(v_op_2691_);
lean_dec(v_instName_2690_);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___redArg___boxed(lean_object* v_instName_2731_, lean_object* v_op_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_getMethodSpecTheorem___redArg(v_instName_2731_, v_op_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem(lean_object* v_instName_2737_, lean_object* v_op_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_getMethodSpecTheorem___redArg(v_instName_2737_, v_op_2738_, v_a_2741_, v_a_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___boxed(lean_object* v_instName_2745_, lean_object* v_op_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_getMethodSpecTheorem(v_instName_2745_, v_op_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(lean_object* v_op_2753_, lean_object* v_instName_2754_, uint8_t v___x_2755_, lean_object* v___x_2756_, lean_object* v_b_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v_fst_2761_; lean_object* v_snd_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2784_; 
v___x_2760_ = lean_st_ref_get(v___y_2758_);
v_fst_2761_ = lean_ctor_get(v_b_2757_, 0);
v_snd_2762_ = lean_ctor_get(v_b_2757_, 1);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_b_2757_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2764_ = v_b_2757_;
v_isShared_2765_ = v_isSharedCheck_2784_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_snd_2762_);
lean_inc(v_fst_2761_);
lean_dec(v_b_2757_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2784_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_env_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v_env_2766_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_ref(v_env_2766_);
lean_dec(v___x_2760_);
v___x_2767_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1));
lean_inc_ref(v_op_2753_);
v___x_2768_ = lean_string_append(v_op_2753_, v___x_2767_);
v___x_2769_ = lean_unsigned_to_nat(1u);
v___x_2770_ = lean_nat_add(v_fst_2761_, v___x_2769_);
lean_inc(v___x_2770_);
v___x_2771_ = l_Nat_reprFast(v___x_2770_);
v___x_2772_ = lean_string_append(v___x_2768_, v___x_2771_);
lean_dec_ref(v___x_2771_);
lean_inc(v_instName_2754_);
v___x_2773_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2766_, v_instName_2754_, v___x_2755_, v___x_2772_);
lean_dec_ref(v_env_2766_);
lean_inc_ref(v___x_2756_);
v___x_2774_ = l_Lean_Environment_containsOnBranch(v___x_2756_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2776_; 
lean_dec(v___x_2773_);
lean_dec(v___x_2770_);
lean_dec_ref(v___x_2756_);
lean_dec(v_instName_2754_);
lean_dec_ref(v_op_2753_);
if (v_isShared_2765_ == 0)
{
v___x_2776_ = v___x_2764_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_fst_2761_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_snd_2762_);
v___x_2776_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_dec(v_fst_2761_);
v___x_2779_ = lean_array_push(v_snd_2762_, v___x_2773_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 1, v___x_2779_);
lean_ctor_set(v___x_2764_, 0, v___x_2770_);
v___x_2781_ = v___x_2764_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
v_b_2757_ = v___x_2781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg___boxed(lean_object* v_op_2785_, lean_object* v_instName_2786_, lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v_b_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
uint8_t v___x_1804__boxed_2792_; lean_object* v_res_2793_; 
v___x_1804__boxed_2792_ = lean_unbox(v___x_2787_);
v_res_2793_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_2785_, v_instName_2786_, v___x_1804__boxed_2792_, v___x_2788_, v_b_2789_, v___y_2790_);
lean_dec(v___y_2790_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorems(lean_object* v_instName_2799_, lean_object* v_op_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v___x_2806_; lean_object* v_env_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2806_ = lean_st_ref_get(v_a_2804_);
v_env_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc_ref(v_env_2807_);
lean_dec(v___x_2806_);
v___x_2808_ = ((lean_object*)(l_Lean_instInhabitedMethodSpecsAttrData_default));
v___x_2809_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
lean_inc(v_instName_2799_);
v___x_2810_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_2808_, v___x_2809_, v_env_2807_, v_instName_2799_);
if (lean_obj_tag(v___x_2810_) == 1)
{
lean_object* v_val_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2854_; 
v_val_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2854_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_val_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2854_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v_env_2816_; uint8_t v_privateSpecs_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2815_ = lean_st_ref_get(v_a_2804_);
v_env_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc_ref(v_env_2816_);
lean_dec(v___x_2815_);
v_privateSpecs_2817_ = lean_ctor_get_uint8(v_val_2811_, sizeof(void*)*1);
lean_dec(v_val_2811_);
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
lean_inc_ref(v_op_2800_);
v___x_2819_ = lean_string_append(v_op_2800_, v___x_2818_);
lean_inc(v_instName_2799_);
v___x_2820_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2816_, v_instName_2799_, v_privateSpecs_2817_, v___x_2819_);
lean_dec_ref(v_env_2816_);
v___x_2821_ = l_Lean_realizeGlobalConstNoOverloadCore(v___x_2820_, v_a_2803_, v_a_2804_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2822_; lean_object* v_env_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v___x_2821_);
v___x_2822_ = lean_st_ref_get(v_a_2804_);
v_env_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc_ref(v_env_2823_);
lean_dec(v___x_2822_);
v___x_2824_ = ((lean_object*)(l_Lean_getMethodSpecTheorems___closed__1));
v___x_2825_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_2800_, v_instName_2799_, v_privateSpecs_2817_, v_env_2823_, v___x_2824_, v_a_2804_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2837_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2837_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2837_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_snd_2830_; lean_object* v___x_2832_; 
v_snd_2830_ = lean_ctor_get(v_a_2826_, 1);
lean_inc(v_snd_2830_);
lean_dec(v_a_2826_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v_snd_2830_);
v___x_2832_ = v___x_2813_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_snd_2830_);
v___x_2832_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2834_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2832_);
v___x_2834_ = v___x_2828_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_del_object(v___x_2813_);
v_a_2838_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2825_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2825_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_del_object(v___x_2813_);
lean_dec_ref(v_op_2800_);
lean_dec(v_instName_2799_);
v_a_2846_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2821_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2821_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec(v___x_2810_);
lean_dec_ref(v_op_2800_);
lean_dec(v_instName_2799_);
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorems___boxed(lean_object* v_instName_2857_, lean_object* v_op_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_getMethodSpecTheorems(v_instName_2857_, v_op_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0(lean_object* v_op_2865_, lean_object* v_instName_2866_, uint8_t v___x_2867_, lean_object* v___x_2868_, lean_object* v_b_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_2865_, v_instName_2866_, v___x_2867_, v___x_2868_, v_b_2869_, v___y_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___boxed(lean_object* v_op_2876_, lean_object* v_instName_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v_b_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v___x_1972__boxed_2886_; lean_object* v_res_2887_; 
v___x_1972__boxed_2886_ = lean_unbox(v___x_2878_);
v_res_2887_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0(v_op_2876_, v_instName_2877_, v___x_1972__boxed_2886_, v___x_2879_, v_b_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2887_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(lean_object* v_env_2888_, lean_object* v_name_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(v_env_2888_, v_name_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
uint8_t v___x_2891_; 
v___x_2891_ = 0;
return v___x_2891_;
}
else
{
uint8_t v___x_2892_; 
lean_dec_ref(v___x_2890_);
v___x_2892_ = 1;
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object* v_env_2893_, lean_object* v_name_2894_){
_start:
{
uint8_t v_res_2895_; lean_object* v_r_2896_; 
v_res_2895_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v_env_2893_, v_name_2894_);
v_r_2896_ = lean_box(v_res_2895_);
return v_r_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(lean_object* v___x_2897_, lean_object* v_name_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; lean_object* v_env_2903_; lean_object* v___x_2904_; 
v___x_2902_ = lean_st_ref_get(v___y_2900_);
v_env_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc_ref(v_env_2903_);
lean_dec(v___x_2902_);
v___x_2904_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(v_env_2903_, v_name_2898_);
if (lean_obj_tag(v___x_2904_) == 1)
{
lean_object* v_val_2905_; uint8_t v___x_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_val_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_val_2905_);
lean_dec_ref(v___x_2904_);
v___x_2906_ = 0;
v___x_2907_ = 1;
v___x_2908_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2);
v___x_2909_ = lean_unsigned_to_nat(32u);
v___x_2910_ = lean_mk_empty_array_with_capacity(v___x_2909_);
lean_dec_ref(v___x_2910_);
v___x_2911_ = lean_unsigned_to_nat(0u);
v___x_2912_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_2913_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7);
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8));
v___x_2915_ = lean_box(0);
lean_inc(v___x_2897_);
v___x_2916_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2916_, 0, v___x_2908_);
lean_ctor_set(v___x_2916_, 1, v___x_2897_);
lean_ctor_set(v___x_2916_, 2, v___x_2913_);
lean_ctor_set(v___x_2916_, 3, v___x_2914_);
lean_ctor_set(v___x_2916_, 4, v___x_2915_);
lean_ctor_set(v___x_2916_, 5, v___x_2911_);
lean_ctor_set(v___x_2916_, 6, v___x_2915_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*7, v___x_2906_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*7 + 1, v___x_2906_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*7 + 2, v___x_2906_);
lean_ctor_set_uint8(v___x_2916_, sizeof(void*)*7 + 3, v___x_2907_);
v___x_2917_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10);
v___x_2918_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11);
v___x_2919_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12);
v___x_2920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2917_);
lean_ctor_set(v___x_2920_, 1, v___x_2918_);
lean_ctor_set(v___x_2920_, 2, v___x_2897_);
lean_ctor_set(v___x_2920_, 3, v___x_2912_);
lean_ctor_set(v___x_2920_, 4, v___x_2919_);
v___x_2921_ = lean_st_mk_ref(v___x_2920_);
v___x_2922_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(v_val_2905_, v___x_2916_, v___x_2921_, v___y_2899_, v___y_2900_);
lean_dec_ref(v___x_2916_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2931_; 
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_2932_);
v___x_2924_ = v___x_2922_;
v_isShared_2925_ = v_isSharedCheck_2931_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v___x_2922_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2931_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2926_ = lean_st_ref_get(v___x_2921_);
lean_dec(v___x_2921_);
lean_dec(v___x_2926_);
v___x_2927_ = lean_box(v___x_2907_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2927_);
v___x_2929_ = v___x_2924_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
else
{
lean_dec(v___x_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2940_; 
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_2941_);
v___x_2934_ = v___x_2922_;
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
else
{
lean_dec(v___x_2922_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2940_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = lean_box(v___x_2907_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2936_);
v___x_2938_ = v___x_2934_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_a_2942_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2922_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2922_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
else
{
uint8_t v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_dec(v___x_2904_);
lean_dec(v___x_2897_);
v___x_2950_ = 0;
v___x_2951_ = lean_box(v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object* v___x_2953_, lean_object* v_name_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v___x_2953_, v_name_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2963_; lean_object* v___x_2964_; 
v___f_2963_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_));
v___x_2964_ = l_Lean_registerReservedNamePredicate(v___f_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___f_2965_; lean_object* v___x_2966_; 
lean_dec_ref(v___x_2964_);
v___f_2965_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_));
v___x_2966_ = l_Lean_registerReservedNameAction(v___f_2965_);
return v___x_2966_;
}
else
{
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
return v_res_2968_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_unsigned_to_nat(2329740376u);
v___x_2987_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_));
v___x_2988_ = l_Lean_Name_num___override(v___x_2987_, v___x_2986_);
return v___x_2988_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_));
v___x_2991_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_2992_ = l_Lean_Name_str___override(v___x_2991_, v___x_2990_);
return v___x_2992_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_));
v___x_2995_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_2996_ = l_Lean_Name_str___override(v___x_2995_, v___x_2994_);
return v___x_2996_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_unsigned_to_nat(2u);
v___x_2998_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_2999_ = l_Lean_Name_num___override(v___x_2998_, v___x_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3001_; uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3001_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_3002_ = 0;
v___x_3003_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_3004_ = l_Lean_registerTraceClass(v___x_3001_, v___x_3002_, v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2____boxed(lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
return v_res_3006_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_MethodSpecs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr);
lean_dec_ref(res);
res = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_MethodSpecs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_MethodSpecs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MethodSpecs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_MethodSpecs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_MethodSpecs(builtin);
}
#ifdef __cplusplus
}
#endif
