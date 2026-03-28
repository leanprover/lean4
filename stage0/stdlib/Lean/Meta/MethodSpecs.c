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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "MethodSpecs for "};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":\n"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nthms: "};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nprivateSpecs: "};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16_value;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "the definition of `"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18;
static const lean_string_object l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` does not have the expected shape"};
static const lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19 = (const lean_object*)&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19_value;
static lean_once_cell_t l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20;
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(lean_object* v_e_82_, lean_object* v_k_83_, uint8_t v_cleanupAnnotations_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___f_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___f_90_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_90_, 0, v_k_83_);
v___x_91_ = 1;
v___x_92_ = 0;
v___x_93_ = lean_box(0);
v___x_94_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_82_, v___x_91_, v___x_92_, v___x_91_, v___x_92_, v___x_93_, v___f_90_, v_cleanupAnnotations_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
v_a_103_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_94_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_94_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg___boxed(lean_object* v_e_111_, lean_object* v_k_112_, lean_object* v_cleanupAnnotations_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_119_; lean_object* v_res_120_; 
v_cleanupAnnotations_boxed_119_ = lean_unbox(v_cleanupAnnotations_113_);
v_res_120_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_e_111_, v_k_112_, v_cleanupAnnotations_boxed_119_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(lean_object* v_00_u03b1_121_, lean_object* v_e_122_, lean_object* v_k_123_, uint8_t v_cleanupAnnotations_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_e_122_, v_k_123_, v_cleanupAnnotations_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___boxed(lean_object* v_00_u03b1_131_, lean_object* v_e_132_, lean_object* v_k_133_, lean_object* v_cleanupAnnotations_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_140_; lean_object* v_res_141_; 
v_cleanupAnnotations_boxed_140_ = lean_unbox(v_cleanupAnnotations_134_);
v_res_141_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12(v_00_u03b1_131_, v_e_132_, v_k_133_, v_cleanupAnnotations_boxed_140_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(lean_object* v_xs_142_, lean_object* v_x_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_array_get_size(v_xs_142_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0___boxed(lean_object* v_xs_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__0(v_xs_151_, v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec_ref(v_x_152_);
lean_dec_ref(v_xs_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(lean_object* v_msgData_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v_env_166_; lean_object* v___x_167_; lean_object* v_mctx_168_; lean_object* v_lctx_169_; lean_object* v_options_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_165_ = lean_st_ref_get(v___y_163_);
v_env_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_env_166_);
lean_dec(v___x_165_);
v___x_167_ = lean_st_ref_get(v___y_161_);
v_mctx_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc_ref(v_mctx_168_);
lean_dec(v___x_167_);
v_lctx_169_ = lean_ctor_get(v___y_160_, 2);
v_options_170_ = lean_ctor_get(v___y_162_, 2);
lean_inc_ref(v_options_170_);
lean_inc_ref(v_lctx_169_);
v___x_171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_171_, 0, v_env_166_);
lean_ctor_set(v___x_171_, 1, v_mctx_168_);
lean_ctor_set(v___x_171_, 2, v_lctx_169_);
lean_ctor_set(v___x_171_, 3, v_options_170_);
v___x_172_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_msgData_159_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4___boxed(lean_object* v_msgData_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msgData_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_ref_187_; lean_object* v___x_188_; lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_197_; 
v_ref_187_ = lean_ctor_get(v___y_184_, 5);
v___x_188_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_197_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_197_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
lean_inc(v_ref_187_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_ref_187_);
lean_ctor_set(v___x_193_, 1, v_a_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set_tag(v___x_191_, 1);
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg___boxed(lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_204_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0(void){
_start:
{
lean_object* v___x_205_; double v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_float_of_nat(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(lean_object* v_cls_210_, lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_ref_217_; lean_object* v___x_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_263_; 
v_ref_217_ = lean_ctor_get(v___y_214_, 5);
v___x_218_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3_spec__4(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_263_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_263_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_263_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v_traceState_224_; lean_object* v_env_225_; lean_object* v_nextMacroScope_226_; lean_object* v_ngen_227_; lean_object* v_auxDeclNGen_228_; lean_object* v_cache_229_; lean_object* v_messages_230_; lean_object* v_infoState_231_; lean_object* v_snapshotTasks_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_262_; 
v___x_223_ = lean_st_ref_take(v___y_215_);
v_traceState_224_ = lean_ctor_get(v___x_223_, 4);
v_env_225_ = lean_ctor_get(v___x_223_, 0);
v_nextMacroScope_226_ = lean_ctor_get(v___x_223_, 1);
v_ngen_227_ = lean_ctor_get(v___x_223_, 2);
v_auxDeclNGen_228_ = lean_ctor_get(v___x_223_, 3);
v_cache_229_ = lean_ctor_get(v___x_223_, 5);
v_messages_230_ = lean_ctor_get(v___x_223_, 6);
v_infoState_231_ = lean_ctor_get(v___x_223_, 7);
v_snapshotTasks_232_ = lean_ctor_get(v___x_223_, 8);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_262_ == 0)
{
v___x_234_ = v___x_223_;
v_isShared_235_ = v_isSharedCheck_262_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_snapshotTasks_232_);
lean_inc(v_infoState_231_);
lean_inc(v_messages_230_);
lean_inc(v_cache_229_);
lean_inc(v_traceState_224_);
lean_inc(v_auxDeclNGen_228_);
lean_inc(v_ngen_227_);
lean_inc(v_nextMacroScope_226_);
lean_inc(v_env_225_);
lean_dec(v___x_223_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_262_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint64_t v_tid_236_; lean_object* v_traces_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_261_; 
v_tid_236_ = lean_ctor_get_uint64(v_traceState_224_, sizeof(void*)*1);
v_traces_237_ = lean_ctor_get(v_traceState_224_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_traceState_224_);
if (v_isSharedCheck_261_ == 0)
{
v___x_239_ = v_traceState_224_;
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_traces_237_);
lean_dec(v_traceState_224_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; double v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__0);
v___x_243_ = 0;
v___x_244_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__1));
v___x_245_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_245_, 0, v_cls_210_);
lean_ctor_set(v___x_245_, 1, v___x_241_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
lean_ctor_set_float(v___x_245_, sizeof(void*)*3, v___x_242_);
lean_ctor_set_float(v___x_245_, sizeof(void*)*3 + 8, v___x_242_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*3 + 16, v___x_243_);
v___x_246_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___closed__2));
v___x_247_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v_a_219_);
lean_ctor_set(v___x_247_, 2, v___x_246_);
lean_inc(v_ref_217_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_ref_217_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_PersistentArray_push___redArg(v_traces_237_, v___x_248_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_249_);
v___x_251_ = v___x_239_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_249_);
lean_ctor_set_uint64(v_reuseFailAlloc_260_, sizeof(void*)*1, v_tid_236_);
v___x_251_ = v_reuseFailAlloc_260_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 4, v___x_251_);
v___x_253_ = v___x_234_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_env_225_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_nextMacroScope_226_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_ngen_227_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_auxDeclNGen_228_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_259_, 5, v_cache_229_);
lean_ctor_set(v_reuseFailAlloc_259_, 6, v_messages_230_);
lean_ctor_set(v_reuseFailAlloc_259_, 7, v_infoState_231_);
lean_ctor_set(v_reuseFailAlloc_259_, 8, v_snapshotTasks_232_);
v___x_253_ = v_reuseFailAlloc_259_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = lean_st_ref_set(v___y_215_, v___x_253_);
v___x_255_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_255_);
v___x_257_ = v___x_221_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11___boxed(lean_object* v_cls_264_, lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v_cls_264_, v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
if (lean_obj_tag(v_a_272_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = l_List_reverse___redArg(v_a_273_);
return v___x_274_;
}
else
{
lean_object* v_head_275_; lean_object* v_tail_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_285_; 
v_head_275_ = lean_ctor_get(v_a_272_, 0);
v_tail_276_ = lean_ctor_get(v_a_272_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_a_272_);
if (v_isSharedCheck_285_ == 0)
{
v___x_278_ = v_a_272_;
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_tail_276_);
lean_inc(v_head_275_);
lean_dec(v_a_272_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = l_Lean_MessageData_ofExpr(v_head_275_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v_a_273_);
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_a_273_);
v___x_282_ = v_reuseFailAlloc_284_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
v_a_272_ = v_tail_276_;
v_a_273_ = v___x_282_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(size_t v_sz_286_, size_t v_i_287_, lean_object* v_bs_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = lean_usize_dec_lt(v_i_287_, v_sz_286_);
if (v___x_289_ == 0)
{
return v_bs_288_;
}
else
{
lean_object* v_v_290_; lean_object* v_type_291_; lean_object* v___x_292_; lean_object* v_bs_x27_293_; size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; 
v_v_290_ = lean_array_uget_borrowed(v_bs_288_, v_i_287_);
v_type_291_ = lean_ctor_get(v_v_290_, 2);
lean_inc_ref(v_type_291_);
v___x_292_ = lean_unsigned_to_nat(0u);
v_bs_x27_293_ = lean_array_uset(v_bs_288_, v_i_287_, v___x_292_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = lean_usize_add(v_i_287_, v___x_294_);
v___x_296_ = lean_array_uset(v_bs_x27_293_, v_i_287_, v_type_291_);
v_i_287_ = v___x_295_;
v_bs_288_ = v___x_296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9___boxed(lean_object* v_sz_298_, lean_object* v_i_299_, lean_object* v_bs_300_){
_start:
{
size_t v_sz_boxed_301_; size_t v_i_boxed_302_; lean_object* v_res_303_; 
v_sz_boxed_301_ = lean_unbox_usize(v_sz_298_);
lean_dec(v_sz_298_);
v_i_boxed_302_ = lean_unbox_usize(v_i_299_);
lean_dec(v_i_299_);
v_res_303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(v_sz_boxed_301_, v_i_boxed_302_, v_bs_300_);
return v_res_303_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__1));
v___x_308_ = l_Lean_MessageData_ofFormat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_box(1);
v___x_310_ = l_Lean_MessageData_ofFormat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
if (lean_obj_tag(v_a_311_) == 0)
{
lean_object* v___x_313_; 
v___x_313_ = l_List_reverse___redArg(v_a_312_);
return v___x_313_;
}
else
{
lean_object* v_head_314_; lean_object* v_tail_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_339_; 
v_head_314_ = lean_ctor_get(v_a_311_, 0);
v_tail_315_ = lean_ctor_get(v_a_311_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_311_);
if (v_isSharedCheck_339_ == 0)
{
v___x_317_ = v_a_311_;
v_isShared_318_ = v_isSharedCheck_339_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_tail_315_);
lean_inc(v_head_314_);
lean_dec(v_a_311_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_339_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_fst_319_; lean_object* v_snd_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_338_; 
v_fst_319_ = lean_ctor_get(v_head_314_, 0);
v_snd_320_ = lean_ctor_get(v_head_314_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_head_314_);
if (v_isSharedCheck_338_ == 0)
{
v___x_322_ = v_head_314_;
v_isShared_323_ = v_isSharedCheck_338_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_snd_320_);
lean_inc(v_fst_319_);
lean_dec(v_head_314_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_338_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = l_Lean_MessageData_ofName(v_fst_319_);
v___x_325_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__2);
if (v_isShared_323_ == 0)
{
lean_ctor_set_tag(v___x_322_, 7);
lean_ctor_set(v___x_322_, 1, v___x_325_);
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_337_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_328_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8___closed__3);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_MessageData_ofName(v_snd_320_);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_Lean_MessageData_paren(v___x_331_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v_a_312_);
lean_ctor_set(v___x_317_, 0, v___x_332_);
v___x_334_ = v___x_317_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_a_312_);
v___x_334_ = v_reuseFailAlloc_336_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
v_a_311_ = v_tail_315_;
v_a_312_ = v___x_334_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
if (lean_obj_tag(v_a_340_) == 0)
{
lean_object* v___x_342_; 
v___x_342_ = l_List_reverse___redArg(v_a_341_);
return v___x_342_;
}
else
{
lean_object* v_head_343_; lean_object* v_tail_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_353_; 
v_head_343_ = lean_ctor_get(v_a_340_, 0);
v_tail_344_ = lean_ctor_get(v_a_340_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_a_340_);
if (v_isSharedCheck_353_ == 0)
{
v___x_346_ = v_a_340_;
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_tail_344_);
lean_inc(v_head_343_);
lean_dec(v_a_340_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_353_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = l_Lean_mkLevelParam(v_head_343_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_a_341_);
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_a_341_);
v___x_350_ = v_reuseFailAlloc_352_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
v_a_340_ = v_tail_344_;
v_a_341_ = v___x_350_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(lean_object* v_xs_354_, lean_object* v_ys_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_zero_357_; uint8_t v_isZero_358_; 
v_zero_357_ = lean_unsigned_to_nat(0u);
v_isZero_358_ = lean_nat_dec_eq(v_x_356_, v_zero_357_);
if (v_isZero_358_ == 1)
{
lean_dec(v_x_356_);
return v_isZero_358_;
}
else
{
lean_object* v_one_359_; lean_object* v_n_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_one_359_ = lean_unsigned_to_nat(1u);
v_n_360_ = lean_nat_sub(v_x_356_, v_one_359_);
lean_dec(v_x_356_);
v___x_361_ = lean_array_fget_borrowed(v_xs_354_, v_n_360_);
v___x_362_ = lean_array_fget_borrowed(v_ys_355_, v_n_360_);
v___x_363_ = lean_expr_eqv(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v_n_360_);
return v___x_363_;
}
else
{
v_x_356_ = v_n_360_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg___boxed(lean_object* v_xs_365_, lean_object* v_ys_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_365_, v_ys_366_, v_x_367_);
lean_dec_ref(v_ys_366_);
lean_dec_ref(v_xs_365_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
if (lean_obj_tag(v_a_370_) == 0)
{
lean_object* v___x_372_; 
v___x_372_ = l_List_reverse___redArg(v_a_371_);
return v___x_372_;
}
else
{
lean_object* v_head_373_; lean_object* v_tail_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v_head_373_ = lean_ctor_get(v_a_370_, 0);
v_tail_374_ = lean_ctor_get(v_a_370_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_a_370_);
if (v_isSharedCheck_383_ == 0)
{
v___x_376_ = v_a_370_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_tail_374_);
lean_inc(v_head_373_);
lean_dec(v_a_370_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = l_Lean_MessageData_ofLevel(v_head_373_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v_a_371_);
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_371_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
v_a_370_ = v_tail_374_;
v_a_371_ = v___x_380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
if (lean_obj_tag(v_x_385_) == 0)
{
uint8_t v___x_386_; 
v___x_386_ = 1;
return v___x_386_;
}
else
{
uint8_t v___x_387_; 
v___x_387_ = 0;
return v___x_387_;
}
}
else
{
if (lean_obj_tag(v_x_385_) == 0)
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
else
{
lean_object* v_head_389_; lean_object* v_tail_390_; lean_object* v_head_391_; lean_object* v_tail_392_; uint8_t v___x_393_; 
v_head_389_ = lean_ctor_get(v_x_384_, 0);
v_tail_390_ = lean_ctor_get(v_x_384_, 1);
v_head_391_ = lean_ctor_get(v_x_385_, 0);
v_tail_392_ = lean_ctor_get(v_x_385_, 1);
v___x_393_ = lean_level_eq(v_head_389_, v_head_391_);
if (v___x_393_ == 0)
{
return v___x_393_;
}
else
{
v_x_384_ = v_tail_390_;
v_x_385_ = v_tail_392_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5___boxed(lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(v_x_395_, v_x_396_);
lean_dec(v_x_396_);
lean_dec(v_x_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0(void){
_start:
{
lean_object* v___x_399_; lean_object* v_dummy_400_; 
v___x_399_ = lean_box(0);
v_dummy_400_ = l_Lean_Expr_sort___override(v___x_399_);
return v_dummy_400_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__1));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__3));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__5));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__7));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__9));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__11));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__13));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__15));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__17));
v___x_427_ = l_Lean_stringToMessageData(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__19));
v___x_430_ = l_Lean_stringToMessageData(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(lean_object* v_val_431_, lean_object* v_a_432_, lean_object* v___x_433_, lean_object* v_xs_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_as_437_, size_t v_sz_438_, size_t v_i_439_, lean_object* v_b_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_a_447_; uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_lt(v_i_439_, v_sz_438_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_b_440_);
return v___x_452_;
}
else
{
lean_object* v_snd_453_; lean_object* v_snd_454_; lean_object* v_snd_455_; lean_object* v_fst_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_729_; 
v_snd_453_ = lean_ctor_get(v_b_440_, 1);
lean_inc(v_snd_453_);
v_snd_454_ = lean_ctor_get(v_snd_453_, 1);
lean_inc(v_snd_454_);
v_snd_455_ = lean_ctor_get(v_snd_454_, 1);
lean_inc(v_snd_455_);
v_fst_456_ = lean_ctor_get(v_b_440_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_b_440_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_b_440_, 1);
lean_dec(v_unused_730_);
v___x_458_ = v_b_440_;
v_isShared_459_ = v_isSharedCheck_729_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_fst_456_);
lean_dec(v_b_440_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_729_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_fst_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_727_; 
v_fst_460_ = lean_ctor_get(v_snd_453_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_snd_453_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_snd_453_, 1);
lean_dec(v_unused_728_);
v___x_462_ = v_snd_453_;
v_isShared_463_ = v_isSharedCheck_727_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_fst_460_);
lean_dec(v_snd_453_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_727_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_fst_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_725_; 
v_fst_464_ = lean_ctor_get(v_snd_454_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_snd_454_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_snd_454_, 1);
lean_dec(v_unused_726_);
v___x_466_ = v_snd_454_;
v_isShared_467_ = v_isSharedCheck_725_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_fst_464_);
lean_dec(v_snd_454_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_725_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v_array_468_; lean_object* v_start_469_; lean_object* v_stop_470_; uint8_t v___x_471_; 
v_array_468_ = lean_ctor_get(v_snd_455_, 0);
v_start_469_ = lean_ctor_get(v_snd_455_, 1);
v_stop_470_ = lean_ctor_get(v_snd_455_, 2);
v___x_471_ = lean_nat_dec_lt(v_start_469_, v_stop_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_473_; 
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
if (v_isShared_467_ == 0)
{
v___x_473_ = v___x_466_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_snd_455_);
v___x_473_ = v_reuseFailAlloc_481_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_473_);
v___x_475_ = v___x_462_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_475_);
v___x_477_ = v___x_458_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_fst_456_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
}
else
{
lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_721_; 
lean_inc(v_stop_470_);
lean_inc(v_start_469_);
lean_inc_ref(v_array_468_);
v_isSharedCheck_721_ = !lean_is_exclusive(v_snd_455_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_722_ = lean_ctor_get(v_snd_455_, 2);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_snd_455_, 1);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_snd_455_, 0);
lean_dec(v_unused_724_);
v___x_483_ = v_snd_455_;
v_isShared_484_ = v_isSharedCheck_721_;
goto v_resetjp_482_;
}
else
{
lean_dec(v_snd_455_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_721_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_array_fget(v_array_468_, v_start_469_);
lean_inc(v___x_485_);
v___x_486_ = l_Lean_Meta_isProof(v___x_485_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_start_469_, v___x_488_);
lean_dec(v_start_469_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_489_);
v___x_491_ = v___x_483_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_array_468_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_stop_470_);
v___x_491_ = v_reuseFailAlloc_712_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
uint8_t v___x_492_; 
v___x_492_ = lean_unbox(v_a_487_);
if (v___x_492_ == 0)
{
lean_object* v_a_493_; uint8_t v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___x_512_; lean_object* v___y_514_; uint8_t v_privateSpecs_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___x_604_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v_dummy_644_; lean_object* v_nargs_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___x_688_; 
v_a_493_ = lean_array_uget_borrowed(v_as_437_, v_i_439_);
v___x_512_ = l_Lean_Expr_eta(v___x_485_);
v___x_604_ = l_Lean_Expr_getAppFn(v___x_512_);
v_dummy_644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
v_nargs_645_ = l_Lean_Expr_getAppNumArgs(v___x_512_);
lean_inc(v_nargs_645_);
v___x_646_ = lean_mk_array(v_nargs_645_, v_dummy_644_);
v___x_647_ = lean_nat_sub(v_nargs_645_, v___x_488_);
lean_dec(v_nargs_645_);
lean_inc_ref(v___x_512_);
v___x_648_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_512_, v___x_646_, v___x_647_);
v___x_688_ = l_Lean_Expr_isConst(v___x_604_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__18);
lean_inc(v_a_493_);
v___x_690_ = l_Lean_MessageData_ofName(v_a_493_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__20);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_693_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_dec_ref(v___x_694_);
v___y_659_ = v___y_441_;
v___y_660_ = v___y_442_;
v___y_661_ = v___y_443_;
v___y_662_ = v___y_444_;
goto v___jp_658_;
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v___x_604_);
lean_dec_ref(v___x_512_);
lean_dec_ref(v___x_491_);
lean_dec(v_a_487_);
lean_del_object(v___x_466_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
v___y_659_ = v___y_441_;
v___y_660_ = v___y_442_;
v___y_661_ = v___y_443_;
v___y_662_ = v___y_444_;
goto v___jp_658_;
}
v___jp_494_:
{
lean_object* v___x_499_; 
lean_inc(v___y_496_);
lean_inc(v_a_493_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___y_496_);
lean_ctor_set(v___x_466_, 0, v_a_493_);
v___x_499_ = v___x_466_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_493_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___y_496_);
v___x_499_ = v_reuseFailAlloc_511_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_500_ = lean_array_push(v_fst_456_, v___x_499_);
lean_inc(v___x_435_);
v___x_501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_501_, 0, v___y_496_);
lean_ctor_set(v___x_501_, 1, v___x_435_);
lean_ctor_set(v___x_501_, 2, v___y_497_);
v___x_502_ = lean_array_push(v_fst_460_, v___x_501_);
v___x_503_ = lean_box(v___y_495_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_491_);
lean_ctor_set(v___x_462_, 0, v___x_503_);
v___x_505_ = v___x_462_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_491_);
v___x_505_ = v_reuseFailAlloc_510_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_507_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_505_);
lean_ctor_set(v___x_458_, 0, v___x_502_);
v___x_507_ = v___x_458_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_500_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v_a_447_ = v___x_508_;
goto v___jp_446_;
}
}
}
}
v___jp_513_:
{
lean_object* v___x_520_; lean_object* v_env_521_; lean_object* v___x_522_; 
v___x_520_ = lean_st_ref_get(v___y_519_);
v_env_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_env_521_);
lean_dec(v___x_520_);
lean_inc(v_a_493_);
lean_inc(v_val_431_);
v___x_522_ = l_Lean_getFieldInfo_x3f(v_env_521_, v_val_431_, v_a_493_);
if (lean_obj_tag(v___x_522_) == 1)
{
lean_object* v_val_523_; lean_object* v_projFn_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_dummy_528_; lean_object* v_nargs_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_val_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref(v___x_522_);
v_projFn_524_ = lean_ctor_get(v_val_523_, 1);
lean_inc(v_projFn_524_);
lean_dec(v_val_523_);
v___x_525_ = l_Lean_Expr_getAppFn(v_a_432_);
v___x_526_ = l_Lean_Expr_constLevels_x21(v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = l_Lean_mkConst(v_projFn_524_, v___x_526_);
v_dummy_528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
v_nargs_529_ = l_Lean_Expr_getAppNumArgs(v_a_432_);
lean_inc(v_nargs_529_);
v___x_530_ = lean_mk_array(v_nargs_529_, v_dummy_528_);
v___x_531_ = lean_nat_sub(v_nargs_529_, v___x_488_);
lean_dec(v_nargs_529_);
lean_inc_ref(v_a_432_);
v___x_532_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_432_, v___x_530_, v___x_531_);
v___x_533_ = lean_mk_empty_array_with_capacity(v___x_488_);
lean_inc_ref(v___x_433_);
v___x_534_ = lean_array_push(v___x_533_, v___x_433_);
v___x_535_ = l_Array_append___redArg(v___x_532_, v___x_534_);
lean_dec_ref(v___x_534_);
v___x_536_ = l_Lean_mkAppN(v___x_527_, v___x_535_);
lean_dec_ref(v___x_535_);
lean_inc_ref(v___x_536_);
lean_inc_ref(v___x_512_);
v___x_537_ = l_Lean_Meta_mkEq(v___x_512_, v___x_536_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; uint8_t v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc_n(v_a_538_, 2);
lean_dec_ref(v___x_537_);
v___x_539_ = 1;
v___x_540_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
v___x_541_ = l_Lean_Meta_mkForallFVars(v_xs_434_, v_a_538_, v___x_540_, v___x_471_, v___x_471_, v___x_539_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref(v___x_541_);
v___x_543_ = l_Lean_Meta_isExprDefEq(v___x_512_, v___x_536_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; uint8_t v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_unbox(v_a_544_);
lean_dec(v_a_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__2);
v___x_547_ = l_Lean_MessageData_ofExpr(v_a_538_);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__4);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_550_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_dec_ref(v___x_551_);
v___y_495_ = v_privateSpecs_515_;
v___y_496_ = v___y_514_;
v___y_497_ = v_a_542_;
goto v___jp_494_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_a_542_);
lean_dec(v___y_514_);
lean_dec_ref(v___x_491_);
lean_del_object(v___x_466_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_dec(v_a_538_);
v___y_495_ = v_privateSpecs_515_;
v___y_496_ = v___y_514_;
v___y_497_ = v_a_542_;
goto v___jp_494_;
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_a_542_);
lean_dec(v_a_538_);
lean_dec(v___y_514_);
lean_dec_ref(v___x_491_);
lean_del_object(v___x_466_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_560_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_543_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_543_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_a_538_);
lean_dec_ref(v___x_536_);
lean_dec(v___y_514_);
lean_dec_ref(v___x_512_);
lean_dec_ref(v___x_491_);
lean_del_object(v___x_466_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_568_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_541_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_541_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v___x_536_);
lean_dec(v___y_514_);
lean_dec_ref(v___x_512_);
lean_dec_ref(v___x_491_);
lean_dec(v_a_487_);
lean_del_object(v___x_466_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_576_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_537_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_537_);
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
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v___x_522_);
lean_dec(v___y_514_);
lean_dec_ref(v___x_512_);
lean_dec(v_a_487_);
lean_del_object(v___x_466_);
lean_del_object(v___x_462_);
lean_del_object(v___x_458_);
v___x_584_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__6);
lean_inc(v_a_493_);
v___x_585_ = l_Lean_MessageData_ofName(v_a_493_);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__8);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
lean_inc(v_val_431_);
v___x_589_ = l_Lean_MessageData_ofName(v_val_431_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_590_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref(v___x_591_);
v___x_592_ = lean_box(v_privateSpecs_515_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_491_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_fst_460_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_fst_456_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v_a_447_ = v___x_595_;
goto v___jp_446_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v___x_491_);
lean_dec(v_fst_460_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_596_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_591_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_591_);
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
}
v___jp_605_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_env_612_; lean_object* v_env_613_; lean_object* v___x_614_; uint8_t v_isModule_615_; lean_object* v___x_616_; 
v___x_610_ = lean_st_ref_get(v___y_609_);
v___x_611_ = lean_st_ref_get(v___y_609_);
v_env_612_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_612_);
lean_dec(v___x_610_);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
lean_inc_ref(v_env_613_);
lean_dec(v___x_611_);
v___x_614_ = l_Lean_Environment_header(v_env_612_);
lean_dec_ref(v_env_612_);
v_isModule_615_ = lean_ctor_get_uint8(v___x_614_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_614_);
v___x_616_ = l_Lean_Expr_constName_x21(v___x_604_);
lean_dec_ref(v___x_604_);
if (v_isModule_615_ == 0)
{
uint8_t v___x_617_; 
lean_dec_ref(v_env_613_);
v___x_617_ = lean_unbox(v_fst_464_);
lean_dec(v_fst_464_);
v___y_514_ = v___x_616_;
v_privateSpecs_515_ = v___x_617_;
v___y_516_ = v___y_606_;
v___y_517_ = v___y_607_;
v___y_518_ = v___y_608_;
v___y_519_ = v___y_609_;
goto v___jp_513_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_Environment_setExporting(v_env_613_, v___x_471_);
v___x_619_ = lean_unbox(v_a_487_);
lean_inc(v___x_616_);
v___x_620_ = l_Lean_Environment_find_x3f(v___x_618_, v___x_616_, v___x_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec(v_fst_464_);
v___y_514_ = v___x_616_;
v_privateSpecs_515_ = v___x_471_;
v___y_516_ = v___y_606_;
v___y_517_ = v___y_607_;
v___y_518_ = v___y_608_;
v___y_519_ = v___y_609_;
goto v___jp_513_;
}
else
{
lean_object* v_val_621_; uint8_t v___x_622_; uint8_t v___x_623_; 
v_val_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_val_621_);
lean_dec_ref(v___x_620_);
v___x_622_ = lean_unbox(v_a_487_);
v___x_623_ = l_Lean_ConstantInfo_hasValue(v_val_621_, v___x_622_);
lean_dec(v_val_621_);
if (v___x_623_ == 0)
{
lean_dec(v_fst_464_);
v___y_514_ = v___x_616_;
v_privateSpecs_515_ = v___x_471_;
v___y_516_ = v___y_606_;
v___y_517_ = v___y_607_;
v___y_518_ = v___y_608_;
v___y_519_ = v___y_609_;
goto v___jp_513_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = lean_unbox(v_fst_464_);
lean_dec(v_fst_464_);
v___y_514_ = v___x_616_;
v_privateSpecs_515_ = v___x_624_;
v___y_516_ = v___y_606_;
v___y_517_ = v___y_607_;
v___y_518_ = v___y_608_;
v___y_519_ = v___y_609_;
goto v___jp_513_;
}
}
}
}
v___jp_625_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
lean_inc_ref(v___x_604_);
v___x_631_ = l_Lean_MessageData_ofExpr(v___x_604_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__12);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_634_, v___y_627_, v___y_628_, v___y_626_, v___y_629_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_dec_ref(v___x_635_);
v___y_606_ = v___y_627_;
v___y_607_ = v___y_628_;
v___y_608_ = v___y_626_;
v___y_609_ = v___y_629_;
goto v___jp_605_;
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v___x_604_);
lean_dec_ref(v___x_512_);
lean_dec_ref(v___x_491_);
lean_dec(v_a_487_);
lean_del_object(v___x_466_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
v___jp_649_:
{
lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_array_get_size(v_xs_434_);
v___x_655_ = lean_array_get_size(v___x_648_);
v___x_656_ = lean_nat_dec_eq(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec_ref(v___x_648_);
v___y_626_ = v___y_652_;
v___y_627_ = v___y_650_;
v___y_628_ = v___y_651_;
v___y_629_ = v___y_653_;
goto v___jp_625_;
}
else
{
uint8_t v___x_657_; 
v___x_657_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_434_, v___x_648_, v___x_654_);
lean_dec_ref(v___x_648_);
if (v___x_657_ == 0)
{
v___y_626_ = v___y_652_;
v___y_627_ = v___y_650_;
v___y_628_ = v___y_651_;
v___y_629_ = v___y_653_;
goto v___jp_625_;
}
else
{
v___y_606_ = v___y_650_;
v___y_607_ = v___y_651_;
v___y_608_ = v___y_652_;
v___y_609_ = v___y_653_;
goto v___jp_605_;
}
}
}
v___jp_658_:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = l_Lean_Expr_constLevels_x21(v___x_604_);
v___x_664_ = l_List_beq___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__5(v___x_663_, v___x_436_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__10);
lean_inc_ref(v___x_604_);
v___x_666_ = l_Lean_MessageData_ofExpr(v___x_604_);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__14);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_box(0);
v___x_671_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_663_, v___x_670_);
v___x_672_ = l_Lean_MessageData_ofList(v___x_671_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_669_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__16);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
lean_inc(v___x_436_);
v___x_676_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__6(v___x_436_, v___x_670_);
v___x_677_ = l_Lean_MessageData_ofList(v___x_676_);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_675_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_678_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_dec_ref(v___x_679_);
v___y_650_ = v___y_659_;
v___y_651_ = v___y_660_;
v___y_652_ = v___y_661_;
v___y_653_ = v___y_662_;
goto v___jp_649_;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v___x_604_);
lean_dec_ref(v___x_512_);
lean_dec_ref(v___x_491_);
lean_dec(v_a_487_);
lean_del_object(v___x_466_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_dec(v___x_663_);
v___y_650_ = v___y_659_;
v___y_651_ = v___y_660_;
v___y_652_ = v___y_661_;
v___y_653_ = v___y_662_;
goto v___jp_649_;
}
}
}
else
{
lean_object* v___x_704_; 
lean_dec(v_a_487_);
lean_dec(v___x_485_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_491_);
v___x_704_ = v___x_466_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_491_);
v___x_704_ = v_reuseFailAlloc_711_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_706_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_704_);
v___x_706_ = v___x_462_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_704_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_706_);
v___x_708_ = v___x_458_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_fst_456_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
v_a_447_ = v___x_708_;
goto v___jp_446_;
}
}
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v___x_485_);
lean_del_object(v___x_483_);
lean_dec(v_stop_470_);
lean_dec(v_start_469_);
lean_dec_ref(v_array_468_);
lean_del_object(v___x_466_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_dec(v_fst_456_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
lean_dec_ref(v___x_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_val_431_);
v_a_713_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_486_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_486_);
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
}
}
}
}
}
v___jp_446_:
{
size_t v___x_448_; size_t v___x_449_; 
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_439_, v___x_448_);
v_i_439_ = v___x_449_;
v_b_440_ = v_a_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___boxed(lean_object* v_val_731_, lean_object* v_a_732_, lean_object* v___x_733_, lean_object* v_xs_734_, lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v_as_737_, lean_object* v_sz_738_, lean_object* v_i_739_, lean_object* v_b_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
size_t v_sz_boxed_746_; size_t v_i_boxed_747_; lean_object* v_res_748_; 
v_sz_boxed_746_ = lean_unbox_usize(v_sz_738_);
lean_dec(v_sz_738_);
v_i_boxed_747_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_res_748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_731_, v_a_732_, v___x_733_, v_xs_734_, v___x_735_, v___x_736_, v_as_737_, v_sz_boxed_746_, v_i_boxed_747_, v_b_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v_as_737_);
lean_dec_ref(v_xs_734_);
return v_res_748_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__5));
v___x_761_ = l_Lean_Name_append(v___x_760_, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__7));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__9));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__11));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__13));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__17));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__19));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(lean_object* v_type_782_, lean_object* v_val_783_, lean_object* v_levelParams_784_, lean_object* v_name_785_, lean_object* v_val_786_, uint8_t v___x_787_, lean_object* v_instName_788_, lean_object* v_a_789_, lean_object* v_xs_790_, lean_object* v_body_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_instantiateForall(v_type_782_, v_xs_790_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
lean_inc_ref(v_body_791_);
v___x_829_ = l_Lean_Meta_isConstructorApp(v_body_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v___x_829_);
v___x_831_ = lean_box(0);
lean_inc(v_levelParams_784_);
v___x_832_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_784_, v___x_831_);
lean_inc(v___x_832_);
v___x_833_ = l_Lean_mkConst(v_name_785_, v___x_832_);
v___x_834_ = l_Lean_mkAppN(v___x_833_, v_xs_790_);
v___x_937_ = lean_array_get_size(v_xs_790_);
v___x_938_ = lean_nat_dec_eq(v___x_937_, v_a_789_);
if (v___x_938_ == 0)
{
lean_dec_ref(v___x_834_);
lean_dec(v___x_832_);
lean_dec(v_a_830_);
lean_dec(v_a_828_);
lean_dec_ref(v_body_791_);
lean_dec(v_levelParams_784_);
lean_dec(v_val_783_);
goto v___jp_922_;
}
else
{
uint8_t v___x_939_; 
v___x_939_ = lean_unbox(v_a_830_);
lean_dec(v_a_830_);
if (v___x_939_ == 0)
{
lean_dec_ref(v___x_834_);
lean_dec(v___x_832_);
lean_dec(v_a_828_);
lean_dec_ref(v_body_791_);
lean_dec(v_levelParams_784_);
lean_dec(v_val_783_);
goto v___jp_922_;
}
else
{
v___y_836_ = v___y_792_;
v___y_837_ = v___y_793_;
v___y_838_ = v___y_794_;
v___y_839_ = v___y_795_;
goto v___jp_835_;
}
}
v___jp_835_:
{
lean_object* v_fieldNames_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_dummy_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; size_t v_sz_853_; size_t v___x_854_; lean_object* v___x_855_; 
v_fieldNames_840_ = lean_ctor_get(v_val_786_, 1);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__0));
v___x_843_ = lean_array_get_size(v_fieldNames_840_);
v_dummy_844_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7___closed__0);
v___x_845_ = lean_mk_array(v___x_843_, v_dummy_844_);
v___x_846_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v___x_843_, v_body_791_, v___x_845_);
v___x_847_ = lean_array_get_size(v___x_846_);
v___x_848_ = l_Array_toSubarray___redArg(v___x_846_, v___x_841_, v___x_847_);
v___x_849_ = lean_box(v___x_787_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_848_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_842_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_842_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v_sz_853_ = lean_array_size(v_fieldNames_840_);
v___x_854_ = ((size_t)0ULL);
lean_inc(v_val_783_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__7(v_val_783_, v_a_828_, v___x_834_, v_xs_790_, v_levelParams_784_, v___x_832_, v_fieldNames_840_, v_sz_853_, v___x_854_, v___x_852_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v_snd_857_; lean_object* v_snd_858_; lean_object* v_options_859_; uint8_t v_hasTrace_860_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
v_snd_857_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_857_);
v_snd_858_ = lean_ctor_get(v_snd_857_, 1);
lean_inc(v_snd_858_);
v_options_859_ = lean_ctor_get(v___y_838_, 2);
v_hasTrace_860_ = lean_ctor_get_uint8(v_options_859_, sizeof(void*)*1);
if (v_hasTrace_860_ == 0)
{
lean_object* v_fst_861_; lean_object* v_fst_862_; lean_object* v_fst_863_; 
lean_dec(v_instName_788_);
v_fst_861_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_fst_861_);
lean_dec(v_a_856_);
v_fst_862_ = lean_ctor_get(v_snd_857_, 0);
lean_inc(v_fst_862_);
lean_dec(v_snd_857_);
v_fst_863_ = lean_ctor_get(v_snd_858_, 0);
lean_inc(v_fst_863_);
lean_dec(v_snd_858_);
v___y_798_ = v_fst_862_;
v___y_799_ = v_fst_861_;
v___y_800_ = v_fst_863_;
goto v___jp_797_;
}
else
{
lean_object* v_fst_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_912_; 
v_fst_864_ = lean_ctor_get(v_a_856_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v_a_856_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v_a_856_, 1);
lean_dec(v_unused_913_);
v___x_866_ = v_a_856_;
v_isShared_867_ = v_isSharedCheck_912_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_fst_864_);
lean_dec(v_a_856_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_912_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_fst_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_910_; 
v_fst_868_ = lean_ctor_get(v_snd_857_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_snd_857_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_snd_857_, 1);
lean_dec(v_unused_911_);
v___x_870_ = v_snd_857_;
v_isShared_871_ = v_isSharedCheck_910_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_fst_868_);
lean_dec(v_snd_857_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_910_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_fst_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_908_; 
v_fst_872_ = lean_ctor_get(v_snd_858_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_snd_858_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_snd_858_, 1);
lean_dec(v_unused_909_);
v___x_874_ = v_snd_858_;
v_isShared_875_ = v_isSharedCheck_908_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_fst_872_);
lean_dec(v_snd_858_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_908_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_inheritedTraceOptions_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_inheritedTraceOptions_876_ = lean_ctor_get(v___y_838_, 13);
v___x_877_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_878_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
v___x_879_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_876_, v_options_859_, v___x_878_);
if (v___x_879_ == 0)
{
lean_del_object(v___x_874_);
lean_del_object(v___x_870_);
lean_del_object(v___x_866_);
lean_dec(v_instName_788_);
v___y_798_ = v_fst_868_;
v___y_799_ = v_fst_864_;
v___y_800_ = v_fst_872_;
goto v___jp_797_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__8);
v___x_881_ = l_Lean_MessageData_ofName(v_instName_788_);
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 7);
lean_ctor_set(v___x_874_, 1, v___x_881_);
lean_ctor_set(v___x_874_, 0, v___x_880_);
v___x_883_ = v___x_874_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_907_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__10);
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 7);
lean_ctor_set(v___x_870_, 1, v___x_884_);
lean_ctor_set(v___x_870_, 0, v___x_883_);
v___x_886_ = v___x_870_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_906_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
lean_inc(v_fst_864_);
v___x_887_ = lean_array_to_list(v_fst_864_);
v___x_888_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__8(v___x_887_, v___x_831_);
v___x_889_ = l_Lean_MessageData_ofList(v___x_888_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 7);
lean_ctor_set(v___x_866_, 1, v___x_889_);
lean_ctor_set(v___x_866_, 0, v___x_886_);
v___x_891_ = v___x_866_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_905_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; size_t v_sz_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__12);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v_sz_894_ = lean_array_size(v_fst_868_);
lean_inc(v_fst_868_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__9(v_sz_894_, v___x_854_, v_fst_868_);
v___x_896_ = lean_array_to_list(v___x_895_);
v___x_897_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__10(v___x_896_, v___x_831_);
v___x_898_ = l_Lean_MessageData_ofList(v___x_897_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_893_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__14);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_unbox(v_fst_872_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__15));
v___y_805_ = v_fst_868_;
v___y_806_ = v___x_877_;
v___y_807_ = v_fst_864_;
v___y_808_ = v___y_839_;
v___y_809_ = v___y_838_;
v___y_810_ = v___y_836_;
v___y_811_ = v___y_837_;
v___y_812_ = v_fst_872_;
v___y_813_ = v___x_901_;
v___y_814_ = v___x_903_;
goto v___jp_804_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__16));
v___y_805_ = v_fst_868_;
v___y_806_ = v___x_877_;
v___y_807_ = v_fst_864_;
v___y_808_ = v___y_839_;
v___y_809_ = v___y_838_;
v___y_810_ = v___y_836_;
v___y_811_ = v___y_837_;
v___y_812_ = v_fst_872_;
v___y_813_ = v___x_901_;
v___y_814_ = v___x_904_;
goto v___jp_804_;
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
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_instName_788_);
lean_dec(v_val_783_);
v_a_914_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_855_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_855_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
v___jp_922_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v___x_923_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__18);
v___x_924_ = l_Lean_MessageData_ofConstName(v_instName_788_, v___x_787_);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__20);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_927_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_828_);
lean_dec_ref(v_body_791_);
lean_dec(v_instName_788_);
lean_dec(v_name_785_);
lean_dec(v_levelParams_784_);
lean_dec(v_val_783_);
v_a_940_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_829_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_829_);
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
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_body_791_);
lean_dec(v_instName_788_);
lean_dec(v_name_785_);
lean_dec(v_levelParams_784_);
lean_dec(v_val_783_);
v_a_948_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_827_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_827_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
v___jp_797_:
{
lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_801_, 0, v_val_783_);
lean_ctor_set(v___x_801_, 1, v___y_799_);
lean_ctor_set(v___x_801_, 2, v___y_798_);
v___x_802_ = lean_unbox(v___y_800_);
lean_dec(v___y_800_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*3, v___x_802_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
return v___x_803_;
}
v___jp_804_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_inc_ref(v___y_814_);
v___x_815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_815_, 0, v___y_814_);
v___x_816_ = l_Lean_MessageData_ofFormat(v___x_815_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___y_813_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
lean_inc(v___y_806_);
v___x_818_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___y_806_, v___x_817_, v___y_810_, v___y_811_, v___y_809_, v___y_808_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_dec_ref(v___x_818_);
v___y_798_ = v___y_805_;
v___y_799_ = v___y_807_;
v___y_800_ = v___y_812_;
goto v___jp_797_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v___y_812_);
lean_dec(v___y_807_);
lean_dec(v___y_805_);
lean_dec(v_val_783_);
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed(lean_object* v_type_956_, lean_object* v_val_957_, lean_object* v_levelParams_958_, lean_object* v_name_959_, lean_object* v_val_960_, lean_object* v___x_961_, lean_object* v_instName_962_, lean_object* v_a_963_, lean_object* v_xs_964_, lean_object* v_body_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_20073__boxed_971_; lean_object* v_res_972_; 
v___x_20073__boxed_971_ = lean_unbox(v___x_961_);
v_res_972_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1(v_type_956_, v_val_957_, v_levelParams_958_, v_name_959_, v_val_960_, v___x_20073__boxed_971_, v_instName_962_, v_a_963_, v_xs_964_, v_body_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_xs_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_val_960_);
return v_res_972_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_instMonadEIO(lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_toApplicative_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1047_; 
v___x_984_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__0);
v___x_985_ = l_StateRefT_x27_instMonad___redArg(v___x_984_);
v_toApplicative_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v___x_985_, 1);
lean_dec(v_unused_1048_);
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1047_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_toApplicative_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1047_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_toFunctor_990_; lean_object* v_toSeq_991_; lean_object* v_toSeqLeft_992_; lean_object* v_toSeqRight_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1045_; 
v_toFunctor_990_ = lean_ctor_get(v_toApplicative_986_, 0);
v_toSeq_991_ = lean_ctor_get(v_toApplicative_986_, 2);
v_toSeqLeft_992_ = lean_ctor_get(v_toApplicative_986_, 3);
v_toSeqRight_993_ = lean_ctor_get(v_toApplicative_986_, 4);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_toApplicative_986_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v_toApplicative_986_, 1);
lean_dec(v_unused_1046_);
v___x_995_ = v_toApplicative_986_;
v_isShared_996_ = v_isSharedCheck_1045_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_toSeqRight_993_);
lean_inc(v_toSeqLeft_992_);
lean_inc(v_toSeq_991_);
lean_inc(v_toFunctor_990_);
lean_dec(v_toApplicative_986_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1045_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___x_1006_; 
v___f_997_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__1));
v___f_998_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_990_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_999_, 0, v_toFunctor_990_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toFunctor_990_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___f_999_);
lean_ctor_set(v___x_1001_, 1, v___f_1000_);
v___f_1002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1002_, 0, v_toSeqRight_993_);
v___f_1003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1003_, 0, v_toSeqLeft_992_);
v___f_1004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1004_, 0, v_toSeq_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___f_1002_);
lean_ctor_set(v___x_995_, 3, v___f_1003_);
lean_ctor_set(v___x_995_, 2, v___f_1004_);
lean_ctor_set(v___x_995_, 1, v___f_997_);
lean_ctor_set(v___x_995_, 0, v___x_1001_);
v___x_1006_ = v___x_995_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___f_997_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v___f_1004_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v___f_1003_);
lean_ctor_set(v_reuseFailAlloc_1044_, 4, v___f_1002_);
v___x_1006_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___f_998_);
lean_ctor_set(v___x_988_, 0, v___x_1006_);
v___x_1008_ = v___x_988_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___f_998_);
v___x_1008_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v_toApplicative_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1041_; 
v___x_1009_ = l_StateRefT_x27_instMonad___redArg(v___x_1008_);
v_toApplicative_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v___x_1009_, 1);
lean_dec(v_unused_1042_);
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1041_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_toApplicative_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1041_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_toFunctor_1014_; lean_object* v_toSeq_1015_; lean_object* v_toSeqLeft_1016_; lean_object* v_toSeqRight_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1039_; 
v_toFunctor_1014_ = lean_ctor_get(v_toApplicative_1010_, 0);
v_toSeq_1015_ = lean_ctor_get(v_toApplicative_1010_, 2);
v_toSeqLeft_1016_ = lean_ctor_get(v_toApplicative_1010_, 3);
v_toSeqRight_1017_ = lean_ctor_get(v_toApplicative_1010_, 4);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_toApplicative_1010_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v_toApplicative_1010_, 1);
lean_dec(v_unused_1040_);
v___x_1019_ = v_toApplicative_1010_;
v_isShared_1020_ = v_isSharedCheck_1039_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_toSeqRight_1017_);
lean_inc(v_toSeqLeft_1016_);
lean_inc(v_toSeq_1015_);
lean_inc(v_toFunctor_1014_);
lean_dec(v_toApplicative_1010_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1039_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___x_1030_; 
v___f_1021_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__3));
v___f_1022_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1014_);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toFunctor_1014_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toFunctor_1014_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___f_1023_);
lean_ctor_set(v___x_1025_, 1, v___f_1024_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toSeqRight_1017_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toSeqLeft_1016_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toSeq_1015_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 4, v___f_1026_);
lean_ctor_set(v___x_1019_, 3, v___f_1027_);
lean_ctor_set(v___x_1019_, 2, v___f_1028_);
lean_ctor_set(v___x_1019_, 1, v___f_1021_);
lean_ctor_set(v___x_1019_, 0, v___x_1025_);
v___x_1030_ = v___x_1019_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___f_1021_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v___f_1028_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v___f_1027_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___f_1026_);
v___x_1030_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 1, v___f_1022_);
lean_ctor_set(v___x_1012_, 0, v___x_1030_);
v___x_1032_ = v___x_1012_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___f_1022_);
v___x_1032_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_17792__overap_1035_; lean_object* v___x_1036_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = l_instInhabitedOfMonad___redArg(v___x_1032_, v___x_1033_);
v___x_17792__overap_1035_ = lean_panic_fn_borrowed(v___x_1034_, v_msg_978_);
lean_dec(v___x_1034_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
v___x_1036_ = lean_apply_5(v___x_17792__overap_1035_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
return v___x_1036_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0___boxed(lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__0));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__2));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1065_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__6));
v___x_1066_ = lean_unsigned_to_nat(11u);
v___x_1067_ = lean_unsigned_to_nat(115u);
v___x_1068_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__5));
v___x_1069_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__4));
v___x_1070_ = l_mkPanicMessageWithDecl(v___x_1069_, v___x_1068_, v___x_1067_, v___x_1066_, v___x_1065_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(lean_object* v_constName_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1085_; lean_object* v_env_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = lean_st_ref_get(v___y_1075_);
v_env_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_env_1086_);
lean_dec(v___x_1085_);
v___x_1087_ = 0;
lean_inc(v_constName_1071_);
v___x_1088_ = l_Lean_Environment_findAsync_x3f(v_env_1086_, v_constName_1071_, v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 1)
{
lean_object* v_val_1089_; uint8_t v_kind_1090_; 
v_val_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_val_1089_);
lean_dec_ref(v___x_1088_);
v_kind_1090_ = lean_ctor_get_uint8(v_val_1089_, sizeof(void*)*3);
if (v_kind_1090_ == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1089_);
if (lean_obj_tag(v___x_1091_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_constName_1071_);
v_val_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 0);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_val_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec_ref(v___x_1091_);
v___x_1100_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__7);
v___x_1101_ = l_panic___at___00Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0_spec__0(v___x_1100_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
if (lean_obj_tag(v_a_1102_) == 0)
{
lean_del_object(v___x_1104_);
goto v___jp_1077_;
}
else
{
lean_object* v_val_1106_; lean_object* v___x_1108_; 
lean_dec(v_constName_1071_);
v_val_1106_ = lean_ctor_get(v_a_1102_, 0);
lean_inc(v_val_1106_);
lean_dec_ref(v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_val_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_val_1106_);
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
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_constName_1071_);
v_a_1111_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1101_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1101_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_dec(v_val_1089_);
goto v___jp_1077_;
}
}
else
{
lean_dec(v___x_1088_);
goto v___jp_1077_;
}
v___jp_1077_:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1078_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
v___x_1079_ = 0;
v___x_1080_ = l_Lean_MessageData_ofConstName(v_constName_1071_, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1078_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__3);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_1083_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___boxed(lean_object* v_constName_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_constName_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__1));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__3));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__5));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__7));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(lean_object* v_instName_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
lean_inc(v_instName_1139_);
v___x_1145_ = l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0(v_instName_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v_toConstantVal_1147_; lean_object* v_value_1148_; lean_object* v_name_1149_; lean_object* v_levelParams_1150_; lean_object* v_type_1151_; lean_object* v___x_1152_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_1145_);
v_toConstantVal_1147_ = lean_ctor_get(v_a_1146_, 0);
lean_inc_ref(v_toConstantVal_1147_);
v_value_1148_ = lean_ctor_get(v_a_1146_, 1);
lean_inc_ref(v_value_1148_);
lean_dec(v_a_1146_);
v_name_1149_ = lean_ctor_get(v_toConstantVal_1147_, 0);
lean_inc(v_name_1149_);
v_levelParams_1150_ = lean_ctor_get(v_toConstantVal_1147_, 1);
lean_inc(v_levelParams_1150_);
v_type_1151_ = lean_ctor_get(v_toConstantVal_1147_, 2);
lean_inc_ref_n(v_type_1151_, 2);
lean_dec_ref(v_toConstantVal_1147_);
v___x_1152_ = l_Lean_Meta_isClass_x3f(v_type_1151_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___x_1152_);
if (lean_obj_tag(v_a_1153_) == 1)
{
lean_object* v_val_1154_; lean_object* v___f_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
v_val_1154_ = lean_ctor_get(v_a_1153_, 0);
lean_inc(v_val_1154_);
lean_dec_ref(v_a_1153_);
v___f_1155_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__0));
v___x_1156_ = 0;
lean_inc_ref(v_type_1151_);
v___x_1157_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__1___redArg(v_type_1151_, v___f_1155_, v___x_1156_, v___x_1156_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; lean_object* v_env_1160_; lean_object* v___x_1161_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref(v___x_1157_);
v___x_1159_ = lean_st_ref_get(v_a_1143_);
v_env_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc_ref(v_env_1160_);
lean_dec(v___x_1159_);
lean_inc(v_val_1154_);
v___x_1161_ = l_Lean_getStructureInfo_x3f(v_env_1160_, v_val_1154_);
if (lean_obj_tag(v___x_1161_) == 1)
{
lean_object* v_val_1162_; lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v___x_1161_);
v___x_1163_ = lean_box(v___x_1156_);
v___f_1164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1164_, 0, v_type_1151_);
lean_closure_set(v___f_1164_, 1, v_val_1154_);
lean_closure_set(v___f_1164_, 2, v_levelParams_1150_);
lean_closure_set(v___f_1164_, 3, v_name_1149_);
lean_closure_set(v___f_1164_, 4, v_val_1162_);
lean_closure_set(v___f_1164_, 5, v___x_1163_);
lean_closure_set(v___f_1164_, 6, v_instName_1139_);
lean_closure_set(v___f_1164_, 7, v_a_1158_);
v___x_1165_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__12___redArg(v_value_1148_, v___f_1164_, v___x_1156_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v___x_1161_);
lean_dec(v_a_1158_);
lean_dec_ref(v_type_1151_);
lean_dec(v_levelParams_1150_);
lean_dec(v_name_1149_);
lean_dec_ref(v_value_1148_);
lean_dec(v_instName_1139_);
v___x_1166_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
v___x_1167_ = l_Lean_MessageData_ofConstName(v_val_1154_, v___x_1156_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__2);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_1170_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1171_;
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_val_1154_);
lean_dec_ref(v_type_1151_);
lean_dec(v_levelParams_1150_);
lean_dec(v_name_1149_);
lean_dec_ref(v_value_1148_);
lean_dec(v_instName_1139_);
v_a_1172_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1157_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1157_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec(v_a_1153_);
lean_dec(v_levelParams_1150_);
lean_dec(v_name_1149_);
lean_dec_ref(v_value_1148_);
v___x_1180_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__4);
v___x_1181_ = 0;
v___x_1182_ = l_Lean_MessageData_ofConstName(v_instName_1139_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1180_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__6);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_unsigned_to_nat(30u);
v___x_1187_ = l_Lean_inlineExpr(v_type_1151_, v___x_1186_);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1185_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___closed__8);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_1190_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
return v___x_1191_;
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_type_1151_);
lean_dec(v_levelParams_1150_);
lean_dec(v_name_1149_);
lean_dec_ref(v_value_1148_);
lean_dec(v_instName_1139_);
v_a_1192_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1152_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1152_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_instName_1139_);
v_a_1200_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1145_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1145_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___boxed(lean_object* v_instName_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(lean_object* v_00_u03b1_1215_, lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___boxed(lean_object* v_00_u03b1_1223_, lean_object* v_msg_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3(v_00_u03b1_1223_, v_msg_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(lean_object* v_xs_1231_, lean_object* v_ys_1232_, lean_object* v_hsz_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_){
_start:
{
uint8_t v___x_1236_; 
v___x_1236_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___redArg(v_xs_1231_, v_ys_1232_, v_x_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4___boxed(lean_object* v_xs_1237_, lean_object* v_ys_1238_, lean_object* v_hsz_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Array_isEqvAux___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__4(v_xs_1237_, v_ys_1238_, v_hsz_1239_, v_x_1240_, v_x_1241_);
lean_dec_ref(v_ys_1238_);
lean_dec_ref(v_xs_1237_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
static uint64_t _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1(void){
_start:
{
lean_object* v___x_1255_; uint64_t v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0));
v___x_1256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2(void){
_start:
{
uint64_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_uint64_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__1);
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__0));
v___x_1259_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set_uint64(v___x_1259_, sizeof(void*)*1, v___x_1257_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3(void){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__3);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_unsigned_to_nat(32u);
v___x_1264_ = lean_mk_empty_array_with_capacity(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6(void){
_start:
{
size_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1266_ = ((size_t)5ULL);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_unsigned_to_nat(32u);
v___x_1269_ = lean_mk_empty_array_with_capacity(v___x_1268_);
v___x_1270_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__5);
v___x_1271_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1269_);
lean_ctor_set(v___x_1271_, 2, v___x_1267_);
lean_ctor_set(v___x_1271_, 3, v___x_1267_);
lean_ctor_set_usize(v___x_1271_, 4, v___x_1266_);
return v___x_1271_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = lean_box(1);
v___x_1273_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_1274_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1272_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9(void){
_start:
{
uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1278_ = 1;
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_box(0);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8));
v___x_1282_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7);
v___x_1283_ = lean_box(1);
v___x_1284_ = 0;
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2);
v___x_1286_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___x_1283_);
lean_ctor_set(v___x_1286_, 2, v___x_1282_);
lean_ctor_set(v___x_1286_, 3, v___x_1281_);
lean_ctor_set(v___x_1286_, 4, v___x_1280_);
lean_ctor_set(v___x_1286_, 5, v___x_1279_);
lean_ctor_set(v___x_1286_, 6, v___x_1280_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*7, v___x_1284_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*7 + 1, v___x_1284_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*7 + 2, v___x_1284_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*7 + 3, v___x_1278_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
lean_ctor_set(v___x_1289_, 2, v___x_1288_);
lean_ctor_set(v___x_1289_, 3, v___x_1287_);
lean_ctor_set(v___x_1289_, 4, v___x_1287_);
lean_ctor_set(v___x_1289_, 5, v___x_1287_);
lean_ctor_set(v___x_1289_, 6, v___x_1287_);
lean_ctor_set(v___x_1289_, 7, v___x_1287_);
lean_ctor_set(v___x_1289_, 8, v___x_1287_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_ctor_set(v___x_1291_, 2, v___x_1290_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
lean_ctor_set(v___x_1291_, 4, v___x_1290_);
lean_ctor_set(v___x_1291_, 5, v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__4);
v___x_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
lean_ctor_set(v___x_1293_, 3, v___x_1292_);
lean_ctor_set(v___x_1293_, 4, v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1294_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12);
v___x_1295_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_1296_ = lean_box(1);
v___x_1297_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11);
v___x_1298_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10);
v___x_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
lean_ctor_set(v___x_1299_, 2, v___x_1296_);
lean_ctor_set(v___x_1299_, 3, v___x_1295_);
lean_ctor_set(v___x_1299_, 4, v___x_1294_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(lean_object* v_instName_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_a_1305_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__9);
v___x_1311_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__13);
v___x_1312_ = lean_st_mk_ref(v___x_1311_);
v___x_1313_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_1300_, v___x_1310_, v___x_1312_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_st_ref_get(v___x_1312_);
lean_dec(v___x_1312_);
lean_dec(v___x_1315_);
v_a_1305_ = v_a_1314_;
goto v___jp_1304_;
}
else
{
lean_dec(v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1316_; 
v_a_1316_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1313_);
v_a_1305_ = v_a_1316_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_a_1317_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1313_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1313_);
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
v___jp_1304_:
{
lean_object* v_clsName_1306_; uint8_t v_privateSpecs_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_clsName_1306_ = lean_ctor_get(v_a_1305_, 0);
lean_inc(v_clsName_1306_);
v_privateSpecs_1307_ = lean_ctor_get_uint8(v_a_1305_, sizeof(void*)*3);
lean_dec_ref(v_a_1305_);
v___x_1308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1308_, 0, v_clsName_1306_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*1, v_privateSpecs_1307_);
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___boxed(lean_object* v_instName_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(v_instName_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(lean_object* v_instName_1330_, lean_object* v___stx_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg(v_instName_1330_, v_a_1332_, v_a_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___boxed(lean_object* v_instName_1336_, lean_object* v___stx_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getParam(v_instName_1336_, v___stx_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v___stx_1337_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v_x_1349_, v_x_1350_, v_x_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v_x_1351_);
lean_dec_ref(v_x_1350_);
lean_dec(v_x_1349_);
return v_res_1354_;
}
}
LEAN_EXPORT uint8_t l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(uint8_t v___x_1355_, lean_object* v_env_1356_, lean_object* v_n_1357_, lean_object* v_x_1358_){
_start:
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Environment_contains(v_env_1356_, v_n_1357_, v___x_1355_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object* v___x_1360_, lean_object* v_env_1361_, lean_object* v_n_1362_, lean_object* v_x_1363_){
_start:
{
uint8_t v___x_98__boxed_1364_; uint8_t v_res_1365_; lean_object* v_r_1366_; 
v___x_98__boxed_1364_ = lean_unbox(v___x_1360_);
v_res_1365_ = l_Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(v___x_98__boxed_1364_, v_env_1361_, v_n_1362_, v_x_1363_);
lean_dec_ref(v_x_1363_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_));
v___x_1394_ = l_Lean_registerParametricAttribute___redArg(v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2____boxed(lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2332742545____hygCtx___hyg_2_();
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1(){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__7));
v___x_1422_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___closed__8));
v___x_1423_ = l_Lean_addBuiltinDocString(v___x_1421_, v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1___boxed(lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr___regBuiltin___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr_docString__1();
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_));
v___x_1436_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_));
v___x_1437_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_));
v___x_1438_ = l_Lean_Meta_registerSimpAttr(v___x_1435_, v___x_1436_, v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2____boxed(lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2970555752____hygCtx___hyg_2_();
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(lean_object* v_env_1441_, lean_object* v_instName_1442_, uint8_t v_privateSpecs_1443_, lean_object* v_suffix_1444_){
_start:
{
lean_object* v_thmName_1445_; 
v_thmName_1445_ = l_Lean_Name_str___override(v_instName_1442_, v_suffix_1444_);
if (v_privateSpecs_1443_ == 0)
{
return v_thmName_1445_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_mkPrivateName(v_env_1441_, v_thmName_1445_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName___boxed(lean_object* v_env_1447_, lean_object* v_instName_1448_, lean_object* v_privateSpecs_1449_, lean_object* v_suffix_1450_){
_start:
{
uint8_t v_privateSpecs_boxed_1451_; lean_object* v_res_1452_; 
v_privateSpecs_boxed_1451_ = lean_unbox(v_privateSpecs_1449_);
v_res_1452_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_1447_, v_instName_1448_, v_privateSpecs_boxed_1451_, v_suffix_1450_);
lean_dec_ref(v_env_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(lean_object* v_s_1453_, lean_object* v_p_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = lean_string_utf8_byte_size(v_s_1453_);
v___x_1456_ = lean_string_utf8_byte_size(v_p_1454_);
v___x_1457_ = lean_nat_dec_le(v___x_1456_, v___x_1455_);
if (v___x_1457_ == 0)
{
lean_dec_ref(v_s_1453_);
return v___x_1457_;
}
else
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_string_memcmp(v_s_1453_, v_p_1454_, v___x_1458_, v___x_1458_, v___x_1456_);
if (v___x_1459_ == 0)
{
lean_dec_ref(v_s_1453_);
return v___x_1459_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1460_ = lean_string_length(v_p_1454_);
lean_inc_ref(v_s_1453_);
v___x_1461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1461_, 0, v_s_1453_);
lean_ctor_set(v___x_1461_, 1, v___x_1458_);
lean_ctor_set(v___x_1461_, 2, v___x_1455_);
v___x_1462_ = l_String_Slice_Pos_nextn(v___x_1461_, v___x_1458_, v___x_1460_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1463_, 0, v_s_1453_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_ctor_set(v___x_1463_, 2, v___x_1455_);
v___x_1464_ = l_String_Slice_isNat(v___x_1463_);
lean_dec_ref(v___x_1463_);
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber___boxed(lean_object* v_s_1465_, lean_object* v_p_1466_){
_start:
{
uint8_t v_res_1467_; lean_object* v_r_1468_; 
v_res_1467_ = l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(v_s_1465_, v_p_1466_);
lean_dec_ref(v_p_1466_);
v_r_1468_ = lean_box(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(lean_object* v_fieldName_1471_, lean_object* v_s_1472_){
_start:
{
uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1473_ = 1;
v___x_1474_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_1471_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
lean_inc_ref(v___x_1474_);
v___x_1476_ = lean_string_append(v___x_1474_, v___x_1475_);
v___x_1477_ = lean_string_dec_eq(v_s_1472_, v___x_1476_);
lean_dec_ref(v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1));
v___x_1479_ = lean_string_append(v___x_1474_, v___x_1478_);
v___x_1480_ = l___private_Lean_Meta_MethodSpecs_0__Lean_startsWithFollowedByNumber(v_s_1472_, v___x_1479_);
lean_dec_ref(v___x_1479_);
return v___x_1480_;
}
else
{
lean_dec_ref(v___x_1474_);
lean_dec_ref(v_s_1472_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___boxed(lean_object* v_fieldName_1481_, lean_object* v_s_1482_){
_start:
{
uint8_t v_res_1483_; lean_object* v_r_1484_; 
v_res_1483_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(v_fieldName_1481_, v_s_1482_);
v_r_1484_ = lean_box(v_res_1483_);
return v_r_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(lean_object* v_str_1488_, lean_object* v_val_1489_, lean_object* v_env_1490_, lean_object* v_p_1491_, lean_object* v_name_1492_, lean_object* v_as_1493_, size_t v_sz_1494_, size_t v_i_1495_, lean_object* v_b_1496_){
_start:
{
lean_object* v_a_1498_; uint8_t v___x_1502_; 
v___x_1502_ = lean_usize_dec_lt(v_i_1495_, v_sz_1494_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
lean_dec(v_p_1491_);
lean_dec_ref(v_str_1488_);
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_b_1496_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_a_1506_; uint8_t v___x_1507_; 
lean_dec_ref(v_b_1496_);
v___x_1504_ = lean_box(0);
v___x_1505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0));
v_a_1506_ = lean_array_uget_borrowed(v_as_1493_, v_i_1495_);
lean_inc_ref(v_str_1488_);
lean_inc(v_a_1506_);
v___x_1507_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix(v_a_1506_, v_str_1488_);
if (v___x_1507_ == 0)
{
v_a_1498_ = v___x_1505_;
goto v___jp_1497_;
}
else
{
uint8_t v_privateSpecs_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_privateSpecs_1508_ = lean_ctor_get_uint8(v_val_1489_, sizeof(void*)*1);
lean_inc_ref(v_str_1488_);
lean_inc(v_p_1491_);
v___x_1509_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_1490_, v_p_1491_, v_privateSpecs_1508_, v_str_1488_);
v___x_1510_ = lean_name_eq(v_name_1492_, v___x_1509_);
lean_dec(v___x_1509_);
if (v___x_1510_ == 0)
{
v_a_1498_ = v___x_1505_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_dec_ref(v_str_1488_);
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_p_1491_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1504_);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
v___jp_1497_:
{
size_t v___x_1499_; size_t v___x_1500_; 
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_add(v_i_1495_, v___x_1499_);
lean_inc_ref(v_a_1498_);
v_i_1495_ = v___x_1500_;
v_b_1496_ = v_a_1498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___boxed(lean_object* v_str_1514_, lean_object* v_val_1515_, lean_object* v_env_1516_, lean_object* v_p_1517_, lean_object* v_name_1518_, lean_object* v_as_1519_, lean_object* v_sz_1520_, lean_object* v_i_1521_, lean_object* v_b_1522_){
_start:
{
size_t v_sz_boxed_1523_; size_t v_i_boxed_1524_; lean_object* v_res_1525_; 
v_sz_boxed_1523_ = lean_unbox_usize(v_sz_1520_);
lean_dec(v_sz_1520_);
v_i_boxed_1524_ = lean_unbox_usize(v_i_1521_);
lean_dec(v_i_1521_);
v_res_1525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_1514_, v_val_1515_, v_env_1516_, v_p_1517_, v_name_1518_, v_as_1519_, v_sz_boxed_1523_, v_i_boxed_1524_, v_b_1522_);
lean_dec_ref(v_as_1519_);
lean_dec(v_name_1518_);
lean_dec_ref(v_env_1516_);
lean_dec_ref(v_val_1515_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(lean_object* v_env_1526_, lean_object* v_str_1527_, lean_object* v_name_1528_, lean_object* v_x_1529_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_object* v___x_1530_; 
lean_dec_ref(v_str_1527_);
lean_dec_ref(v_env_1526_);
v___x_1530_ = lean_box(0);
return v___x_1530_;
}
else
{
lean_object* v_head_1531_; lean_object* v_tail_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_head_1531_ = lean_ctor_get(v_x_1529_, 0);
lean_inc_n(v_head_1531_, 2);
v_tail_1532_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_tail_1532_);
lean_dec_ref(v_x_1529_);
v___x_1533_ = ((lean_object*)(l_Lean_instInhabitedMethodSpecsAttrData_default));
v___x_1534_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
lean_inc_ref(v_env_1526_);
v___x_1535_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1533_, v___x_1534_, v_env_1526_, v_head_1531_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_dec(v_head_1531_);
v_x_1529_ = v_tail_1532_;
goto _start;
}
else
{
lean_object* v_val_1537_; lean_object* v_clsName_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; size_t v_sz_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v_val_1537_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1537_);
lean_dec_ref(v___x_1535_);
v_clsName_1538_ = lean_ctor_get(v_val_1537_, 0);
lean_inc(v_clsName_1538_);
lean_inc_ref(v_env_1526_);
v___x_1539_ = l_Lean_getStructureFields(v_env_1526_, v_clsName_1538_);
v___x_1540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0___closed__0));
v_sz_1541_ = lean_array_size(v___x_1539_);
v___x_1542_ = ((size_t)0ULL);
lean_inc_ref(v_str_1527_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__0(v_str_1527_, v_val_1537_, v_env_1526_, v_head_1531_, v_name_1528_, v___x_1539_, v_sz_1541_, v___x_1542_, v___x_1540_);
lean_dec_ref(v___x_1539_);
lean_dec(v_val_1537_);
if (lean_obj_tag(v___x_1543_) == 0)
{
v_x_1529_ = v_tail_1532_;
goto _start;
}
else
{
lean_object* v_val_1545_; lean_object* v_fst_1546_; 
v_val_1545_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_val_1545_);
lean_dec_ref(v___x_1543_);
v_fst_1546_ = lean_ctor_get(v_val_1545_, 0);
lean_inc(v_fst_1546_);
lean_dec(v_val_1545_);
if (lean_obj_tag(v_fst_1546_) == 0)
{
v_x_1529_ = v_tail_1532_;
goto _start;
}
else
{
lean_dec(v_tail_1532_);
lean_dec_ref(v_str_1527_);
lean_dec_ref(v_env_1526_);
return v_fst_1546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1___boxed(lean_object* v_env_1548_, lean_object* v_str_1549_, lean_object* v_name_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(v_env_1548_, v_str_1549_, v_name_1550_, v_x_1551_);
lean_dec(v_name_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(lean_object* v_env_1553_, lean_object* v_name_1554_){
_start:
{
if (lean_obj_tag(v_name_1554_) == 1)
{
lean_object* v_pre_1555_; lean_object* v_str_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_pre_1555_ = lean_ctor_get(v_name_1554_, 0);
v_str_1556_ = lean_ctor_get(v_name_1554_, 1);
lean_inc_ref(v_str_1556_);
lean_inc_n(v_pre_1555_, 2);
v___x_1557_ = l_Lean_privateToUserName(v_pre_1555_);
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_pre_1555_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = l_List_firstM___at___00__private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor_spec__1(v_env_1553_, v_str_1556_, v_name_1554_, v___x_1560_);
lean_dec_ref(v_name_1554_);
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; 
lean_dec(v_name_1554_);
lean_dec_ref(v_env_1553_);
v___x_1562_ = lean_box(0);
return v___x_1562_;
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_ctor_set(v___x_1568_, 2, v___x_1567_);
lean_ctor_set(v___x_1568_, 3, v___x_1566_);
lean_ctor_set(v___x_1568_, 4, v___x_1566_);
lean_ctor_set(v___x_1568_, 5, v___x_1566_);
lean_ctor_set(v___x_1568_, 6, v___x_1566_);
lean_ctor_set(v___x_1568_, 7, v___x_1566_);
lean_ctor_set(v___x_1568_, 8, v___x_1566_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_box(1);
v___x_1570_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_1571_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1570_);
lean_ctor_set(v___x_1572_, 2, v___x_1569_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4));
v___x_1575_ = l_Lean_stringToMessageData(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1578_ = l_Lean_stringToMessageData(v___x_1577_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1587_ = l_Lean_stringToMessageData(v___x_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1594_, lean_object* v_declHint_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; lean_object* v_env_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_st_ref_get(v___y_1596_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1600_ = l_Lean_Name_isAnonymous(v_declHint_1595_);
if (v___x_1600_ == 0)
{
uint8_t v_isExporting_1601_; 
v_isExporting_1601_ = lean_ctor_get_uint8(v_env_1599_, sizeof(void*)*8);
if (v_isExporting_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1595_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_msg_1594_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
lean_inc_ref(v_env_1599_);
v___x_1603_ = l_Lean_Environment_setExporting(v_env_1599_, v___x_1600_);
lean_inc(v_declHint_1595_);
lean_inc_ref(v___x_1603_);
v___x_1604_ = l_Lean_Environment_contains(v___x_1603_, v_declHint_1595_, v_isExporting_1601_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref(v___x_1603_);
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1595_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_msg_1594_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_c_1611_; lean_object* v___x_1612_; 
v___x_1606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1608_ = l_Lean_Options_empty;
v___x_1609_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1603_);
lean_ctor_set(v___x_1609_, 1, v___x_1606_);
lean_ctor_set(v___x_1609_, 2, v___x_1607_);
lean_ctor_set(v___x_1609_, 3, v___x_1608_);
lean_inc(v_declHint_1595_);
v___x_1610_ = l_Lean_MessageData_ofConstName(v_declHint_1595_, v___x_1600_);
v_c_1611_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1611_, 0, v___x_1609_);
lean_ctor_set(v_c_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1599_, v_declHint_1595_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1595_);
v___x_1613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v_c_1611_);
v___x_1615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_MessageData_note(v___x_1616_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_msg_1594_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1655_; 
v_val_1620_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1622_ = v___x_1612_;
v_isShared_1623_ = v_isSharedCheck_1655_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_val_1620_);
lean_dec(v___x_1612_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1655_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_mod_1627_; uint8_t v___x_1628_; 
v___x_1624_ = lean_box(0);
v___x_1625_ = l_Lean_Environment_header(v_env_1599_);
lean_dec_ref(v_env_1599_);
v___x_1626_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1625_);
v_mod_1627_ = lean_array_get(v___x_1624_, v___x_1626_, v_val_1620_);
lean_dec(v_val_1620_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = l_Lean_isPrivateName(v_declHint_1595_);
lean_dec(v_declHint_1595_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1629_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_c_1611_);
v___x_1631_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_MessageData_ofName(v_mod_1627_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_MessageData_note(v___x_1636_);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_msg_1594_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1638_);
v___x_1640_ = v___x_1622_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_c_1611_);
v___x_1644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_MessageData_ofName(v_mod_1627_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_MessageData_note(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v_msg_1594_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1651_);
v___x_1653_ = v___x_1622_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1656_; 
lean_dec_ref(v_env_1599_);
lean_dec(v_declHint_1595_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_msg_1594_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1657_, lean_object* v_declHint_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1657_, v_declHint_1658_, v___y_1659_);
lean_dec(v___y_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1662_, lean_object* v_declHint_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1679_; 
v___x_1669_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1662_, v_declHint_1663_, v___y_1667_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1679_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1674_ = l_Lean_unknownIdentifierMessageTag;
v___x_1675_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_a_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1680_, lean_object* v_declHint_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1680_, v_declHint_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1688_, lean_object* v_msg_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_fileName_1695_; lean_object* v_fileMap_1696_; lean_object* v_options_1697_; lean_object* v_currRecDepth_1698_; lean_object* v_maxRecDepth_1699_; lean_object* v_ref_1700_; lean_object* v_currNamespace_1701_; lean_object* v_openDecls_1702_; lean_object* v_initHeartbeats_1703_; lean_object* v_maxHeartbeats_1704_; lean_object* v_quotContext_1705_; lean_object* v_currMacroScope_1706_; uint8_t v_diag_1707_; lean_object* v_cancelTk_x3f_1708_; uint8_t v_suppressElabErrors_1709_; lean_object* v_inheritedTraceOptions_1710_; lean_object* v_ref_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_fileName_1695_ = lean_ctor_get(v___y_1692_, 0);
v_fileMap_1696_ = lean_ctor_get(v___y_1692_, 1);
v_options_1697_ = lean_ctor_get(v___y_1692_, 2);
v_currRecDepth_1698_ = lean_ctor_get(v___y_1692_, 3);
v_maxRecDepth_1699_ = lean_ctor_get(v___y_1692_, 4);
v_ref_1700_ = lean_ctor_get(v___y_1692_, 5);
v_currNamespace_1701_ = lean_ctor_get(v___y_1692_, 6);
v_openDecls_1702_ = lean_ctor_get(v___y_1692_, 7);
v_initHeartbeats_1703_ = lean_ctor_get(v___y_1692_, 8);
v_maxHeartbeats_1704_ = lean_ctor_get(v___y_1692_, 9);
v_quotContext_1705_ = lean_ctor_get(v___y_1692_, 10);
v_currMacroScope_1706_ = lean_ctor_get(v___y_1692_, 11);
v_diag_1707_ = lean_ctor_get_uint8(v___y_1692_, sizeof(void*)*14);
v_cancelTk_x3f_1708_ = lean_ctor_get(v___y_1692_, 12);
v_suppressElabErrors_1709_ = lean_ctor_get_uint8(v___y_1692_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1710_ = lean_ctor_get(v___y_1692_, 13);
v_ref_1711_ = l_Lean_replaceRef(v_ref_1688_, v_ref_1700_);
lean_inc_ref(v_inheritedTraceOptions_1710_);
lean_inc(v_cancelTk_x3f_1708_);
lean_inc(v_currMacroScope_1706_);
lean_inc(v_quotContext_1705_);
lean_inc(v_maxHeartbeats_1704_);
lean_inc(v_initHeartbeats_1703_);
lean_inc(v_openDecls_1702_);
lean_inc(v_currNamespace_1701_);
lean_inc(v_maxRecDepth_1699_);
lean_inc(v_currRecDepth_1698_);
lean_inc_ref(v_options_1697_);
lean_inc_ref(v_fileMap_1696_);
lean_inc_ref(v_fileName_1695_);
v___x_1712_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1712_, 0, v_fileName_1695_);
lean_ctor_set(v___x_1712_, 1, v_fileMap_1696_);
lean_ctor_set(v___x_1712_, 2, v_options_1697_);
lean_ctor_set(v___x_1712_, 3, v_currRecDepth_1698_);
lean_ctor_set(v___x_1712_, 4, v_maxRecDepth_1699_);
lean_ctor_set(v___x_1712_, 5, v_ref_1711_);
lean_ctor_set(v___x_1712_, 6, v_currNamespace_1701_);
lean_ctor_set(v___x_1712_, 7, v_openDecls_1702_);
lean_ctor_set(v___x_1712_, 8, v_initHeartbeats_1703_);
lean_ctor_set(v___x_1712_, 9, v_maxHeartbeats_1704_);
lean_ctor_set(v___x_1712_, 10, v_quotContext_1705_);
lean_ctor_set(v___x_1712_, 11, v_currMacroScope_1706_);
lean_ctor_set(v___x_1712_, 12, v_cancelTk_x3f_1708_);
lean_ctor_set(v___x_1712_, 13, v_inheritedTraceOptions_1710_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*14, v_diag_1707_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*14 + 1, v_suppressElabErrors_1709_);
v___x_1713_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v_msg_1689_, v___y_1690_, v___y_1691_, v___x_1712_, v___y_1693_);
lean_dec_ref(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1714_, lean_object* v_msg_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1714_, v_msg_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v_ref_1714_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1722_, lean_object* v_msg_1723_, lean_object* v_declHint_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v_a_1731_; lean_object* v___x_1732_; 
v___x_1730_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1723_, v_declHint_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1722_, v_a_1731_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1733_, lean_object* v_msg_1734_, lean_object* v_declHint_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1733_, v_msg_1734_, v_declHint_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_ref_1733_);
return v_res_1741_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1744_ = l_Lean_stringToMessageData(v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1745_, lean_object* v_constName_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1752_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1753_ = 0;
lean_inc(v_constName_1746_);
v___x_1754_ = l_Lean_MessageData_ofConstName(v_constName_1746_, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1752_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__0___closed__1);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1745_, v___x_1757_, v_constName_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1759_, lean_object* v_constName_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_1759_, v_constName_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v_ref_1759_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(lean_object* v_constName_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_ref_1773_; lean_object* v___x_1774_; 
v_ref_1773_ = lean_ctor_get(v___y_1770_, 5);
v___x_1774_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_1773_, v_constName_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(lean_object* v_constName_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; lean_object* v_env_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1788_ = lean_st_ref_get(v___y_1786_);
v_env_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc_ref(v_env_1789_);
lean_dec(v___x_1788_);
v___x_1790_ = 0;
lean_inc(v_constName_1782_);
v___x_1791_ = l_Lean_Environment_findConstVal_x3f(v_env_1789_, v_constName_1782_, v___x_1790_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1792_;
}
else
{
lean_object* v_val_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_constName_1782_);
v_val_1793_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1791_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_val_1793_);
lean_dec(v___x_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 0);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_val_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0___boxed(lean_object* v_constName_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(v_constName_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0(void){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__0);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
return v___x_1813_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(32u);
v___x_1815_ = lean_mk_empty_array_with_capacity(v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4(void){
_start:
{
size_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1817_ = ((size_t)5ULL);
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_unsigned_to_nat(32u);
v___x_1820_ = lean_mk_empty_array_with_capacity(v___x_1819_);
v___x_1821_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__3);
v___x_1822_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v___x_1820_);
lean_ctor_set(v___x_1822_, 2, v___x_1818_);
lean_ctor_set(v___x_1822_, 3, v___x_1818_);
lean_ctor_set_usize(v___x_1822_, 4, v___x_1817_);
return v___x_1822_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__4);
v___x_1824_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__1);
v___x_1825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
lean_ctor_set(v___x_1825_, 2, v___x_1824_);
lean_ctor_set(v___x_1825_, 3, v___x_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__5);
v___x_1827_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__2);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = l_Lean_Level_ofNat(v___x_1834_);
return v___x_1835_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__10);
v___x_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1836_);
return v___x_1838_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__11);
v___x_1840_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__9));
v___x_1841_ = l_Lean_mkConst(v___x_1840_, v___x_1839_);
return v___x_1841_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__13));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__15));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(lean_object* v_ctx_1848_, lean_object* v_simprocs_1849_, lean_object* v_eqThmName_1850_, lean_object* v_destThmName_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1857_; 
lean_inc(v_eqThmName_1850_);
v___x_1857_ = l_Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0(v_eqThmName_1850_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_levelParams_1859_; lean_object* v_type_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1937_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1857_);
v_levelParams_1859_ = lean_ctor_get(v_a_1858_, 1);
v_type_1860_ = lean_ctor_get(v_a_1858_, 2);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_a_1858_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_a_1858_, 0);
lean_dec(v_unused_1938_);
v___x_1862_ = v_a_1858_;
v_isShared_1863_ = v_isSharedCheck_1937_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_type_1860_);
lean_inc(v_levelParams_1859_);
lean_dec(v_a_1858_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1937_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = lean_unsigned_to_nat(1u);
v___x_1865_ = lean_mk_empty_array_with_capacity(v___x_1864_);
v___x_1866_ = lean_array_push(v___x_1865_, v_simprocs_1849_);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__6);
lean_inc_ref(v_type_1860_);
v___x_1869_ = l_Lean_Meta_simp(v_type_1860_, v_ctx_1848_, v___x_1866_, v___x_1867_, v___x_1868_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_fst_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1927_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1869_);
v_fst_1871_ = lean_ctor_get(v_a_1870_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_a_1870_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_a_1870_, 1);
lean_dec(v_unused_1928_);
v___x_1873_ = v_a_1870_;
v_isShared_1874_ = v_isSharedCheck_1927_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_fst_1871_);
lean_dec(v_a_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1927_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v_options_1912_; uint8_t v_hasTrace_1913_; 
v_options_1912_ = lean_ctor_get(v_a_1854_, 2);
v_hasTrace_1913_ = lean_ctor_get_uint8(v_options_1912_, sizeof(void*)*1);
if (v_hasTrace_1913_ == 0)
{
v___y_1876_ = v_a_1852_;
v___y_1877_ = v_a_1853_;
v___y_1878_ = v_a_1854_;
v___y_1879_ = v_a_1855_;
goto v___jp_1875_;
}
else
{
lean_object* v_inheritedTraceOptions_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_inheritedTraceOptions_1914_ = lean_ctor_get(v_a_1854_, 13);
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_1916_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
v___x_1917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1914_, v_options_1912_, v___x_1916_);
if (v___x_1917_ == 0)
{
v___y_1876_ = v_a_1852_;
v___y_1877_ = v_a_1853_;
v___y_1878_ = v_a_1854_;
v___y_1879_ = v_a_1855_;
goto v___jp_1875_;
}
else
{
lean_object* v_expr_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_expr_1918_ = lean_ctor_get(v_fst_1871_, 0);
v___x_1919_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__14);
lean_inc(v_destThmName_1851_);
v___x_1920_ = l_Lean_MessageData_ofName(v_destThmName_1851_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__16);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
lean_inc_ref(v_expr_1918_);
v___x_1924_ = l_Lean_indentExpr(v_expr_1918_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___x_1915_, v___x_1925_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_dec_ref(v___x_1926_);
v___y_1876_ = v_a_1852_;
v___y_1877_ = v_a_1853_;
v___y_1878_ = v_a_1854_;
v___y_1879_ = v_a_1855_;
goto v___jp_1875_;
}
else
{
lean_del_object(v___x_1873_);
lean_dec(v_fst_1871_);
lean_del_object(v___x_1862_);
lean_dec_ref(v_type_1860_);
lean_dec(v_levelParams_1859_);
lean_dec(v_destThmName_1851_);
lean_dec(v_eqThmName_1850_);
return v___x_1926_;
}
}
}
v___jp_1875_:
{
lean_object* v___x_1880_; 
lean_inc(v_fst_1871_);
v___x_1880_ = l_Lean_Meta_Simp_Result_getProof(v_fst_1871_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_expr_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
v_expr_1882_ = lean_ctor_get(v_fst_1871_, 0);
lean_inc_ref_n(v_expr_1882_, 2);
lean_dec(v_fst_1871_);
v___x_1883_ = lean_box(0);
lean_inc(v_levelParams_1859_);
v___x_1884_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__2(v_levelParams_1859_, v___x_1883_);
v___x_1885_ = l_Lean_mkConst(v_eqThmName_1850_, v___x_1884_);
v___x_1886_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12, &l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___closed__12);
v___x_1887_ = lean_unsigned_to_nat(4u);
v___x_1888_ = lean_mk_empty_array_with_capacity(v___x_1887_);
v___x_1889_ = lean_array_push(v___x_1888_, v_type_1860_);
v___x_1890_ = lean_array_push(v___x_1889_, v_expr_1882_);
v___x_1891_ = lean_array_push(v___x_1890_, v_a_1881_);
v___x_1892_ = lean_array_push(v___x_1891_, v___x_1885_);
v___x_1893_ = l_Lean_mkAppN(v___x_1886_, v___x_1892_);
lean_dec_ref(v___x_1892_);
lean_inc(v_destThmName_1851_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 2, v_expr_1882_);
lean_ctor_set(v___x_1862_, 0, v_destThmName_1851_);
v___x_1895_ = v___x_1862_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_destThmName_1851_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_levelParams_1859_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_expr_1882_);
v___x_1895_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 1);
lean_ctor_set(v___x_1873_, 1, v___x_1883_);
lean_ctor_set(v___x_1873_, 0, v_destThmName_1851_);
v___x_1897_ = v___x_1873_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_destThmName_1851_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___x_1883_);
v___x_1897_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1895_);
lean_ctor_set(v___x_1898_, 1, v___x_1893_);
lean_ctor_set(v___x_1898_, 2, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
v___x_1900_ = 0;
v___x_1901_ = l_Lean_addDecl(v___x_1899_, v___x_1900_, v___y_1878_, v___y_1879_);
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1873_);
lean_dec(v_fst_1871_);
lean_del_object(v___x_1862_);
lean_dec_ref(v_type_1860_);
lean_dec(v_levelParams_1859_);
lean_dec(v_destThmName_1851_);
lean_dec(v_eqThmName_1850_);
v_a_1904_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1880_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1880_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_del_object(v___x_1862_);
lean_dec_ref(v_type_1860_);
lean_dec(v_levelParams_1859_);
lean_dec(v_destThmName_1851_);
lean_dec(v_eqThmName_1850_);
v_a_1929_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1869_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1869_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
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
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_destThmName_1851_);
lean_dec(v_eqThmName_1850_);
lean_dec_ref(v_simprocs_1849_);
lean_dec_ref(v_ctx_1848_);
v_a_1939_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1857_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1857_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm___boxed(lean_object* v_ctx_1947_, lean_object* v_simprocs_1948_, lean_object* v_eqThmName_1949_, lean_object* v_destThmName_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(v_ctx_1947_, v_simprocs_1948_, v_eqThmName_1949_, v_destThmName_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(lean_object* v_00_u03b1_1957_, lean_object* v_constName_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___redArg(v_constName_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_constName_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0(v_00_u03b1_1965_, v_constName_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1973_, lean_object* v_ref_1974_, lean_object* v_constName_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___redArg(v_ref_1974_, v_constName_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1982_, lean_object* v_ref_1983_, lean_object* v_constName_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1(v_00_u03b1_1982_, v_ref_1983_, v_constName_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v_ref_1983_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1991_, lean_object* v_ref_1992_, lean_object* v_msg_1993_, lean_object* v_declHint_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1992_, v_msg_1993_, v_declHint_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2001_, lean_object* v_ref_2002_, lean_object* v_msg_2003_, lean_object* v_declHint_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_2001_, v_ref_2002_, v_msg_2003_, v_declHint_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_ref_2002_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_2011_, lean_object* v_declHint_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2011_, v_declHint_2012_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_2019_, lean_object* v_declHint_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_2019_, v_declHint_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2027_, lean_object* v_ref_2028_, lean_object* v_msg_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2028_, v_msg_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2036_, lean_object* v_ref_2037_, lean_object* v_msg_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2036_, v_ref_2037_, v_msg_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v_ref_2037_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(lean_object* v___x_2045_, lean_object* v___x_2046_, lean_object* v_instName_2047_, uint8_t v___x_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_as_2051_, size_t v_sz_2052_, size_t v_i_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_usize_dec_lt(v_i_2053_, v_sz_2052_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_instName_2047_);
lean_dec_ref(v___x_2045_);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_b_2054_);
return v___x_2061_;
}
else
{
lean_object* v_start_2062_; lean_object* v_stop_2063_; lean_object* v_step_2064_; uint8_t v___x_2065_; 
v_start_2062_ = lean_ctor_get(v_b_2054_, 0);
v_stop_2063_ = lean_ctor_get(v_b_2054_, 1);
v_step_2064_ = lean_ctor_get(v_b_2054_, 2);
v___x_2065_ = lean_nat_dec_lt(v_start_2062_, v_stop_2063_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; 
lean_dec_ref(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_instName_2047_);
lean_dec_ref(v___x_2045_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_b_2054_);
return v___x_2066_;
}
else
{
lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2094_; 
lean_inc(v_step_2064_);
lean_inc(v_stop_2063_);
lean_inc(v_start_2062_);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_b_2054_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; lean_object* v_unused_2096_; lean_object* v_unused_2097_; 
v_unused_2095_ = lean_ctor_get(v_b_2054_, 2);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_b_2054_, 1);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_b_2054_, 0);
lean_dec(v_unused_2097_);
v___x_2068_ = v_b_2054_;
v_isShared_2069_ = v_isSharedCheck_2094_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v_b_2054_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2094_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v_a_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2070_ = lean_unsigned_to_nat(1u);
v_a_2071_ = lean_array_uget_borrowed(v_as_2051_, v_i_2053_);
v___x_2072_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1));
lean_inc_ref(v___x_2045_);
v___x_2073_ = lean_string_append(v___x_2045_, v___x_2072_);
v___x_2074_ = lean_nat_add(v_start_2062_, v___x_2070_);
v___x_2075_ = l_Nat_reprFast(v___x_2074_);
v___x_2076_ = lean_string_append(v___x_2073_, v___x_2075_);
lean_dec_ref(v___x_2075_);
lean_inc(v_instName_2047_);
v___x_2077_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v___x_2046_, v_instName_2047_, v___x_2048_, v___x_2076_);
lean_inc(v_a_2071_);
lean_inc_ref(v_a_2050_);
lean_inc_ref(v_a_2049_);
v___x_2078_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(v_a_2049_, v_a_2050_, v_a_2071_, v___x_2077_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
lean_dec_ref(v___x_2078_);
v___x_2079_ = lean_nat_add(v_start_2062_, v_step_2064_);
lean_dec(v_start_2062_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2079_);
v___x_2081_ = v___x_2068_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_stop_2063_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_step_2064_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
size_t v___x_2082_; size_t v___x_2083_; 
v___x_2082_ = ((size_t)1ULL);
v___x_2083_ = lean_usize_add(v_i_2053_, v___x_2082_);
v_i_2053_ = v___x_2083_;
v_b_2054_ = v___x_2081_;
goto _start;
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_del_object(v___x_2068_);
lean_dec(v_step_2064_);
lean_dec(v_stop_2063_);
lean_dec(v_start_2062_);
lean_dec_ref(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_instName_2047_);
lean_dec_ref(v___x_2045_);
v_a_2086_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2078_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2078_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1___boxed(lean_object* v___x_2098_, lean_object* v___x_2099_, lean_object* v_instName_2100_, lean_object* v___x_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_as_2104_, lean_object* v_sz_2105_, lean_object* v_i_2106_, lean_object* v_b_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v___x_9634__boxed_2113_; size_t v_sz_boxed_2114_; size_t v_i_boxed_2115_; lean_object* v_res_2116_; 
v___x_9634__boxed_2113_ = lean_unbox(v___x_2101_);
v_sz_boxed_2114_ = lean_unbox_usize(v_sz_2105_);
lean_dec(v_sz_2105_);
v_i_boxed_2115_ = lean_unbox_usize(v_i_2106_);
lean_dec(v_i_2106_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_2098_, v___x_2099_, v_instName_2100_, v___x_9634__boxed_2113_, v_a_2102_, v_a_2103_, v_as_2104_, v_sz_boxed_2114_, v_i_boxed_2115_, v_b_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec_ref(v_as_2104_);
lean_dec_ref(v___x_2099_);
return v_res_2116_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__0));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(lean_object* v_a_2120_, lean_object* v___x_2121_, lean_object* v_instName_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_as_2125_, size_t v_sz_2126_, size_t v_i_2127_, lean_object* v_b_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_a_2135_; uint8_t v___x_2139_; 
v___x_2139_ = lean_usize_dec_lt(v_i_2127_, v_sz_2126_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_dec_ref(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_instName_2122_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_b_2128_);
return v___x_2140_;
}
else
{
lean_object* v_a_2141_; lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2198_; 
v_a_2141_ = lean_array_uget(v_as_2125_, v_i_2127_);
v_fst_2142_ = lean_ctor_get(v_a_2141_, 0);
v_snd_2143_ = lean_ctor_get(v_a_2141_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2145_ = v_a_2141_;
v_isShared_2146_ = v_isSharedCheck_2198_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_snd_2143_);
lean_inc(v_fst_2142_);
lean_dec(v_a_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2198_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; 
lean_inc(v_snd_2143_);
v___x_2147_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_snd_2143_, v___x_2139_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v___x_2147_);
v___x_2149_ = lean_box(0);
if (lean_obj_tag(v_a_2148_) == 1)
{
lean_object* v_val_2150_; uint8_t v_privateSpecs_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_del_object(v___x_2145_);
v_val_2150_ = lean_ctor_get(v_a_2148_, 0);
lean_inc(v_val_2150_);
lean_dec_ref(v_a_2148_);
v_privateSpecs_2151_ = lean_ctor_get_uint8(v_a_2120_, sizeof(void*)*3);
v___x_2152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2142_, v___x_2139_);
v___x_2153_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
lean_inc_ref(v___x_2152_);
v___x_2154_ = lean_string_append(v___x_2152_, v___x_2153_);
lean_inc(v_instName_2122_);
v___x_2155_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v___x_2121_, v_instName_2122_, v_privateSpecs_2151_, v___x_2154_);
lean_inc_ref(v_a_2124_);
lean_inc_ref(v_a_2123_);
v___x_2156_ = l___private_Lean_Meta_MethodSpecs_0__Lean_rewriteThm(v_a_2123_, v_a_2124_, v_val_2150_, v___x_2155_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v___x_2157_; 
lean_dec_ref(v___x_2156_);
v___x_2157_ = l_Lean_Meta_getEqnsFor_x3f(v_snd_2143_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2157_);
if (lean_obj_tag(v_a_2158_) == 1)
{
lean_object* v_val_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; size_t v_sz_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v_val_2159_ = lean_ctor_get(v_a_2158_, 0);
lean_inc(v_val_2159_);
lean_dec_ref(v_a_2158_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v___x_2161_ = lean_array_get_size(v_val_2159_);
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2160_);
lean_ctor_set(v___x_2163_, 1, v___x_2161_);
lean_ctor_set(v___x_2163_, 2, v___x_2162_);
v_sz_2164_ = lean_array_size(v_val_2159_);
v___x_2165_ = ((size_t)0ULL);
lean_inc_ref(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v_instName_2122_);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__1(v___x_2152_, v___x_2121_, v_instName_2122_, v_privateSpecs_2151_, v_a_2123_, v_a_2124_, v_val_2159_, v_sz_2164_, v___x_2165_, v___x_2163_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v_val_2159_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_dec_ref(v___x_2166_);
v_a_2135_ = v___x_2149_;
goto v___jp_2134_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_instName_2122_);
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_dec(v_a_2158_);
lean_dec_ref(v___x_2152_);
v_a_2135_ = v___x_2149_;
goto v___jp_2134_;
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec_ref(v___x_2152_);
lean_dec_ref(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_instName_2122_);
v_a_2175_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2157_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2157_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_dec_ref(v___x_2152_);
lean_dec(v_snd_2143_);
lean_dec_ref(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_instName_2122_);
return v___x_2156_;
}
}
else
{
uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_dec(v_a_2148_);
lean_dec(v_fst_2142_);
v___x_2183_ = 0;
v___x_2184_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___closed__1);
v___x_2185_ = l_Lean_MessageData_ofConstName(v_snd_2143_, v___x_2183_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 7);
lean_ctor_set(v___x_2145_, 1, v___x_2185_);
lean_ctor_set(v___x_2145_, 0, v___x_2184_);
v___x_2187_ = v___x_2145_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_throwError___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__3___redArg(v___x_2187_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_dec_ref(v___x_2188_);
v_a_2135_ = v___x_2149_;
goto v___jp_2134_;
}
else
{
lean_dec_ref(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_instName_2122_);
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_del_object(v___x_2145_);
lean_dec(v_snd_2143_);
lean_dec(v_fst_2142_);
lean_dec_ref(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_instName_2122_);
v_a_2190_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2147_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2147_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
v___jp_2134_:
{
size_t v___x_2136_; size_t v___x_2137_; 
v___x_2136_ = ((size_t)1ULL);
v___x_2137_ = lean_usize_add(v_i_2127_, v___x_2136_);
v_i_2127_ = v___x_2137_;
v_b_2128_ = v_a_2135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2___boxed(lean_object* v_a_2199_, lean_object* v___x_2200_, lean_object* v_instName_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_as_2204_, lean_object* v_sz_2205_, lean_object* v_i_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
size_t v_sz_boxed_2213_; size_t v_i_boxed_2214_; lean_object* v_res_2215_; 
v_sz_boxed_2213_ = lean_unbox_usize(v_sz_2205_);
lean_dec(v_sz_2205_);
v_i_boxed_2214_ = lean_unbox_usize(v_i_2206_);
lean_dec(v_i_2206_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_2199_, v___x_2200_, v_instName_2201_, v_a_2202_, v_a_2203_, v_as_2204_, v_sz_boxed_2213_, v_i_boxed_2214_, v_b_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec_ref(v_as_2204_);
lean_dec_ref(v___x_2200_);
lean_dec_ref(v_a_2199_);
return v_res_2215_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__0));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__2));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(lean_object* v_as_2222_, size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_b_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v_b_2225_);
return v___x_2232_;
}
else
{
lean_object* v_options_2233_; lean_object* v_inheritedTraceOptions_2234_; uint8_t v_hasTrace_2235_; lean_object* v_a_2236_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; 
v_options_2233_ = lean_ctor_get(v___y_2228_, 2);
v_inheritedTraceOptions_2234_ = lean_ctor_get(v___y_2228_, 13);
v_hasTrace_2235_ = lean_ctor_get_uint8(v_options_2233_, sizeof(void*)*1);
v_a_2236_ = lean_array_uget_borrowed(v_as_2222_, v_i_2224_);
if (v_hasTrace_2235_ == 0)
{
v___y_2238_ = v___y_2226_;
v___y_2239_ = v___y_2227_;
v___y_2240_ = v___y_2228_;
v___y_2241_ = v___y_2229_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2263_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_2264_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__6);
v___x_2265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2234_, v_options_2233_, v___x_2264_);
if (v___x_2265_ == 0)
{
v___y_2238_ = v___y_2226_;
v___y_2239_ = v___y_2227_;
v___y_2240_ = v___y_2228_;
v___y_2241_ = v___y_2229_;
goto v___jp_2237_;
}
else
{
lean_object* v_name_2266_; lean_object* v_type_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_name_2266_ = lean_ctor_get(v_a_2236_, 0);
v_type_2267_ = lean_ctor_get(v_a_2236_, 2);
v___x_2268_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__1);
lean_inc(v_name_2266_);
v___x_2269_ = l_Lean_MessageData_ofName(v_name_2266_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___closed__3);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
lean_inc_ref(v_type_2267_);
v___x_2273_ = l_Lean_MessageData_ofExpr(v_type_2267_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = l_Lean_addTrace___at___00__private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo_spec__11(v___x_2263_, v___x_2274_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_dec_ref(v___x_2275_);
v___y_2238_ = v___y_2226_;
v___y_2239_ = v___y_2227_;
v___y_2240_ = v___y_2228_;
v___y_2241_ = v___y_2229_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_b_2225_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
v___jp_2237_:
{
lean_object* v_name_2242_; lean_object* v_levelParams_2243_; lean_object* v_type_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v_name_2242_ = lean_ctor_get(v_a_2236_, 0);
v_levelParams_2243_ = lean_ctor_get(v_a_2236_, 1);
v_type_2244_ = lean_ctor_get(v_a_2236_, 2);
lean_inc(v_name_2242_);
v___x_2245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_name_2242_);
lean_inc(v_levelParams_2243_);
v___x_2246_ = lean_array_mk(v_levelParams_2243_);
v___x_2247_ = lean_unsigned_to_nat(1000u);
v___x_2248_ = l_Lean_Meta_simpGlobalConfig;
lean_inc_ref(v_type_2244_);
v___x_2249_ = l_Lean_Meta_mkDSimpTheorem(v___x_2245_, v___x_2246_, v_type_2244_, v___x_2231_, v___x_2247_, v___x_2248_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = l_Lean_Meta_SimpTheorems_addSimpTheorem(v_b_2225_, v_a_2250_);
v___x_2252_ = ((size_t)1ULL);
v___x_2253_ = lean_usize_add(v_i_2224_, v___x_2252_);
v_i_2224_ = v___x_2253_;
v_b_2225_ = v___x_2251_;
goto _start;
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec_ref(v_b_2225_);
v_a_2255_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2249_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2249_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0___boxed(lean_object* v_as_2284_, lean_object* v_sz_2285_, lean_object* v_i_2286_, lean_object* v_b_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2285_);
lean_dec(v_sz_2285_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2286_);
lean_dec(v_i_2286_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_as_2284_, v_sz_boxed_2293_, v_i_boxed_2294_, v_b_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v_as_2284_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(lean_object* v___x_2303_, lean_object* v_thms_2304_, lean_object* v_fieldImpls_2305_, lean_object* v_a_2306_, lean_object* v_instName_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2303_, v___y_2311_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; size_t v_sz_2315_; size_t v___x_2316_; lean_object* v___x_2317_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
v_sz_2315_ = lean_array_size(v_thms_2304_);
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__0(v_thms_2304_, v_sz_2315_, v___x_2316_, v_a_2314_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref(v___x_2317_);
v___x_2319_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_2311_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2319_);
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___closed__0));
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2324_ = lean_array_push(v___x_2323_, v_a_2318_);
v___x_2325_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2321_, v___x_2324_, v_a_2320_, v___y_2308_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v___x_2327_ = l_Lean_Meta_Simp_getSimprocs___redArg(v___y_2311_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v_env_2330_; lean_object* v___x_2331_; size_t v_sz_2332_; lean_object* v___x_2333_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref(v___x_2327_);
v___x_2329_ = lean_st_ref_get(v___y_2311_);
v_env_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc_ref(v_env_2330_);
lean_dec(v___x_2329_);
v___x_2331_ = lean_box(0);
v_sz_2332_ = lean_array_size(v_fieldImpls_2305_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__2(v_a_2306_, v_env_2330_, v_instName_2307_, v_a_2326_, v_a_2328_, v_fieldImpls_2305_, v_sz_2332_, v___x_2316_, v___x_2331_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec_ref(v_env_2330_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v___x_2333_, 0);
lean_dec(v_unused_2341_);
v___x_2335_ = v___x_2333_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v___x_2333_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2331_);
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2331_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
return v___x_2333_;
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_a_2326_);
lean_dec(v_instName_2307_);
v_a_2342_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2327_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2327_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_instName_2307_);
v_a_2350_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2325_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2325_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_2318_);
lean_dec(v_instName_2307_);
v_a_2358_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2319_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2319_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_instName_2307_);
v_a_2366_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2317_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2317_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_instName_2307_);
v_a_2374_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2313_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2313_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed(lean_object* v___x_2382_, lean_object* v_thms_2383_, lean_object* v_fieldImpls_2384_, lean_object* v_a_2385_, lean_object* v_instName_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0(v___x_2382_, v_thms_2383_, v_fieldImpls_2384_, v_a_2385_, v_instName_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec_ref(v_a_2385_);
lean_dec_ref(v_fieldImpls_2384_);
lean_dec_ref(v_thms_2383_);
lean_dec_ref(v___x_2382_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(lean_object* v___y_2393_, uint8_t v_isExporting_2394_, lean_object* v___x_2395_, lean_object* v___y_2396_, lean_object* v___x_2397_, lean_object* v_a_x3f_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v_env_2401_; lean_object* v_nextMacroScope_2402_; lean_object* v_ngen_2403_; lean_object* v_auxDeclNGen_2404_; lean_object* v_traceState_2405_; lean_object* v_messages_2406_; lean_object* v_infoState_2407_; lean_object* v_snapshotTasks_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2433_; 
v___x_2400_ = lean_st_ref_take(v___y_2393_);
v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
v_nextMacroScope_2402_ = lean_ctor_get(v___x_2400_, 1);
v_ngen_2403_ = lean_ctor_get(v___x_2400_, 2);
v_auxDeclNGen_2404_ = lean_ctor_get(v___x_2400_, 3);
v_traceState_2405_ = lean_ctor_get(v___x_2400_, 4);
v_messages_2406_ = lean_ctor_get(v___x_2400_, 6);
v_infoState_2407_ = lean_ctor_get(v___x_2400_, 7);
v_snapshotTasks_2408_ = lean_ctor_get(v___x_2400_, 8);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v___x_2400_, 5);
lean_dec(v_unused_2434_);
v___x_2410_ = v___x_2400_;
v_isShared_2411_ = v_isSharedCheck_2433_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snapshotTasks_2408_);
lean_inc(v_infoState_2407_);
lean_inc(v_messages_2406_);
lean_inc(v_traceState_2405_);
lean_inc(v_auxDeclNGen_2404_);
lean_inc(v_ngen_2403_);
lean_inc(v_nextMacroScope_2402_);
lean_inc(v_env_2401_);
lean_dec(v___x_2400_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2433_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = l_Lean_Environment_setExporting(v_env_2401_, v_isExporting_2394_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 5, v___x_2395_);
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_nextMacroScope_2402_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_ngen_2403_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_auxDeclNGen_2404_);
lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_traceState_2405_);
lean_ctor_set(v_reuseFailAlloc_2432_, 5, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2432_, 6, v_messages_2406_);
lean_ctor_set(v_reuseFailAlloc_2432_, 7, v_infoState_2407_);
lean_ctor_set(v_reuseFailAlloc_2432_, 8, v_snapshotTasks_2408_);
v___x_2414_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_mctx_2417_; lean_object* v_zetaDeltaFVarIds_2418_; lean_object* v_postponed_2419_; lean_object* v_diag_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2430_; 
v___x_2415_ = lean_st_ref_set(v___y_2393_, v___x_2414_);
v___x_2416_ = lean_st_ref_take(v___y_2396_);
v_mctx_2417_ = lean_ctor_get(v___x_2416_, 0);
v_zetaDeltaFVarIds_2418_ = lean_ctor_get(v___x_2416_, 2);
v_postponed_2419_ = lean_ctor_get(v___x_2416_, 3);
v_diag_2420_ = lean_ctor_get(v___x_2416_, 4);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___x_2416_, 1);
lean_dec(v_unused_2431_);
v___x_2422_ = v___x_2416_;
v_isShared_2423_ = v_isSharedCheck_2430_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_diag_2420_);
lean_inc(v_postponed_2419_);
lean_inc(v_zetaDeltaFVarIds_2418_);
lean_inc(v_mctx_2417_);
lean_dec(v___x_2416_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2430_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2397_);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_mctx_2417_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2429_, 2, v_zetaDeltaFVarIds_2418_);
lean_ctor_set(v_reuseFailAlloc_2429_, 3, v_postponed_2419_);
lean_ctor_set(v_reuseFailAlloc_2429_, 4, v_diag_2420_);
v___x_2425_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = lean_st_ref_set(v___y_2396_, v___x_2425_);
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v___y_2435_, lean_object* v_isExporting_2436_, lean_object* v___x_2437_, lean_object* v___y_2438_, lean_object* v___x_2439_, lean_object* v_a_x3f_2440_, lean_object* v___y_2441_){
_start:
{
uint8_t v_isExporting_boxed_2442_; lean_object* v_res_2443_; 
v_isExporting_boxed_2442_ = lean_unbox(v_isExporting_2436_);
v_res_2443_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_2435_, v_isExporting_boxed_2442_, v___x_2437_, v___y_2438_, v___x_2439_, v_a_x3f_2440_);
lean_dec(v_a_x3f_2440_);
lean_dec(v___y_2438_);
lean_dec(v___y_2435_);
return v_res_2443_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2444_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__0);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__1);
v___x_2450_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
lean_ctor_set(v___x_2450_, 2, v___x_2449_);
lean_ctor_set(v___x_2450_, 3, v___x_2449_);
lean_ctor_set(v___x_2450_, 4, v___x_2449_);
lean_ctor_set(v___x_2450_, 5, v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(lean_object* v_x_2451_, uint8_t v_isExporting_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v_env_2459_; uint8_t v_isExporting_2460_; lean_object* v___x_2461_; lean_object* v_env_2462_; lean_object* v_nextMacroScope_2463_; lean_object* v_ngen_2464_; lean_object* v_auxDeclNGen_2465_; lean_object* v_traceState_2466_; lean_object* v_messages_2467_; lean_object* v_infoState_2468_; lean_object* v_snapshotTasks_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2523_; 
v___x_2458_ = lean_st_ref_get(v___y_2456_);
v_env_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_env_2459_);
lean_dec(v___x_2458_);
v_isExporting_2460_ = lean_ctor_get_uint8(v_env_2459_, sizeof(void*)*8);
lean_dec_ref(v_env_2459_);
v___x_2461_ = lean_st_ref_take(v___y_2456_);
v_env_2462_ = lean_ctor_get(v___x_2461_, 0);
v_nextMacroScope_2463_ = lean_ctor_get(v___x_2461_, 1);
v_ngen_2464_ = lean_ctor_get(v___x_2461_, 2);
v_auxDeclNGen_2465_ = lean_ctor_get(v___x_2461_, 3);
v_traceState_2466_ = lean_ctor_get(v___x_2461_, 4);
v_messages_2467_ = lean_ctor_get(v___x_2461_, 6);
v_infoState_2468_ = lean_ctor_get(v___x_2461_, 7);
v_snapshotTasks_2469_ = lean_ctor_get(v___x_2461_, 8);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2461_, 5);
lean_dec(v_unused_2524_);
v___x_2471_ = v___x_2461_;
v_isShared_2472_ = v_isSharedCheck_2523_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_snapshotTasks_2469_);
lean_inc(v_infoState_2468_);
lean_inc(v_messages_2467_);
lean_inc(v_traceState_2466_);
lean_inc(v_auxDeclNGen_2465_);
lean_inc(v_ngen_2464_);
lean_inc(v_nextMacroScope_2463_);
lean_inc(v_env_2462_);
lean_dec(v___x_2461_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2523_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2473_ = l_Lean_Environment_setExporting(v_env_2462_, v_isExporting_2452_);
v___x_2474_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__2);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 5, v___x_2474_);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2476_ = v___x_2471_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_nextMacroScope_2463_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_ngen_2464_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_auxDeclNGen_2465_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_traceState_2466_);
lean_ctor_set(v_reuseFailAlloc_2522_, 5, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2522_, 6, v_messages_2467_);
lean_ctor_set(v_reuseFailAlloc_2522_, 7, v_infoState_2468_);
lean_ctor_set(v_reuseFailAlloc_2522_, 8, v_snapshotTasks_2469_);
v___x_2476_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_mctx_2479_; lean_object* v_zetaDeltaFVarIds_2480_; lean_object* v_postponed_2481_; lean_object* v_diag_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2520_; 
v___x_2477_ = lean_st_ref_set(v___y_2456_, v___x_2476_);
v___x_2478_ = lean_st_ref_take(v___y_2454_);
v_mctx_2479_ = lean_ctor_get(v___x_2478_, 0);
v_zetaDeltaFVarIds_2480_ = lean_ctor_get(v___x_2478_, 2);
v_postponed_2481_ = lean_ctor_get(v___x_2478_, 3);
v_diag_2482_ = lean_ctor_get(v___x_2478_, 4);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v___x_2478_, 1);
lean_dec(v_unused_2521_);
v___x_2484_ = v___x_2478_;
v_isShared_2485_ = v_isSharedCheck_2520_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_diag_2482_);
lean_inc(v_postponed_2481_);
lean_inc(v_zetaDeltaFVarIds_2480_);
lean_inc(v_mctx_2479_);
lean_dec(v___x_2478_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2520_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2486_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___closed__3);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2486_);
v___x_2488_ = v___x_2484_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_mctx_2479_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_zetaDeltaFVarIds_2480_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_postponed_2481_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_diag_2482_);
v___x_2488_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v_r_2490_; 
v___x_2489_ = lean_st_ref_set(v___y_2454_, v___x_2488_);
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
lean_inc(v___y_2454_);
lean_inc_ref(v___y_2453_);
v_r_2490_ = lean_apply_5(v_x_2451_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, lean_box(0));
if (lean_obj_tag(v_r_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2507_; 
v_a_2491_ = lean_ctor_get(v_r_2490_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_r_2490_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2493_ = v_r_2490_;
v_isShared_2494_ = v_isSharedCheck_2507_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v_r_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2507_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
lean_inc(v_a_2491_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
v___x_2497_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_2456_, v_isExporting_2460_, v___x_2474_, v___y_2454_, v___x_2486_, v___x_2496_);
lean_dec_ref(v___x_2496_);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v___x_2497_, 0);
lean_dec(v_unused_2505_);
v___x_2499_ = v___x_2497_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_dec(v___x_2497_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v_a_2491_);
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2491_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_a_2508_ = lean_ctor_get(v_r_2490_, 0);
lean_inc(v_a_2508_);
lean_dec_ref(v_r_2490_);
v___x_2509_ = lean_box(0);
v___x_2510_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___lam__0(v___y_2456_, v_isExporting_2460_, v___x_2474_, v___y_2454_, v___x_2486_, v___x_2509_);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v___x_2510_, 0);
lean_dec(v_unused_2518_);
v___x_2512_ = v___x_2510_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_dec(v___x_2510_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set_tag(v___x_2512_, 1);
lean_ctor_set(v___x_2512_, 0, v_a_2508_);
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2508_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg___boxed(lean_object* v_x_2525_, lean_object* v_isExporting_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
uint8_t v_isExporting_boxed_2532_; lean_object* v_res_2533_; 
v_isExporting_boxed_2532_ = lean_unbox(v_isExporting_2526_);
v_res_2533_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_2525_, v_isExporting_boxed_2532_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(lean_object* v_x_2534_, uint8_t v_when_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
if (v_when_2535_ == 0)
{
lean_object* v___x_2541_; 
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2536_);
v___x_2541_ = lean_apply_5(v_x_2534_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, lean_box(0));
return v___x_2541_;
}
else
{
uint8_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = 0;
v___x_2543_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_2534_, v___x_2542_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg___boxed(lean_object* v_x_2544_, lean_object* v_when_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
uint8_t v_when_boxed_2551_; lean_object* v_res_2552_; 
v_when_boxed_2551_ = lean_unbox(v_when_2545_);
v_res_2552_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_2544_, v_when_boxed_2551_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(lean_object* v_instName_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; 
lean_inc(v_instName_2553_);
v___x_2559_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; uint8_t v_privateSpecs_2561_; lean_object* v_fieldImpls_2562_; lean_object* v_thms_2563_; lean_object* v___x_2564_; lean_object* v___f_2565_; lean_object* v___x_2566_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref(v___x_2559_);
v_privateSpecs_2561_ = lean_ctor_get_uint8(v_a_2560_, sizeof(void*)*3);
v_fieldImpls_2562_ = lean_ctor_get(v_a_2560_, 1);
lean_inc_ref(v_fieldImpls_2562_);
v_thms_2563_ = lean_ctor_get(v_a_2560_, 2);
lean_inc_ref(v_thms_2563_);
v___x_2564_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsSimpExtension;
v___f_2565_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2565_, 0, v___x_2564_);
lean_closure_set(v___f_2565_, 1, v_thms_2563_);
lean_closure_set(v___f_2565_, 2, v_fieldImpls_2562_);
lean_closure_set(v___f_2565_, 3, v_a_2560_);
lean_closure_set(v___f_2565_, 4, v_instName_2553_);
v___x_2566_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v___f_2565_, v_privateSpecs_2561_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2566_;
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_instName_2553_);
v_a_2567_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2559_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2559_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed(lean_object* v_instName_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize(v_instName_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(lean_object* v_00_u03b1_2582_, lean_object* v_x_2583_, uint8_t v_isExporting_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___redArg(v_x_2583_, v_isExporting_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2591_, lean_object* v_x_2592_, lean_object* v_isExporting_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v_isExporting_boxed_2599_; lean_object* v_res_2600_; 
v_isExporting_boxed_2599_ = lean_unbox(v_isExporting_2593_);
v_res_2600_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3_spec__3(v_00_u03b1_2591_, v_x_2592_, v_isExporting_boxed_2599_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(lean_object* v_00_u03b1_2601_, lean_object* v_x_2602_, uint8_t v_when_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___redArg(v_x_2602_, v_when_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_x_2611_, lean_object* v_when_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v_when_boxed_2618_; lean_object* v_res_2619_; 
v_when_boxed_2618_ = lean_unbox(v_when_2612_);
v_res_2619_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize_spec__3(v_00_u03b1_2610_, v_x_2611_, v_when_boxed_2618_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(lean_object* v_instName_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___closed__0));
lean_inc(v_instName_2622_);
v___x_2629_ = l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo(v_instName_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v_env_2632_; uint8_t v_privateSpecs_2633_; lean_object* v_fieldImpls_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v_fst_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2629_);
v___x_2631_ = lean_st_ref_get(v_a_2626_);
v_env_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc_ref(v_env_2632_);
lean_dec(v___x_2631_);
v_privateSpecs_2633_ = lean_ctor_get_uint8(v_a_2630_, sizeof(void*)*3);
v_fieldImpls_2634_ = lean_ctor_get(v_a_2630_, 1);
lean_inc_ref(v_fieldImpls_2634_);
lean_dec(v_a_2630_);
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_array_get(v___x_2628_, v_fieldImpls_2634_, v___x_2635_);
lean_dec_ref(v_fieldImpls_2634_);
v_fst_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_fst_2637_);
lean_dec(v___x_2636_);
v___x_2638_ = 1;
v___x_2639_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2637_, v___x_2638_);
v___x_2640_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
lean_inc_n(v_instName_2622_, 2);
v___x_2642_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2632_, v_instName_2622_, v_privateSpecs_2633_, v___x_2641_);
lean_dec_ref(v_env_2632_);
v___x_2643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs_doRealize___boxed), 6, 1);
lean_closure_set(v___x_2643_, 0, v_instName_2622_);
v___x_2644_ = l_Lean_Meta_realizeConst(v_instName_2622_, v___x_2642_, v___x_2643_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
return v___x_2644_;
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_instName_2622_);
v_a_2645_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2629_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2629_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs___boxed(lean_object* v_instName_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(v_instName_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___redArg(lean_object* v_instName_2660_, lean_object* v_op_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v_env_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2665_ = lean_st_ref_get(v_a_2663_);
v_env_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc_ref_n(v_env_2666_, 2);
lean_dec(v___x_2665_);
v___x_2667_ = ((lean_object*)(l_Lean_instInhabitedMethodSpecsAttrData_default));
v___x_2668_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
lean_inc(v_instName_2660_);
v___x_2669_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_2667_, v___x_2668_, v_env_2666_, v_instName_2660_);
if (lean_obj_tag(v___x_2669_) == 1)
{
lean_object* v_val_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2698_; 
v_val_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2698_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_val_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2698_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
uint8_t v_privateSpecs_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_privateSpecs_2674_ = lean_ctor_get_uint8(v_val_2670_, sizeof(void*)*1);
lean_dec(v_val_2670_);
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
v___x_2676_ = lean_string_append(v_op_2661_, v___x_2675_);
v___x_2677_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2666_, v_instName_2660_, v_privateSpecs_2674_, v___x_2676_);
lean_dec_ref(v_env_2666_);
v___x_2678_ = l_Lean_realizeGlobalConstNoOverloadCore(v___x_2677_, v_a_2662_, v_a_2663_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2689_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2689_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2689_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v_a_2679_);
v___x_2684_ = v___x_2672_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2684_);
v___x_2686_ = v___x_2681_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_del_object(v___x_2672_);
v_a_2690_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2678_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2678_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_dec(v___x_2669_);
lean_dec_ref(v_env_2666_);
lean_dec_ref(v_op_2661_);
lean_dec(v_instName_2660_);
v___x_2699_ = lean_box(0);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___redArg___boxed(lean_object* v_instName_2701_, lean_object* v_op_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_getMethodSpecTheorem___redArg(v_instName_2701_, v_op_2702_, v_a_2703_, v_a_2704_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem(lean_object* v_instName_2707_, lean_object* v_op_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_getMethodSpecTheorem___redArg(v_instName_2707_, v_op_2708_, v_a_2711_, v_a_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorem___boxed(lean_object* v_instName_2715_, lean_object* v_op_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_getMethodSpecTheorem(v_instName_2715_, v_op_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(lean_object* v_op_2723_, lean_object* v_instName_2724_, uint8_t v___x_2725_, lean_object* v___x_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v_fst_2731_; lean_object* v_snd_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2754_; 
v___x_2730_ = lean_st_ref_get(v___y_2728_);
v_fst_2731_ = lean_ctor_get(v_b_2727_, 0);
v_snd_2732_ = lean_ctor_get(v_b_2727_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_b_2727_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2734_ = v_b_2727_;
v_isShared_2735_ = v_isSharedCheck_2754_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_snd_2732_);
lean_inc(v_fst_2731_);
lean_dec(v_b_2727_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2754_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v_env_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v_env_2736_ = lean_ctor_get(v___x_2730_, 0);
lean_inc_ref(v_env_2736_);
lean_dec(v___x_2730_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__1));
lean_inc_ref(v_op_2723_);
v___x_2738_ = lean_string_append(v_op_2723_, v___x_2737_);
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_nat_add(v_fst_2731_, v___x_2739_);
lean_inc(v___x_2740_);
v___x_2741_ = l_Nat_reprFast(v___x_2740_);
v___x_2742_ = lean_string_append(v___x_2738_, v___x_2741_);
lean_dec_ref(v___x_2741_);
lean_inc(v_instName_2724_);
v___x_2743_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2736_, v_instName_2724_, v___x_2725_, v___x_2742_);
lean_dec_ref(v_env_2736_);
v___x_2744_ = l_Lean_Environment_containsOnBranch(v___x_2726_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2746_; 
lean_dec(v___x_2743_);
lean_dec(v___x_2740_);
lean_dec(v_instName_2724_);
lean_dec_ref(v_op_2723_);
if (v_isShared_2735_ == 0)
{
v___x_2746_ = v___x_2734_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_fst_2731_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_snd_2732_);
v___x_2746_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
return v___x_2747_;
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_dec(v_fst_2731_);
v___x_2749_ = lean_array_push(v_snd_2732_, v___x_2743_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2749_);
lean_ctor_set(v___x_2734_, 0, v___x_2740_);
v___x_2751_ = v___x_2734_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
v_b_2727_ = v___x_2751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg___boxed(lean_object* v_op_2755_, lean_object* v_instName_2756_, lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v_b_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___x_1804__boxed_2762_; lean_object* v_res_2763_; 
v___x_1804__boxed_2762_ = lean_unbox(v___x_2757_);
v_res_2763_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_2755_, v_instName_2756_, v___x_1804__boxed_2762_, v___x_2758_, v_b_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___x_2758_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorems(lean_object* v_instName_2769_, lean_object* v_op_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v___x_2776_; lean_object* v_env_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2776_ = lean_st_ref_get(v_a_2774_);
v_env_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc_ref(v_env_2777_);
lean_dec(v___x_2776_);
v___x_2778_ = ((lean_object*)(l_Lean_instInhabitedMethodSpecsAttrData_default));
v___x_2779_ = l___private_Lean_Meta_MethodSpecs_0__Lean_methodSpecsAttr;
lean_inc(v_instName_2769_);
v___x_2780_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_2778_, v___x_2779_, v_env_2777_, v_instName_2769_);
if (lean_obj_tag(v___x_2780_) == 1)
{
lean_object* v_val_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2824_; 
v_val_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2824_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_val_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2824_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v_env_2786_; uint8_t v_privateSpecs_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2785_ = lean_st_ref_get(v_a_2774_);
v_env_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc_ref(v_env_2786_);
lean_dec(v___x_2785_);
v_privateSpecs_2787_ = lean_ctor_get_uint8(v_val_2781_, sizeof(void*)*1);
lean_dec(v_val_2781_);
v___x_2788_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmLikeSuffix___closed__0));
lean_inc_ref(v_op_2770_);
v___x_2789_ = lean_string_append(v_op_2770_, v___x_2788_);
lean_inc(v_instName_2769_);
v___x_2790_ = l___private_Lean_Meta_MethodSpecs_0__Lean_mkSpecTheoremName(v_env_2786_, v_instName_2769_, v_privateSpecs_2787_, v___x_2789_);
lean_dec_ref(v_env_2786_);
v___x_2791_ = l_Lean_realizeGlobalConstNoOverloadCore(v___x_2790_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v___x_2792_; lean_object* v_env_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec_ref(v___x_2791_);
v___x_2792_ = lean_st_ref_get(v_a_2774_);
v_env_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc_ref(v_env_2793_);
lean_dec(v___x_2792_);
v___x_2794_ = ((lean_object*)(l_Lean_getMethodSpecTheorems___closed__1));
v___x_2795_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_2770_, v_instName_2769_, v_privateSpecs_2787_, v_env_2793_, v___x_2794_, v_a_2774_);
lean_dec_ref(v_env_2793_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2807_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2807_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2807_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v_snd_2800_; lean_object* v___x_2802_; 
v_snd_2800_ = lean_ctor_get(v_a_2796_, 1);
lean_inc(v_snd_2800_);
lean_dec(v_a_2796_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v_snd_2800_);
v___x_2802_ = v___x_2783_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_snd_2800_);
v___x_2802_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2802_);
v___x_2804_ = v___x_2798_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_del_object(v___x_2783_);
v_a_2808_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2795_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2795_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_del_object(v___x_2783_);
lean_dec_ref(v_op_2770_);
lean_dec(v_instName_2769_);
v_a_2816_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2791_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2791_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v___x_2780_);
lean_dec_ref(v_op_2770_);
lean_dec(v_instName_2769_);
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMethodSpecTheorems___boxed(lean_object* v_instName_2827_, lean_object* v_op_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_getMethodSpecTheorems(v_instName_2827_, v_op_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0(lean_object* v_op_2835_, lean_object* v_instName_2836_, uint8_t v___x_2837_, lean_object* v___x_2838_, lean_object* v_b_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___redArg(v_op_2835_, v_instName_2836_, v___x_2837_, v___x_2838_, v_b_2839_, v___y_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0___boxed(lean_object* v_op_2846_, lean_object* v_instName_2847_, lean_object* v___x_2848_, lean_object* v___x_2849_, lean_object* v_b_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
uint8_t v___x_1972__boxed_2856_; lean_object* v_res_2857_; 
v___x_1972__boxed_2856_ = lean_unbox(v___x_2848_);
v_res_2857_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_getMethodSpecTheorems_spec__0(v_op_2846_, v_instName_2847_, v___x_1972__boxed_2856_, v___x_2849_, v_b_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec_ref(v___x_2849_);
return v_res_2857_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(lean_object* v_env_2858_, lean_object* v_name_2859_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(v_env_2858_, v_name_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
uint8_t v___x_2861_; 
v___x_2861_ = 0;
return v___x_2861_;
}
else
{
uint8_t v___x_2862_; 
lean_dec_ref(v___x_2860_);
v___x_2862_ = 1;
return v___x_2862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object* v_env_2863_, lean_object* v_name_2864_){
_start:
{
uint8_t v_res_2865_; lean_object* v_r_2866_; 
v_res_2865_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v_env_2863_, v_name_2864_);
v_r_2866_ = lean_box(v_res_2865_);
return v_r_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(lean_object* v___x_2867_, lean_object* v_name_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v___x_2872_; lean_object* v_env_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_st_ref_get(v___y_2870_);
v_env_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc_ref(v_env_2873_);
lean_dec(v___x_2872_);
v___x_2874_ = l___private_Lean_Meta_MethodSpecs_0__Lean_isSpecThmNameFor(v_env_2873_, v_name_2868_);
if (lean_obj_tag(v___x_2874_) == 1)
{
lean_object* v_val_2875_; uint8_t v___x_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_val_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_val_2875_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = 0;
v___x_2877_ = 1;
v___x_2878_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__2);
v___x_2879_ = lean_unsigned_to_nat(32u);
v___x_2880_ = lean_mk_empty_array_with_capacity(v___x_2879_);
lean_dec_ref(v___x_2880_);
v___x_2881_ = lean_unsigned_to_nat(0u);
v___x_2882_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__6);
v___x_2883_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__7);
v___x_2884_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__8));
v___x_2885_ = lean_box(0);
lean_inc(v___x_2867_);
v___x_2886_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2886_, 0, v___x_2878_);
lean_ctor_set(v___x_2886_, 1, v___x_2867_);
lean_ctor_set(v___x_2886_, 2, v___x_2883_);
lean_ctor_set(v___x_2886_, 3, v___x_2884_);
lean_ctor_set(v___x_2886_, 4, v___x_2885_);
lean_ctor_set(v___x_2886_, 5, v___x_2881_);
lean_ctor_set(v___x_2886_, 6, v___x_2885_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7, v___x_2876_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 1, v___x_2876_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 2, v___x_2876_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 3, v___x_2877_);
v___x_2887_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__10);
v___x_2888_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__11);
v___x_2889_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12, &l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12_once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_getParam___redArg___closed__12);
v___x_2890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2887_);
lean_ctor_set(v___x_2890_, 1, v___x_2888_);
lean_ctor_set(v___x_2890_, 2, v___x_2867_);
lean_ctor_set(v___x_2890_, 3, v___x_2882_);
lean_ctor_set(v___x_2890_, 4, v___x_2889_);
v___x_2891_ = lean_st_mk_ref(v___x_2890_);
v___x_2892_ = l___private_Lean_Meta_MethodSpecs_0__Lean_genSpecs(v_val_2875_, v___x_2886_, v___x_2891_, v___y_2869_, v___y_2870_);
lean_dec_ref(v___x_2886_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2901_; 
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v___x_2892_, 0);
lean_dec(v_unused_2902_);
v___x_2894_ = v___x_2892_;
v_isShared_2895_ = v_isSharedCheck_2901_;
goto v_resetjp_2893_;
}
else
{
lean_dec(v___x_2892_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2901_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2896_ = lean_st_ref_get(v___x_2891_);
lean_dec(v___x_2891_);
lean_dec(v___x_2896_);
v___x_2897_ = lean_box(v___x_2877_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2897_);
v___x_2899_ = v___x_2894_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
else
{
lean_dec(v___x_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2910_; 
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2892_, 0);
lean_dec(v_unused_2911_);
v___x_2904_ = v___x_2892_;
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
else
{
lean_dec(v___x_2892_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2910_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = lean_box(v___x_2877_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2906_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2892_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2892_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
else
{
uint8_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v___x_2874_);
lean_dec(v___x_2867_);
v___x_2920_ = 0;
v___x_2921_ = lean_box(v___x_2920_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object* v___x_2923_, lean_object* v_name_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___lam__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(v___x_2923_, v_name_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_2933_; lean_object* v___x_2934_; 
v___f_2933_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__0_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_));
v___x_2934_ = l_Lean_registerReservedNamePredicate(v___f_2933_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v___f_2935_; lean_object* v___x_2936_; 
lean_dec_ref(v___x_2934_);
v___f_2935_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__1_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_));
v___x_2936_ = l_Lean_registerReservedNameAction(v___f_2935_);
return v___x_2936_;
}
else
{
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2____boxed(lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_784571591____hygCtx___hyg_2_();
return v_res_2938_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(2329740376u);
v___x_2957_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__6_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_));
v___x_2958_ = l_Lean_Name_num___override(v___x_2957_, v___x_2956_);
return v___x_2958_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__8_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_));
v___x_2961_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__7_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_2962_ = l_Lean_Name_str___override(v___x_2961_, v___x_2960_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__10_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_));
v___x_2965_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__9_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_2966_ = l_Lean_Name_str___override(v___x_2965_, v___x_2964_);
return v___x_2966_;
}
}
static lean_object* _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = lean_unsigned_to_nat(2u);
v___x_2968_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__11_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_2969_ = l_Lean_Name_num___override(v___x_2968_, v___x_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2971_ = ((lean_object*)(l___private_Lean_Meta_MethodSpecs_0__Lean_getMethodSpecsInfo___lam__1___closed__3));
v___x_2972_ = 0;
v___x_2973_ = lean_obj_once(&l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_, &l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_MethodSpecs_0__Lean_initFn___closed__12_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_);
v___x_2974_ = l_Lean_registerTraceClass(v___x_2971_, v___x_2972_, v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2____boxed(lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Lean_Meta_MethodSpecs_0__Lean_initFn_00___x40_Lean_Meta_MethodSpecs_2329740376____hygCtx___hyg_2_();
return v_res_2976_;
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
