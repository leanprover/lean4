// Lean compiler output
// Module: Lean.Meta.LazyDiscrTree
// Imports: public import Lean.Meta.CompletionName public import Lean.Meta.DiscrTree import Init.Omega
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_hasNoindexAnnotation(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isStrictImplicit(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_isClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkNoindexAnnotation(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint8_t l_Lean_getDiag(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* l_Lean_AsyncConstantInfo_ofConstantInfo(lean_object*);
uint8_t l_Lean_AsyncConstantInfo_isUnsafe(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternalDetail(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_BaseIO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_instReprLiteral_repr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getLocalConstantInfos(lean_object*, uint8_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_const_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_lit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_star_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_star_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_arrow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_arrow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_proj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instInhabitedKey_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedKey_default___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedKey_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedKey_default = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedKey_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedKey = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedKey_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_instBEqKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_instBEqKey___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instBEqKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_instBEqKey = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instBEqKey___closed__0_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.LazyDiscrTree.Key.arrow"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.LazyDiscrTree.Key.other"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__3 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.LazyDiscrTree.Key.star"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__4 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__5 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Meta.LazyDiscrTree.Key.const"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__6 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__7 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__7_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__8 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__8_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.LazyDiscrTree.Key.fvar"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__11 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__11_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__12 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__13 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__13_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.LazyDiscrTree.Key.lit"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__14 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__14_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__14_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__15 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__15_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__16 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__16_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.LazyDiscrTree.Key.proj"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__17 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__17_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__17_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__18 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__18_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__19 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_instReprKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_instReprKey_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instReprKey___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_LazyDiscrTree_Key_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_Key_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_Key_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_Key_instHashable___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_Key_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_Key_instHashable = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_Key_instHashable___closed__0_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "_discr_tree_tmp"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 72, 223, 190, 190, 84, 146, 120)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId___closed__1_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__0_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__1_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__3 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__3_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__4 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__4_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__6 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__6_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object*);
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__0_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__1_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__3 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__3_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__4 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__4_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__4_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2;
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_initCapacity;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_patternPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_pushArgs___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_patternPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_targetPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_targetPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new();
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionType"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3_value;
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6;
static const lean_array_object l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_InitResults_append, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Processing failure with "};
static const lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ":\n  "};
static const lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "lazy discriminator import initialization"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "build module discriminator tree"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "lazy discriminator local search"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_LazyDiscrTree_Key_ctorIdx(v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
switch(lean_obj_tag(v_t_11_))
{
case 0:
{
lean_object* v_a_13_; lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
v_a_14_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_14_);
lean_dec_ref_known(v_t_11_, 2);
v___x_15_ = lean_apply_2(v_k_12_, v_a_13_, v_a_14_);
return v___x_15_;
}
case 1:
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; 
v_a_16_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_17_);
lean_dec_ref_known(v_t_11_, 2);
v___x_18_ = lean_apply_2(v_k_12_, v_a_16_, v_a_17_);
return v___x_18_;
}
case 2:
{
lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_19_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_19_);
lean_dec_ref_known(v_t_11_, 1);
v___x_20_ = lean_apply_1(v_k_12_, v_a_19_);
return v___x_20_;
}
case 6:
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v_a_23_; lean_object* v___x_24_; 
v_a_21_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_21_);
v_a_22_ = lean_ctor_get(v_t_11_, 1);
lean_inc(v_a_22_);
v_a_23_ = lean_ctor_get(v_t_11_, 2);
lean_inc(v_a_23_);
lean_dec_ref_known(v_t_11_, 3);
v___x_24_ = lean_apply_3(v_k_12_, v_a_21_, v_a_22_, v_a_23_);
return v___x_24_;
}
default: 
{
lean_dec(v_t_11_);
return v_k_12_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_27_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_ctorElim___boxed(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim(v_motive_31_, v_ctorIdx_32_, v_t_33_, v_h_34_, v_k_35_);
lean_dec(v_ctorIdx_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_const_elim___redArg(lean_object* v_t_37_, lean_object* v_const_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_37_, v_const_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_const_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_const_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_41_, v_const_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_fvar_elim___redArg(lean_object* v_t_45_, lean_object* v_fvar_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_45_, v_fvar_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_fvar_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_fvar_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_49_, v_fvar_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_lit_elim___redArg(lean_object* v_t_53_, lean_object* v_lit_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_53_, v_lit_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_lit_elim(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_lit_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_57_, v_lit_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_star_elim___redArg(lean_object* v_t_61_, lean_object* v_star_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_61_, v_star_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_star_elim(lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_star_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_65_, v_star_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_other_elim___redArg(lean_object* v_t_69_, lean_object* v_other_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_69_, v_other_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_other_elim(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_other_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_73_, v_other_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_arrow_elim___redArg(lean_object* v_t_77_, lean_object* v_arrow_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_77_, v_arrow_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_arrow_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_arrow_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_81_, v_arrow_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_proj_elim___redArg(lean_object* v_t_85_, lean_object* v_proj_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_85_, v_proj_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_proj_elim(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_proj_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_LazyDiscrTree_Key_ctorElim___redArg(v_t_89_, v_proj_91_);
return v___x_92_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
switch(lean_obj_tag(v_x_98_))
{
case 0:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v_a_103_; uint8_t v___x_104_; 
v_a_100_ = lean_ctor_get(v_x_98_, 0);
v_a_101_ = lean_ctor_get(v_x_98_, 1);
v_a_102_ = lean_ctor_get(v_x_99_, 0);
v_a_103_ = lean_ctor_get(v_x_99_, 1);
v___x_104_ = lean_name_eq(v_a_100_, v_a_102_);
if (v___x_104_ == 0)
{
return v___x_104_;
}
else
{
uint8_t v___x_105_; 
v___x_105_ = lean_nat_dec_eq(v_a_101_, v_a_103_);
return v___x_105_;
}
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
case 1:
{
if (lean_obj_tag(v_x_99_) == 1)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v_a_110_; uint8_t v___x_111_; 
v_a_107_ = lean_ctor_get(v_x_98_, 0);
v_a_108_ = lean_ctor_get(v_x_98_, 1);
v_a_109_ = lean_ctor_get(v_x_99_, 0);
v_a_110_ = lean_ctor_get(v_x_99_, 1);
v___x_111_ = l_Lean_instBEqFVarId_beq(v_a_107_, v_a_109_);
if (v___x_111_ == 0)
{
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
v___x_112_ = lean_nat_dec_eq(v_a_108_, v_a_110_);
return v___x_112_;
}
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
case 2:
{
if (lean_obj_tag(v_x_99_) == 2)
{
lean_object* v_a_114_; lean_object* v_a_115_; uint8_t v___x_116_; 
v_a_114_ = lean_ctor_get(v_x_98_, 0);
v_a_115_ = lean_ctor_get(v_x_99_, 0);
v___x_116_ = l_Lean_instBEqLiteral_beq(v_a_114_, v_a_115_);
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
case 3:
{
if (lean_obj_tag(v_x_99_) == 3)
{
uint8_t v___x_118_; 
v___x_118_ = 1;
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
}
case 4:
{
if (lean_obj_tag(v_x_99_) == 4)
{
uint8_t v___x_120_; 
v___x_120_ = 1;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
case 5:
{
if (lean_obj_tag(v_x_99_) == 5)
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
default: 
{
if (lean_obj_tag(v_x_99_) == 6)
{
lean_object* v_a_124_; lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v_a_127_; lean_object* v_a_128_; lean_object* v_a_129_; uint8_t v___x_130_; 
v_a_124_ = lean_ctor_get(v_x_98_, 0);
v_a_125_ = lean_ctor_get(v_x_98_, 1);
v_a_126_ = lean_ctor_get(v_x_98_, 2);
v_a_127_ = lean_ctor_get(v_x_99_, 0);
v_a_128_ = lean_ctor_get(v_x_99_, 1);
v_a_129_ = lean_ctor_get(v_x_99_, 2);
v___x_130_ = lean_name_eq(v_a_124_, v_a_127_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = lean_nat_dec_eq(v_a_125_, v_a_128_);
if (v___x_131_ == 0)
{
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_eq(v_a_126_, v_a_129_);
return v___x_132_;
}
}
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instBEqKey_beq___boxed(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_x_134_, v_x_135_);
lean_dec(v_x_135_);
lean_dec(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(2u);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr(lean_object* v_x_177_, lean_object* v_prec_178_){
_start:
{
lean_object* v___y_180_; lean_object* v___y_187_; lean_object* v___y_194_; 
switch(lean_obj_tag(v_x_177_))
{
case 0:
{
lean_object* v_a_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_226_; 
v_a_200_ = lean_ctor_get(v_x_177_, 0);
v_a_201_ = lean_ctor_get(v_x_177_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_226_ == 0)
{
v___x_203_ = v_x_177_;
v_isShared_204_ = v_isSharedCheck_226_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_inc(v_a_200_);
lean_dec(v_x_177_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_226_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___y_206_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(1024u);
v___x_223_ = lean_nat_dec_le(v___x_222_, v_prec_178_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
v___x_224_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_206_ = v___x_224_;
goto v___jp_205_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_206_ = v___x_225_;
goto v___jp_205_;
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_207_ = lean_box(1);
v___x_208_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__8));
v___x_209_ = lean_unsigned_to_nat(1024u);
v___x_210_ = l_Lean_Name_reprPrec(v_a_200_, v___x_209_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 5);
lean_ctor_set(v___x_203_, 1, v___x_210_);
lean_ctor_set(v___x_203_, 0, v___x_208_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_221_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_207_);
v___x_214_ = l_Nat_reprFast(v_a_201_);
v___x_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_213_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
lean_inc(v___y_206_);
v___x_217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_217_, 0, v___y_206_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = 0;
v___x_219_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*1, v___x_218_);
v___x_220_ = l_Repr_addAppParen(v___x_219_, v_prec_178_);
return v___x_220_;
}
}
}
}
case 1:
{
lean_object* v_a_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_253_; 
v_a_227_ = lean_ctor_get(v_x_177_, 0);
v_a_228_ = lean_ctor_get(v_x_177_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_253_ == 0)
{
v___x_230_ = v_x_177_;
v_isShared_231_ = v_isSharedCheck_253_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_inc(v_a_227_);
lean_dec(v_x_177_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_253_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___y_233_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1024u);
v___x_250_ = lean_nat_dec_le(v___x_249_, v_prec_178_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_233_ = v___x_251_;
goto v___jp_232_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_233_ = v___x_252_;
goto v___jp_232_;
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_234_ = lean_box(1);
v___x_235_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__13));
v___x_236_ = lean_unsigned_to_nat(1024u);
v___x_237_ = l_Lean_Name_reprPrec(v_a_227_, v___x_236_);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 5);
lean_ctor_set(v___x_230_, 1, v___x_237_);
lean_ctor_set(v___x_230_, 0, v___x_235_);
v___x_239_ = v___x_230_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_248_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_234_);
v___x_241_ = l_Nat_reprFast(v_a_228_);
v___x_242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_240_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_inc(v___y_233_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___y_233_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_245_);
v___x_247_ = l_Repr_addAppParen(v___x_246_, v_prec_178_);
return v___x_247_;
}
}
}
}
case 2:
{
lean_object* v_a_254_; lean_object* v___y_256_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_a_254_ = lean_ctor_get(v_x_177_, 0);
lean_inc_ref(v_a_254_);
lean_dec_ref_known(v_x_177_, 1);
v___x_265_ = lean_unsigned_to_nat(1024u);
v___x_266_ = lean_nat_dec_le(v___x_265_, v_prec_178_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_256_ = v___x_267_;
goto v___jp_255_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_256_ = v___x_268_;
goto v___jp_255_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_257_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__16));
v___x_258_ = lean_unsigned_to_nat(1024u);
v___x_259_ = l_Lean_instReprLiteral_repr(v_a_254_, v___x_258_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_257_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_inc(v___y_256_);
v___x_261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_261_, 0, v___y_256_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = 0;
v___x_263_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*1, v___x_262_);
v___x_264_ = l_Repr_addAppParen(v___x_263_, v_prec_178_);
return v___x_264_;
}
}
case 3:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_prec_178_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_194_ = v___x_271_;
goto v___jp_193_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_194_ = v___x_272_;
goto v___jp_193_;
}
}
case 4:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1024u);
v___x_274_ = lean_nat_dec_le(v___x_273_, v_prec_178_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_187_ = v___x_275_;
goto v___jp_186_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_187_ = v___x_276_;
goto v___jp_186_;
}
}
case 5:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(1024u);
v___x_278_ = lean_nat_dec_le(v___x_277_, v_prec_178_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_180_ = v___x_279_;
goto v___jp_179_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_180_ = v___x_280_;
goto v___jp_179_;
}
}
default: 
{
lean_object* v_a_281_; lean_object* v_a_282_; lean_object* v_a_283_; lean_object* v___y_285_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_a_281_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_a_281_);
v_a_282_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_a_282_);
v_a_283_ = lean_ctor_get(v_x_177_, 2);
lean_inc(v_a_283_);
lean_dec_ref_known(v_x_177_, 3);
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_nat_dec_le(v___x_303_, v_prec_178_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__9);
v___y_285_ = v___x_305_;
goto v___jp_284_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10, &l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__10);
v___y_285_ = v___x_306_;
goto v___jp_284_;
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_286_ = lean_box(1);
v___x_287_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__19));
v___x_288_ = lean_unsigned_to_nat(1024u);
v___x_289_ = l_Lean_Name_reprPrec(v_a_281_, v___x_288_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_286_);
v___x_292_ = l_Nat_reprFast(v_a_282_);
v___x_293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_291_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_286_);
v___x_296_ = l_Nat_reprFast(v_a_283_);
v___x_297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_inc(v___y_285_);
v___x_299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_299_, 0, v___y_285_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = 0;
v___x_301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_300_);
v___x_302_ = l_Repr_addAppParen(v___x_301_, v_prec_178_);
return v___x_302_;
}
}
}
v___jp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_181_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__1));
lean_inc(v___y_180_);
v___x_182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_182_, 0, v___y_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = 0;
v___x_184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_183_);
v___x_185_ = l_Repr_addAppParen(v___x_184_, v_prec_178_);
return v___x_185_;
}
v___jp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_188_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__3));
lean_inc(v___y_187_);
v___x_189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_189_, 0, v___y_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = 0;
v___x_191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_190_);
v___x_192_ = l_Repr_addAppParen(v___x_191_, v_prec_178_);
return v___x_192_;
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_195_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instReprKey_repr___closed__5));
lean_inc(v___y_194_);
v___x_196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_196_, 0, v___y_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = 0;
v___x_198_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_197_);
v___x_199_ = l_Repr_addAppParen(v___x_198_, v_prec_178_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instReprKey_repr___boxed(lean_object* v_x_307_, lean_object* v_prec_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_LazyDiscrTree_instReprKey_repr(v_x_307_, v_prec_308_);
lean_dec(v_prec_308_);
return v_res_309_;
}
}
static uint64_t _init_l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0(void){
_start:
{
lean_object* v___x_312_; uint64_t v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1723u);
v___x_313_ = lean_uint64_of_nat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LazyDiscrTree_Key_hash(lean_object* v_x_314_){
_start:
{
switch(lean_obj_tag(v_x_314_))
{
case 0:
{
lean_object* v_a_315_; lean_object* v_a_316_; uint64_t v___x_317_; uint64_t v___y_319_; 
v_a_315_ = lean_ctor_get(v_x_314_, 0);
v_a_316_ = lean_ctor_get(v_x_314_, 1);
v___x_317_ = 5237ULL;
if (lean_obj_tag(v_a_315_) == 0)
{
uint64_t v___x_323_; 
v___x_323_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0, &l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0);
v___y_319_ = v___x_323_;
goto v___jp_318_;
}
else
{
uint64_t v_hash_324_; 
v_hash_324_ = lean_ctor_get_uint64(v_a_315_, sizeof(void*)*2);
v___y_319_ = v_hash_324_;
goto v___jp_318_;
}
v___jp_318_:
{
uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; 
v___x_320_ = lean_uint64_of_nat(v_a_316_);
v___x_321_ = lean_uint64_mix_hash(v___y_319_, v___x_320_);
v___x_322_ = lean_uint64_mix_hash(v___x_317_, v___x_321_);
return v___x_322_;
}
}
case 1:
{
lean_object* v_a_325_; lean_object* v_a_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; 
v_a_325_ = lean_ctor_get(v_x_314_, 0);
v_a_326_ = lean_ctor_get(v_x_314_, 1);
v___x_327_ = 3541ULL;
v___x_328_ = l_Lean_instHashableFVarId_hash(v_a_325_);
v___x_329_ = lean_uint64_of_nat(v_a_326_);
v___x_330_ = lean_uint64_mix_hash(v___x_328_, v___x_329_);
v___x_331_ = lean_uint64_mix_hash(v___x_327_, v___x_330_);
return v___x_331_;
}
case 2:
{
lean_object* v_a_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; 
v_a_332_ = lean_ctor_get(v_x_314_, 0);
v___x_333_ = 1879ULL;
v___x_334_ = l_Lean_Literal_hash(v_a_332_);
v___x_335_ = lean_uint64_mix_hash(v___x_333_, v___x_334_);
return v___x_335_;
}
case 3:
{
uint64_t v___x_336_; 
v___x_336_ = 7883ULL;
return v___x_336_;
}
case 4:
{
uint64_t v___x_337_; 
v___x_337_ = 2411ULL;
return v___x_337_;
}
case 5:
{
uint64_t v___x_338_; 
v___x_338_ = 17ULL;
return v___x_338_;
}
default: 
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v_a_341_; uint64_t v___x_342_; uint64_t v___y_344_; 
v_a_339_ = lean_ctor_get(v_x_314_, 0);
v_a_340_ = lean_ctor_get(v_x_314_, 1);
v_a_341_ = lean_ctor_get(v_x_314_, 2);
v___x_342_ = lean_uint64_of_nat(v_a_341_);
if (lean_obj_tag(v_a_339_) == 0)
{
uint64_t v___x_348_; 
v___x_348_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0, &l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0);
v___y_344_ = v___x_348_;
goto v___jp_343_;
}
else
{
uint64_t v_hash_349_; 
v_hash_349_ = lean_ctor_get_uint64(v_a_339_, sizeof(void*)*2);
v___y_344_ = v_hash_349_;
goto v___jp_343_;
}
v___jp_343_:
{
uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; 
v___x_345_ = lean_uint64_of_nat(v_a_340_);
v___x_346_ = lean_uint64_mix_hash(v___y_344_, v___x_345_);
v___x_347_ = lean_uint64_mix_hash(v___x_342_, v___x_346_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_hash___boxed(lean_object* v_x_350_){
_start:
{
uint64_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_x_350_);
lean_dec(v_x_350_);
v_r_352_ = lean_box_uint64(v_res_351_);
return v_r_352_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_360_ = l_Lean_mkMVar(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0, &l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(lean_object* v_a_362_, lean_object* v_i_363_, lean_object* v_infos_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_get_size(v_infos_364_);
v___x_384_ = lean_nat_dec_lt(v_i_363_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_isProof(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_385_;
}
else
{
lean_object* v_info_386_; uint8_t v_isInstance_387_; 
v_info_386_ = lean_array_fget_borrowed(v_infos_364_, v_i_363_);
v_isInstance_387_ = lean_ctor_get_uint8(v_info_386_, sizeof(void*)*1 + 4);
if (v_isInstance_387_ == 0)
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_386_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
v___x_389_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_386_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_isProof(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_390_;
}
else
{
goto v___jp_370_;
}
}
else
{
goto v___jp_370_;
}
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec_ref(v_a_362_);
v___x_391_ = lean_box(v_isInstance_387_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
v___jp_370_:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_isType(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_382_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_382_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_382_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_382_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint8_t v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_376_ = lean_unbox(v_a_372_);
lean_dec(v_a_372_);
v___x_377_ = lean_bool_not(v___x_376_);
v___x_378_ = lean_box(v___x_377_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_378_);
v___x_380_ = v___x_374_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg___boxed(lean_object* v_a_393_, lean_object* v_i_394_, lean_object* v_infos_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_a_393_, v_i_394_, v_infos_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec_ref(v_infos_395_);
lean_dec(v_i_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(lean_object* v_infos_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
if (lean_obj_tag(v_x_404_) == 5)
{
lean_object* v_fn_411_; lean_object* v_arg_412_; lean_object* v___x_413_; 
v_fn_411_ = lean_ctor_get(v_x_404_, 0);
lean_inc_ref(v_fn_411_);
v_arg_412_ = lean_ctor_get(v_x_404_, 1);
lean_inc_ref_n(v_arg_412_, 2);
lean_dec_ref_known(v_x_404_, 2);
v___x_413_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_arg_412_, v_x_403_, v_infos_402_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; uint8_t v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = lean_unbox(v_a_414_);
lean_dec(v_a_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_sub(v_x_403_, v___x_416_);
lean_dec(v_x_403_);
v___x_418_ = lean_array_push(v_x_405_, v_arg_412_);
v_x_403_ = v___x_417_;
v_x_404_ = v_fn_411_;
v_x_405_ = v___x_418_;
goto _start;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v_arg_412_);
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_sub(v_x_403_, v___x_420_);
lean_dec(v_x_403_);
v___x_422_ = l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar;
v___x_423_ = lean_array_push(v_x_405_, v___x_422_);
v_x_403_ = v___x_421_;
v_x_404_ = v_fn_411_;
v_x_405_ = v___x_423_;
goto _start;
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_arg_412_);
lean_dec_ref(v_fn_411_);
lean_dec_ref(v_x_405_);
lean_dec(v_x_403_);
v_a_425_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_413_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_413_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
lean_object* v___x_433_; 
lean_dec_ref(v_x_404_);
lean_dec(v_x_403_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_x_405_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux___boxed(lean_object* v_infos_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_infos_434_, v_x_435_, v_x_436_, v_x_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec_ref(v_infos_434_);
return v_res_443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(lean_object* v_e_458_){
_start:
{
uint8_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = l_Lean_Expr_isRawNatLit(v_e_458_);
v___x_460_ = 1;
if (v___x_459_ == 0)
{
lean_object* v_f_461_; uint8_t v___x_462_; uint8_t v___x_463_; 
v_f_461_ = l_Lean_Expr_getAppFn(v_e_458_);
v___x_462_ = l_Lean_Expr_isConst(v_f_461_);
v___x_463_ = lean_bool_not(v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v_fName_464_; uint8_t v___y_466_; uint8_t v___y_479_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_fName_464_ = l_Lean_Expr_constName_x21(v_f_461_);
lean_dec_ref(v_f_461_);
v___x_487_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_488_ = lean_name_eq(v_fName_464_, v___x_487_);
if (v___x_488_ == 0)
{
v___y_479_ = v___x_488_;
goto v___jp_478_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = l_Lean_Expr_getAppNumArgs(v_e_458_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_dec_eq(v___x_489_, v___x_490_);
lean_dec(v___x_489_);
v___y_479_ = v___x_491_;
goto v___jp_478_;
}
v___jp_465_:
{
if (v___y_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_468_ = lean_name_eq(v_fName_464_, v___x_467_);
lean_dec(v_fName_464_);
if (v___x_468_ == 0)
{
lean_dec_ref(v_e_458_);
if (v___x_468_ == 0)
{
return v___x_468_;
}
else
{
return v___x_460_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = l_Lean_Expr_getAppNumArgs(v_e_458_);
lean_dec_ref(v_e_458_);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_nat_dec_eq(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
return v___x_460_;
}
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_fName_464_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = l_Lean_Expr_getAppNumArgs(v_e_458_);
v___x_474_ = lean_nat_sub(v___x_473_, v___x_472_);
lean_dec(v___x_473_);
v___x_475_ = lean_nat_sub(v___x_474_, v___x_472_);
lean_dec(v___x_474_);
v___x_476_ = l_Lean_Expr_getRevArg_x21(v_e_458_, v___x_475_);
lean_dec_ref(v_e_458_);
v_e_458_ = v___x_476_;
goto _start;
}
}
v___jp_478_:
{
if (v___y_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_481_ = lean_name_eq(v_fName_464_, v___x_480_);
if (v___x_481_ == 0)
{
v___y_466_ = v___x_481_;
goto v___jp_465_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_482_ = l_Lean_Expr_getAppNumArgs(v_e_458_);
v___x_483_ = lean_unsigned_to_nat(3u);
v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
lean_dec(v___x_482_);
v___y_466_ = v___x_484_;
goto v___jp_465_;
}
}
else
{
lean_object* v___x_485_; 
lean_dec(v_fName_464_);
v___x_485_ = l_Lean_Expr_appArg_x21(v_e_458_);
lean_dec_ref(v_e_458_);
v_e_458_ = v___x_485_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_f_461_);
lean_dec_ref(v_e_458_);
return v___x_459_;
}
}
else
{
lean_dec_ref(v_e_458_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___boxed(lean_object* v_e_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(lean_object* v_e_497_){
_start:
{
uint8_t v___y_499_; lean_object* v_f_502_; 
v_f_502_ = l_Lean_Expr_getAppFn(v_e_497_);
switch(lean_obj_tag(v_f_502_))
{
case 9:
{
lean_object* v_a_503_; 
lean_dec_ref(v_e_497_);
v_a_503_ = lean_ctor_get(v_f_502_, 0);
lean_inc_ref(v_a_503_);
lean_dec_ref_known(v_f_502_, 1);
if (lean_obj_tag(v_a_503_) == 0)
{
lean_object* v_val_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_val_504_ = lean_ctor_get(v_a_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v_a_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_val_504_);
lean_dec(v_a_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 1);
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_val_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
lean_object* v___x_512_; 
lean_dec_ref(v_a_503_);
v___x_512_ = lean_box(0);
return v___x_512_;
}
}
case 4:
{
lean_object* v_declName_513_; uint8_t v___y_515_; uint8_t v___y_528_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_declName_513_ = lean_ctor_get(v_f_502_, 0);
lean_inc(v_declName_513_);
lean_dec_ref_known(v_f_502_, 2);
v___x_546_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_547_ = lean_name_eq(v_declName_513_, v___x_546_);
if (v___x_547_ == 0)
{
v___y_528_ = v___x_547_;
goto v___jp_527_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = l_Lean_Expr_getAppNumArgs(v_e_497_);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_dec_eq(v___x_548_, v___x_549_);
lean_dec(v___x_548_);
v___y_528_ = v___x_550_;
goto v___jp_527_;
}
v___jp_514_:
{
if (v___y_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_517_ = lean_name_eq(v_declName_513_, v___x_516_);
lean_dec(v_declName_513_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_e_497_);
v___y_499_ = v___x_517_;
goto v___jp_498_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = l_Lean_Expr_getAppNumArgs(v_e_497_);
lean_dec_ref(v_e_497_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_nat_dec_eq(v___x_518_, v___x_519_);
lean_dec(v___x_518_);
v___y_499_ = v___x_520_;
goto v___jp_498_;
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_declName_513_);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = l_Lean_Expr_getAppNumArgs(v_e_497_);
v___x_523_ = lean_nat_sub(v___x_522_, v___x_521_);
lean_dec(v___x_522_);
v___x_524_ = lean_nat_sub(v___x_523_, v___x_521_);
lean_dec(v___x_523_);
v___x_525_ = l_Lean_Expr_getRevArg_x21(v_e_497_, v___x_524_);
lean_dec_ref(v_e_497_);
v_e_497_ = v___x_525_;
goto _start;
}
}
v___jp_527_:
{
if (v___y_528_ == 0)
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_530_ = lean_name_eq(v_declName_513_, v___x_529_);
if (v___x_530_ == 0)
{
v___y_515_ = v___x_530_;
goto v___jp_514_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_531_ = l_Lean_Expr_getAppNumArgs(v_e_497_);
v___x_532_ = lean_unsigned_to_nat(3u);
v___x_533_ = lean_nat_dec_eq(v___x_531_, v___x_532_);
lean_dec(v___x_531_);
v___y_515_ = v___x_533_;
goto v___jp_514_;
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_declName_513_);
v___x_534_ = l_Lean_Expr_appArg_x21(v_e_497_);
lean_dec_ref(v_e_497_);
v___x_535_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v___x_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
return v___x_535_;
}
else
{
lean_object* v_val_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
v_val_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_val_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_val_536_, v___x_540_);
lean_dec(v_val_536_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_551_; 
lean_dec_ref(v_f_502_);
lean_dec_ref(v_e_497_);
v___x_551_ = lean_box(0);
return v___x_551_;
}
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_box(0);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0));
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object* v_e_552_){
_start:
{
uint8_t v___x_553_; 
lean_inc_ref(v_e_552_);
v___x_553_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec_ref(v_e_552_);
v___x_554_ = lean_box(0);
return v___x_554_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v_e_552_);
if (lean_obj_tag(v___x_555_) == 1)
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_564_; 
v_val_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_val_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v___x_565_; 
lean_dec(v___x_555_);
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; 
lean_inc(v_a_572_);
lean_inc_ref(v_a_571_);
lean_inc(v_a_570_);
lean_inc_ref(v_a_569_);
v___x_574_ = lean_whnf(v_e_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_585_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_585_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_579_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0));
v___x_580_ = l_Lean_Expr_isConstOf(v_a_575_, v___x_579_);
lean_dec(v_a_575_);
v___x_581_ = lean_box(v___x_580_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_581_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_574_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_574_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object* v_e_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v_e_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object* v_fName_614_, lean_object* v_e_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
uint8_t v___y_622_; uint8_t v___y_652_; uint8_t v___y_677_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6));
v___x_688_ = lean_name_eq(v_fName_614_, v___x_687_);
if (v___x_688_ == 0)
{
v___y_677_ = v___x_688_;
goto v___jp_676_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
v___x_690_ = lean_unsigned_to_nat(2u);
v___x_691_ = lean_nat_dec_eq(v___x_689_, v___x_690_);
lean_dec(v___x_689_);
v___y_677_ = v___x_691_;
goto v___jp_676_;
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_624_ = lean_name_eq(v_fName_614_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_box(v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_627_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_dec_eq(v___x_627_, v___x_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
v___x_634_ = lean_nat_sub(v___x_633_, v___x_632_);
lean_dec(v___x_633_);
v___x_635_ = lean_nat_sub(v___x_634_, v___x_632_);
lean_dec(v___x_634_);
v___x_636_ = l_Lean_Expr_getRevArg_x21(v_e_615_, v___x_635_);
v___x_637_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_636_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; uint8_t v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
v___x_639_ = lean_unbox(v_a_638_);
lean_dec(v_a_638_);
if (v___x_639_ == 0)
{
return v___x_637_;
}
else
{
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_649_; 
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v___x_637_, 0);
lean_dec(v_unused_650_);
v___x_641_ = v___x_637_;
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
else
{
lean_dec(v___x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_649_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_643_ = l_Lean_Expr_appArg_x21(v_e_615_);
v___x_644_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_643_);
v___x_645_ = lean_box(v___x_644_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_645_);
v___x_647_ = v___x_641_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
return v___x_637_;
}
}
}
v___jp_651_:
{
if (v___y_652_ == 0)
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2));
v___x_654_ = lean_name_eq(v_fName_614_, v___x_653_);
if (v___x_654_ == 0)
{
v___y_622_ = v___x_654_;
goto v___jp_621_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
v___x_656_ = lean_unsigned_to_nat(6u);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
lean_dec(v___x_655_);
v___y_622_ = v___x_657_;
goto v___jp_621_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_658_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_sub(v___x_658_, v___x_659_);
lean_dec(v___x_658_);
v___x_661_ = l_Lean_Expr_getRevArg_x21(v_e_615_, v___x_660_);
v___x_662_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_661_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; uint8_t v___x_664_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
v___x_664_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
if (v___x_664_ == 0)
{
return v___x_662_;
}
else
{
lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_674_; 
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_662_, 0);
lean_dec(v_unused_675_);
v___x_666_ = v___x_662_;
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
else
{
lean_dec(v___x_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_668_ = l_Lean_Expr_appArg_x21(v_e_615_);
v___x_669_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_668_);
v___x_670_ = lean_box(v___x_669_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_670_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
return v___x_662_;
}
}
}
v___jp_676_:
{
if (v___y_677_ == 0)
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5));
v___x_679_ = lean_name_eq(v_fName_614_, v___x_678_);
if (v___x_679_ == 0)
{
v___y_652_ = v___x_679_;
goto v___jp_651_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = l_Lean_Expr_getAppNumArgs(v_e_615_);
v___x_681_ = lean_unsigned_to_nat(4u);
v___x_682_ = lean_nat_dec_eq(v___x_680_, v___x_681_);
lean_dec(v___x_680_);
v___y_652_ = v___x_682_;
goto v___jp_651_;
}
}
else
{
lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = l_Lean_Expr_appArg_x21(v_e_615_);
v___x_684_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_683_);
v___x_685_ = lean_box(v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object* v_fName_692_, lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_692_, v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec_ref(v_e_693_);
lean_dec(v_fName_692_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object* v_fName_700_, lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_700_, v_e_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object* v_fName_708_, lean_object* v_e_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(v_fName_708_, v_e_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec_ref(v_e_709_);
lean_dec(v_fName_708_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object* v_e_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = l_Lean_Expr_hasLooseBVars(v_e_718_);
v___x_723_ = lean_bool_not(v___x_722_);
if (v___x_723_ == 0)
{
uint8_t v___x_724_; 
v___x_724_ = l_Lean_Expr_isHeadBetaTarget(v_e_718_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v_e_718_);
v___x_725_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0));
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_Expr_headBeta(v_e_718_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_e_718_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object* v_e_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(v_e_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object* v_e_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_e_737_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object* v_e_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(v_e_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_747_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_interruptExceptionId;
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_755_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = l_Lean_maxRecDepthErrorMessage;
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_764_ = l_Lean_MessageData_ofFormat(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_766_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_767_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_768_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_ref_768_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___y_782_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; uint8_t v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v_fileName_814_; lean_object* v_fileMap_815_; lean_object* v_options_816_; lean_object* v_currRecDepth_817_; lean_object* v_maxRecDepth_818_; lean_object* v_ref_819_; lean_object* v_currNamespace_820_; lean_object* v_openDecls_821_; lean_object* v_initHeartbeats_822_; lean_object* v_maxHeartbeats_823_; lean_object* v_quotContext_824_; lean_object* v_currMacroScope_825_; uint8_t v_diag_826_; lean_object* v_cancelTk_x3f_827_; uint8_t v_suppressElabErrors_828_; lean_object* v_inheritedTraceOptions_829_; 
v_fileName_814_ = lean_ctor_get(v___y_778_, 0);
v_fileMap_815_ = lean_ctor_get(v___y_778_, 1);
v_options_816_ = lean_ctor_get(v___y_778_, 2);
v_currRecDepth_817_ = lean_ctor_get(v___y_778_, 3);
v_maxRecDepth_818_ = lean_ctor_get(v___y_778_, 4);
v_ref_819_ = lean_ctor_get(v___y_778_, 5);
v_currNamespace_820_ = lean_ctor_get(v___y_778_, 6);
v_openDecls_821_ = lean_ctor_get(v___y_778_, 7);
v_initHeartbeats_822_ = lean_ctor_get(v___y_778_, 8);
v_maxHeartbeats_823_ = lean_ctor_get(v___y_778_, 9);
v_quotContext_824_ = lean_ctor_get(v___y_778_, 10);
v_currMacroScope_825_ = lean_ctor_get(v___y_778_, 11);
v_diag_826_ = lean_ctor_get_uint8(v___y_778_, sizeof(void*)*14);
v_cancelTk_x3f_827_ = lean_ctor_get(v___y_778_, 12);
v_suppressElabErrors_828_ = lean_ctor_get_uint8(v___y_778_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_829_ = lean_ctor_get(v___y_778_, 13);
if (lean_obj_tag(v_cancelTk_x3f_827_) == 1)
{
lean_object* v_val_835_; uint8_t v___x_836_; 
v_val_835_ = lean_ctor_get(v_cancelTk_x3f_827_, 0);
v___x_836_ = l_IO_CancelToken_isSet(v_val_835_);
if (v___x_836_ == 0)
{
goto v___jp_830_;
}
else
{
lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v_x_776_);
v___x_837_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
goto v___jp_830_;
}
v___jp_781_:
{
if (lean_obj_tag(v___y_782_) == 0)
{
return v___y_782_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___y_782_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___y_782_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___y_782_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___y_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
v___jp_791_:
{
if (v___y_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v___y_800_, v___x_809_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_798_);
lean_inc(v___y_793_);
lean_inc(v___y_803_);
lean_inc(v___y_806_);
lean_inc(v___y_797_);
lean_inc(v___y_794_);
lean_inc(v___y_796_);
lean_inc(v___y_795_);
lean_inc(v___y_801_);
lean_inc_ref(v___y_804_);
lean_inc_ref(v___y_792_);
lean_inc_ref(v___y_799_);
v___x_811_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_811_, 0, v___y_799_);
lean_ctor_set(v___x_811_, 1, v___y_792_);
lean_ctor_set(v___x_811_, 2, v___y_804_);
lean_ctor_set(v___x_811_, 3, v___x_810_);
lean_ctor_set(v___x_811_, 4, v___y_801_);
lean_ctor_set(v___x_811_, 5, v___y_795_);
lean_ctor_set(v___x_811_, 6, v___y_796_);
lean_ctor_set(v___x_811_, 7, v___y_794_);
lean_ctor_set(v___x_811_, 8, v___y_797_);
lean_ctor_set(v___x_811_, 9, v___y_806_);
lean_ctor_set(v___x_811_, 10, v___y_803_);
lean_ctor_set(v___x_811_, 11, v___y_793_);
lean_ctor_set(v___x_811_, 12, v___y_798_);
lean_ctor_set(v___x_811_, 13, v___y_807_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14, v___y_805_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*14 + 1, v___y_802_);
lean_inc(v___y_779_);
lean_inc(v___y_777_);
v___x_812_ = lean_apply_4(v_x_776_, v___y_777_, v___x_811_, v___y_779_, lean_box(0));
v___y_782_ = v___x_812_;
goto v___jp_781_;
}
else
{
lean_object* v___x_813_; 
lean_dec_ref(v_x_776_);
lean_inc(v___y_795_);
v___x_813_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v___y_795_);
v___y_782_ = v___x_813_;
goto v___jp_781_;
}
}
v___jp_830_:
{
lean_object* v___x_831_; uint8_t v___x_832_; uint8_t v___x_833_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_nat_dec_eq(v_maxRecDepth_818_, v___x_831_);
v___x_833_ = lean_bool_not(v___x_832_);
if (v___x_833_ == 0)
{
v___y_792_ = v_fileMap_815_;
v___y_793_ = v_currMacroScope_825_;
v___y_794_ = v_openDecls_821_;
v___y_795_ = v_ref_819_;
v___y_796_ = v_currNamespace_820_;
v___y_797_ = v_initHeartbeats_822_;
v___y_798_ = v_cancelTk_x3f_827_;
v___y_799_ = v_fileName_814_;
v___y_800_ = v_currRecDepth_817_;
v___y_801_ = v_maxRecDepth_818_;
v___y_802_ = v_suppressElabErrors_828_;
v___y_803_ = v_quotContext_824_;
v___y_804_ = v_options_816_;
v___y_805_ = v_diag_826_;
v___y_806_ = v_maxHeartbeats_823_;
v___y_807_ = v_inheritedTraceOptions_829_;
v___y_808_ = v___x_833_;
goto v___jp_791_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_eq(v_currRecDepth_817_, v_maxRecDepth_818_);
v___y_792_ = v_fileMap_815_;
v___y_793_ = v_currMacroScope_825_;
v___y_794_ = v_openDecls_821_;
v___y_795_ = v_ref_819_;
v___y_796_ = v_currNamespace_820_;
v___y_797_ = v_initHeartbeats_822_;
v___y_798_ = v_cancelTk_x3f_827_;
v___y_799_ = v_fileName_814_;
v___y_800_ = v_currRecDepth_817_;
v___y_801_ = v_maxRecDepth_818_;
v___y_802_ = v_suppressElabErrors_828_;
v___y_803_ = v_quotContext_824_;
v___y_804_ = v_options_816_;
v___y_805_ = v_diag_826_;
v___y_806_ = v_maxHeartbeats_823_;
v___y_807_ = v_inheritedTraceOptions_829_;
v___y_808_ = v___x_834_;
goto v___jp_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_box(0);
return v___x_854_;
}
else
{
lean_object* v_key_855_; lean_object* v_value_856_; lean_object* v_tail_857_; uint8_t v___x_858_; 
v_key_855_ = lean_ctor_get(v_x_853_, 0);
v_value_856_ = lean_ctor_get(v_x_853_, 1);
v_tail_857_ = lean_ctor_get(v_x_853_, 2);
v___x_858_ = l_Lean_ExprStructEq_beq(v_key_855_, v_a_852_);
if (v___x_858_ == 0)
{
v_x_853_ = v_tail_857_;
goto _start;
}
else
{
lean_object* v___x_860_; 
lean_inc(v_value_856_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_value_856_);
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_861_, lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_861_, v_x_862_);
lean_dec(v_x_862_);
lean_dec_ref(v_a_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_buckets_866_; lean_object* v___x_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; uint64_t v_fold_871_; uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_buckets_866_ = lean_ctor_get(v_m_864_, 1);
v___x_867_ = lean_array_get_size(v_buckets_866_);
v___x_868_ = l_Lean_ExprStructEq_hash(v_a_865_);
v___x_869_ = 32ULL;
v___x_870_ = lean_uint64_shift_right(v___x_868_, v___x_869_);
v_fold_871_ = lean_uint64_xor(v___x_868_, v___x_870_);
v___x_872_ = 16ULL;
v___x_873_ = lean_uint64_shift_right(v_fold_871_, v___x_872_);
v___x_874_ = lean_uint64_xor(v_fold_871_, v___x_873_);
v___x_875_ = lean_uint64_to_usize(v___x_874_);
v___x_876_ = lean_usize_of_nat(v___x_867_);
v___x_877_ = ((size_t)1ULL);
v___x_878_ = lean_usize_sub(v___x_876_, v___x_877_);
v___x_879_ = lean_usize_land(v___x_875_, v___x_878_);
v___x_880_ = lean_array_uget_borrowed(v_buckets_866_, v___x_879_);
v___x_881_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_865_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_882_, v_a_883_);
lean_dec_ref(v_a_883_);
lean_dec_ref(v_m_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_885_, lean_object* v_b_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_dec(v_b_886_);
lean_dec_ref(v_a_885_);
return v_x_887_;
}
else
{
lean_object* v_key_888_; lean_object* v_value_889_; lean_object* v_tail_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_902_; 
v_key_888_ = lean_ctor_get(v_x_887_, 0);
v_value_889_ = lean_ctor_get(v_x_887_, 1);
v_tail_890_ = lean_ctor_get(v_x_887_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_902_ == 0)
{
v___x_892_ = v_x_887_;
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_tail_890_);
lean_inc(v_value_889_);
lean_inc(v_key_888_);
lean_dec(v_x_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = l_Lean_ExprStructEq_beq(v_key_888_, v_a_885_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_885_, v_b_886_, v_tail_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 2, v___x_895_);
v___x_897_ = v___x_892_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_key_888_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_value_889_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_object* v___x_900_; 
lean_dec(v_value_889_);
lean_dec(v_key_888_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v_b_886_);
lean_ctor_set(v___x_892_, 0, v_a_885_);
v___x_900_ = v___x_892_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_b_886_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_tail_890_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
return v_x_903_;
}
else
{
lean_object* v_key_905_; lean_object* v_value_906_; lean_object* v_tail_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_930_; 
v_key_905_ = lean_ctor_get(v_x_904_, 0);
v_value_906_ = lean_ctor_get(v_x_904_, 1);
v_tail_907_ = lean_ctor_get(v_x_904_, 2);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_930_ == 0)
{
v___x_909_ = v_x_904_;
v_isShared_910_ = v_isSharedCheck_930_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_tail_907_);
lean_inc(v_value_906_);
lean_inc(v_key_905_);
lean_dec(v_x_904_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_930_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v_fold_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_911_ = lean_array_get_size(v_x_903_);
v___x_912_ = l_Lean_ExprStructEq_hash(v_key_905_);
v___x_913_ = 32ULL;
v___x_914_ = lean_uint64_shift_right(v___x_912_, v___x_913_);
v_fold_915_ = lean_uint64_xor(v___x_912_, v___x_914_);
v___x_916_ = 16ULL;
v___x_917_ = lean_uint64_shift_right(v_fold_915_, v___x_916_);
v___x_918_ = lean_uint64_xor(v_fold_915_, v___x_917_);
v___x_919_ = lean_uint64_to_usize(v___x_918_);
v___x_920_ = lean_usize_of_nat(v___x_911_);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_sub(v___x_920_, v___x_921_);
v___x_923_ = lean_usize_land(v___x_919_, v___x_922_);
v___x_924_ = lean_array_uget_borrowed(v_x_903_, v___x_923_);
lean_inc(v___x_924_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 2, v___x_924_);
v___x_926_ = v___x_909_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_key_905_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_value_906_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v___x_924_);
v___x_926_ = v_reuseFailAlloc_929_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; 
v___x_927_ = lean_array_uset(v_x_903_, v___x_923_, v___x_926_);
v_x_903_ = v___x_927_;
v_x_904_ = v_tail_907_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_931_, lean_object* v_source_932_, lean_object* v_target_933_){
_start:
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_array_get_size(v_source_932_);
v___x_935_ = lean_nat_dec_lt(v_i_931_, v___x_934_);
if (v___x_935_ == 0)
{
lean_dec_ref(v_source_932_);
lean_dec(v_i_931_);
return v_target_933_;
}
else
{
lean_object* v_es_936_; lean_object* v___x_937_; lean_object* v_source_938_; lean_object* v_target_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_es_936_ = lean_array_fget(v_source_932_, v_i_931_);
v___x_937_ = lean_box(0);
v_source_938_ = lean_array_fset(v_source_932_, v_i_931_, v___x_937_);
v_target_939_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_933_, v_es_936_);
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_add(v_i_931_, v___x_940_);
lean_dec(v_i_931_);
v_i_931_ = v___x_941_;
v_source_932_ = v_source_938_;
v_target_933_ = v_target_939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_943_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_nbuckets_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_944_ = lean_array_get_size(v_data_943_);
v___x_945_ = lean_unsigned_to_nat(2u);
v_nbuckets_946_ = lean_nat_mul(v___x_944_, v___x_945_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_box(0);
v___x_949_ = lean_mk_array(v_nbuckets_946_, v___x_948_);
v___x_950_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_947_, v_data_943_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_951_, lean_object* v_x_952_){
_start:
{
if (lean_obj_tag(v_x_952_) == 0)
{
uint8_t v___x_953_; 
v___x_953_ = 0;
return v___x_953_;
}
else
{
lean_object* v_key_954_; lean_object* v_tail_955_; uint8_t v___x_956_; 
v_key_954_ = lean_ctor_get(v_x_952_, 0);
v_tail_955_ = lean_ctor_get(v_x_952_, 2);
v___x_956_ = l_Lean_ExprStructEq_beq(v_key_954_, v_a_951_);
if (v___x_956_ == 0)
{
v_x_952_ = v_tail_955_;
goto _start;
}
else
{
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_958_, lean_object* v_x_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_958_, v_x_959_);
lean_dec(v_x_959_);
lean_dec_ref(v_a_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_962_, lean_object* v_a_963_, lean_object* v_b_964_){
_start:
{
lean_object* v_size_965_; lean_object* v_buckets_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1009_; 
v_size_965_ = lean_ctor_get(v_m_962_, 0);
v_buckets_966_ = lean_ctor_get(v_m_962_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_m_962_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_968_ = v_m_962_;
v_isShared_969_ = v_isSharedCheck_1009_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_buckets_966_);
lean_inc(v_size_965_);
lean_dec(v_m_962_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1009_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v_fold_974_; uint64_t v___x_975_; uint64_t v___x_976_; uint64_t v___x_977_; size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v_bkt_983_; uint8_t v___x_984_; 
v___x_970_ = lean_array_get_size(v_buckets_966_);
v___x_971_ = l_Lean_ExprStructEq_hash(v_a_963_);
v___x_972_ = 32ULL;
v___x_973_ = lean_uint64_shift_right(v___x_971_, v___x_972_);
v_fold_974_ = lean_uint64_xor(v___x_971_, v___x_973_);
v___x_975_ = 16ULL;
v___x_976_ = lean_uint64_shift_right(v_fold_974_, v___x_975_);
v___x_977_ = lean_uint64_xor(v_fold_974_, v___x_976_);
v___x_978_ = lean_uint64_to_usize(v___x_977_);
v___x_979_ = lean_usize_of_nat(v___x_970_);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_sub(v___x_979_, v___x_980_);
v___x_982_ = lean_usize_land(v___x_978_, v___x_981_);
v_bkt_983_ = lean_array_uget_borrowed(v_buckets_966_, v___x_982_);
v___x_984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_963_, v_bkt_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v_size_x27_986_; lean_object* v___x_987_; lean_object* v_buckets_x27_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v_size_x27_986_ = lean_nat_add(v_size_965_, v___x_985_);
lean_dec(v_size_965_);
lean_inc(v_bkt_983_);
v___x_987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_987_, 0, v_a_963_);
lean_ctor_set(v___x_987_, 1, v_b_964_);
lean_ctor_set(v___x_987_, 2, v_bkt_983_);
v_buckets_x27_988_ = lean_array_uset(v_buckets_966_, v___x_982_, v___x_987_);
v___x_989_ = lean_unsigned_to_nat(4u);
v___x_990_ = lean_nat_mul(v_size_x27_986_, v___x_989_);
v___x_991_ = lean_unsigned_to_nat(3u);
v___x_992_ = lean_nat_div(v___x_990_, v___x_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_array_get_size(v_buckets_x27_988_);
v___x_994_ = lean_nat_dec_le(v___x_992_, v___x_993_);
lean_dec(v___x_992_);
if (v___x_994_ == 0)
{
lean_object* v_val_995_; lean_object* v___x_997_; 
v_val_995_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_988_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_val_995_);
lean_ctor_set(v___x_968_, 0, v_size_x27_986_);
v___x_997_ = v___x_968_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_size_x27_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_val_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
lean_object* v___x_1000_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_buckets_x27_988_);
lean_ctor_set(v___x_968_, 0, v_size_x27_986_);
v___x_1000_ = v___x_968_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_size_x27_986_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_buckets_x27_988_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
else
{
lean_object* v___x_1002_; lean_object* v_buckets_x27_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_inc(v_bkt_983_);
v___x_1002_ = lean_box(0);
v_buckets_x27_1003_ = lean_array_uset(v_buckets_966_, v___x_982_, v___x_1002_);
v___x_1004_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_963_, v_b_964_, v_bkt_983_);
v___x_1005_ = lean_array_uset(v_buckets_x27_1003_, v___x_982_, v___x_1004_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v___x_1005_);
v___x_1007_ = v___x_968_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_size_965_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_1010_, lean_object* v_e_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = lean_st_ref_take(v_a_1010_);
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_1014_, v_e_1011_, v_a_1012_);
v___x_1016_ = lean_st_ref_set(v_a_1010_, v___x_1015_);
v___x_1017_ = lean_box(0);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1018_, lean_object* v_e_1019_, lean_object* v_a_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_1018_, v_e_1019_, v_a_1020_);
lean_dec(v_a_1018_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_apply_1(v_x_1024_, lean_box(0));
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1030_, v_x_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1037_; lean_object* v_dummy_1038_; 
v___x_1037_ = lean_box(0);
v_dummy_1038_ = l_Lean_Expr_sort___override(v___x_1037_);
return v_dummy_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1039_, lean_object* v_post_1040_, size_t v_sz_1041_, size_t v_i_1042_, lean_object* v_bs_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_usize_dec_lt(v_i_1042_, v_sz_1041_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec_ref(v_post_1040_);
lean_dec_ref(v_pre_1039_);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_bs_1043_);
return v___x_1049_;
}
else
{
lean_object* v_v_1050_; lean_object* v___x_1051_; 
v_v_1050_ = lean_array_uget_borrowed(v_bs_1043_, v_i_1042_);
lean_inc(v_v_1050_);
lean_inc_ref(v_post_1040_);
lean_inc_ref(v_pre_1039_);
v___x_1051_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1039_, v_post_1040_, v_v_1050_, v___y_1044_, v___y_1045_, v___y_1046_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v_bs_x27_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = lean_unsigned_to_nat(0u);
v_bs_x27_1054_ = lean_array_uset(v_bs_1043_, v_i_1042_, v___x_1053_);
v___x_1055_ = ((size_t)1ULL);
v___x_1056_ = lean_usize_add(v_i_1042_, v___x_1055_);
v___x_1057_ = lean_array_uset(v_bs_x27_1054_, v_i_1042_, v_a_1052_);
v_i_1042_ = v___x_1056_;
v_bs_1043_ = v___x_1057_;
goto _start;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_bs_1043_);
lean_dec_ref(v_post_1040_);
lean_dec_ref(v_pre_1039_);
v_a_1059_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1051_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1051_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1067_, lean_object* v_post_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
if (lean_obj_tag(v_x_1069_) == 5)
{
lean_object* v_fn_1076_; lean_object* v_arg_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_fn_1076_ = lean_ctor_get(v_x_1069_, 0);
lean_inc_ref(v_fn_1076_);
v_arg_1077_ = lean_ctor_get(v_x_1069_, 1);
lean_inc_ref(v_arg_1077_);
lean_dec_ref_known(v_x_1069_, 2);
v___x_1078_ = lean_array_set(v_x_1070_, v_x_1071_, v_arg_1077_);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_sub(v_x_1071_, v___x_1079_);
lean_dec(v_x_1071_);
v_x_1069_ = v_fn_1076_;
v_x_1070_ = v___x_1078_;
v_x_1071_ = v___x_1080_;
goto _start;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_x_1071_);
lean_inc_ref(v_post_1068_);
lean_inc_ref(v_pre_1067_);
v___x_1082_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1067_, v_post_1068_, v_x_1069_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; size_t v_sz_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v_sz_1084_ = lean_array_size(v_x_1070_);
v___x_1085_ = ((size_t)0ULL);
lean_inc_ref(v_post_1068_);
lean_inc_ref(v_pre_1067_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1067_, v_post_1068_, v_sz_1084_, v___x_1085_, v_x_1070_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l_Lean_mkAppN(v_a_1083_, v_a_1087_);
lean_dec(v_a_1087_);
v___x_1089_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1067_, v_post_1068_, v___x_1088_, v___y_1072_, v___y_1073_, v___y_1074_);
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1083_);
lean_dec_ref(v_post_1068_);
lean_dec_ref(v_pre_1067_);
v_a_1090_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1086_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1086_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
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
else
{
lean_dec_ref(v_x_1070_);
lean_dec_ref(v_post_1068_);
lean_dec_ref(v_pre_1067_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1098_, lean_object* v_pre_1099_, lean_object* v_e_1100_, lean_object* v_post_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___y_1141_; uint8_t v___y_1142_; lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Core_checkSystem(v___x_1098_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1150_; 
lean_dec_ref_known(v___x_1149_, 1);
lean_inc_ref(v_pre_1099_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1103_);
lean_inc_ref(v_e_1100_);
v___x_1150_ = lean_apply_4(v_pre_1099_, v_e_1100_, v___y_1103_, v___y_1104_, lean_box(0));
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1240_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1240_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1240_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___y_1156_; 
switch(lean_obj_tag(v_a_1151_))
{
case 0:
{
lean_object* v_e_1230_; lean_object* v___x_1232_; 
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_e_1100_);
lean_dec_ref(v_pre_1099_);
v_e_1230_ = lean_ctor_get(v_a_1151_, 0);
lean_inc_ref(v_e_1230_);
lean_dec_ref_known(v_a_1151_, 1);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_e_1230_);
v___x_1232_ = v___x_1153_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_e_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
case 1:
{
lean_object* v_e_1234_; lean_object* v___x_1235_; 
lean_del_object(v___x_1153_);
lean_dec_ref(v_e_1100_);
v_e_1234_ = lean_ctor_get(v_a_1151_, 0);
lean_inc_ref(v_e_1234_);
lean_dec_ref_known(v_a_1151_, 1);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1235_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_e_1234_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1237_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v_a_1236_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1237_;
}
else
{
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1235_;
}
}
default: 
{
lean_object* v_e_x3f_1238_; 
lean_del_object(v___x_1153_);
v_e_x3f_1238_ = lean_ctor_get(v_a_1151_, 0);
lean_inc(v_e_x3f_1238_);
lean_dec_ref_known(v_a_1151_, 1);
if (lean_obj_tag(v_e_x3f_1238_) == 0)
{
v___y_1156_ = v_e_1100_;
goto v___jp_1155_;
}
else
{
lean_object* v_val_1239_; 
lean_dec_ref(v_e_1100_);
v_val_1239_ = lean_ctor_get(v_e_x3f_1238_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v_e_x3f_1238_, 1);
v___y_1156_ = v_val_1239_;
goto v___jp_1155_;
}
}
}
v___jp_1155_:
{
switch(lean_obj_tag(v___y_1156_))
{
case 7:
{
lean_object* v_binderName_1157_; lean_object* v_binderType_1158_; lean_object* v_body_1159_; uint8_t v_binderInfo_1160_; lean_object* v___x_1161_; 
v_binderName_1157_ = lean_ctor_get(v___y_1156_, 0);
lean_inc(v_binderName_1157_);
v_binderType_1158_ = lean_ctor_get(v___y_1156_, 1);
v_body_1159_ = lean_ctor_get(v___y_1156_, 2);
v_binderInfo_1160_ = lean_ctor_get_uint8(v___y_1156_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1158_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1161_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_binderType_1158_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
lean_inc_ref(v_body_1159_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_body_1159_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; size_t v___x_1165_; size_t v___x_1166_; uint8_t v___x_1167_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = lean_ptr_addr(v_binderType_1158_);
v___x_1166_ = lean_ptr_addr(v_a_1162_);
v___x_1167_ = lean_usize_dec_eq(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
v___y_1137_ = v_a_1164_;
v___y_1138_ = v___y_1156_;
v___y_1139_ = v_a_1162_;
v___y_1140_ = v_binderName_1157_;
v___y_1141_ = v_binderInfo_1160_;
v___y_1142_ = v___x_1167_;
goto v___jp_1136_;
}
else
{
size_t v___x_1168_; size_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_ptr_addr(v_body_1159_);
v___x_1169_ = lean_ptr_addr(v_a_1164_);
v___x_1170_ = lean_usize_dec_eq(v___x_1168_, v___x_1169_);
v___y_1137_ = v_a_1164_;
v___y_1138_ = v___y_1156_;
v___y_1139_ = v_a_1162_;
v___y_1140_ = v_binderName_1157_;
v___y_1141_ = v_binderInfo_1160_;
v___y_1142_ = v___x_1170_;
goto v___jp_1136_;
}
}
else
{
lean_dec(v_a_1162_);
lean_dec_ref_known(v___y_1156_, 3);
lean_dec(v_binderName_1157_);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1163_;
}
}
else
{
lean_dec_ref_known(v___y_1156_, 3);
lean_dec(v_binderName_1157_);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1161_;
}
}
case 6:
{
lean_object* v_binderName_1171_; lean_object* v_binderType_1172_; lean_object* v_body_1173_; uint8_t v_binderInfo_1174_; lean_object* v___x_1175_; 
v_binderName_1171_ = lean_ctor_get(v___y_1156_, 0);
lean_inc(v_binderName_1171_);
v_binderType_1172_ = lean_ctor_get(v___y_1156_, 1);
v_body_1173_ = lean_ctor_get(v___y_1156_, 2);
v_binderInfo_1174_ = lean_ctor_get_uint8(v___y_1156_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1172_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_binderType_1172_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
lean_inc_ref(v_body_1173_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1177_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_body_1173_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; size_t v___x_1179_; size_t v___x_1180_; uint8_t v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_ptr_addr(v_binderType_1172_);
v___x_1180_ = lean_ptr_addr(v_a_1176_);
v___x_1181_ = lean_usize_dec_eq(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
v___y_1124_ = v_a_1176_;
v___y_1125_ = v_a_1178_;
v___y_1126_ = v___y_1156_;
v___y_1127_ = v_binderName_1171_;
v___y_1128_ = v_binderInfo_1174_;
v___y_1129_ = v___x_1181_;
goto v___jp_1123_;
}
else
{
size_t v___x_1182_; size_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = lean_ptr_addr(v_body_1173_);
v___x_1183_ = lean_ptr_addr(v_a_1178_);
v___x_1184_ = lean_usize_dec_eq(v___x_1182_, v___x_1183_);
v___y_1124_ = v_a_1176_;
v___y_1125_ = v_a_1178_;
v___y_1126_ = v___y_1156_;
v___y_1127_ = v_binderName_1171_;
v___y_1128_ = v_binderInfo_1174_;
v___y_1129_ = v___x_1184_;
goto v___jp_1123_;
}
}
else
{
lean_dec(v_a_1176_);
lean_dec(v_binderName_1171_);
lean_dec_ref_known(v___y_1156_, 3);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1177_;
}
}
else
{
lean_dec_ref_known(v___y_1156_, 3);
lean_dec(v_binderName_1171_);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1175_;
}
}
case 8:
{
lean_object* v_declName_1185_; lean_object* v_type_1186_; lean_object* v_value_1187_; lean_object* v_body_1188_; uint8_t v_nondep_1189_; lean_object* v___x_1190_; 
v_declName_1185_ = lean_ctor_get(v___y_1156_, 0);
lean_inc(v_declName_1185_);
v_type_1186_ = lean_ctor_get(v___y_1156_, 1);
v_value_1187_ = lean_ctor_get(v___y_1156_, 2);
v_body_1188_ = lean_ctor_get(v___y_1156_, 3);
lean_inc_ref(v_body_1188_);
v_nondep_1189_ = lean_ctor_get_uint8(v___y_1156_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1186_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_type_1186_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
lean_inc_ref(v_value_1187_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1192_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_value_1187_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
lean_inc_ref(v_body_1188_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1194_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_body_1188_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; size_t v___x_1196_; size_t v___x_1197_; uint8_t v___x_1198_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = lean_ptr_addr(v_type_1186_);
v___x_1197_ = lean_ptr_addr(v_a_1191_);
v___x_1198_ = lean_usize_dec_eq(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
v___y_1107_ = v_a_1193_;
v___y_1108_ = v_declName_1185_;
v___y_1109_ = v_a_1195_;
v___y_1110_ = v_a_1191_;
v___y_1111_ = v___y_1156_;
v___y_1112_ = v_body_1188_;
v___y_1113_ = v_nondep_1189_;
v___y_1114_ = v___x_1198_;
goto v___jp_1106_;
}
else
{
size_t v___x_1199_; size_t v___x_1200_; uint8_t v___x_1201_; 
v___x_1199_ = lean_ptr_addr(v_value_1187_);
v___x_1200_ = lean_ptr_addr(v_a_1193_);
v___x_1201_ = lean_usize_dec_eq(v___x_1199_, v___x_1200_);
v___y_1107_ = v_a_1193_;
v___y_1108_ = v_declName_1185_;
v___y_1109_ = v_a_1195_;
v___y_1110_ = v_a_1191_;
v___y_1111_ = v___y_1156_;
v___y_1112_ = v_body_1188_;
v___y_1113_ = v_nondep_1189_;
v___y_1114_ = v___x_1201_;
goto v___jp_1106_;
}
}
else
{
lean_dec(v_a_1193_);
lean_dec(v_a_1191_);
lean_dec_ref(v_body_1188_);
lean_dec_ref_known(v___y_1156_, 4);
lean_dec(v_declName_1185_);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1194_;
}
}
else
{
lean_dec(v_a_1191_);
lean_dec_ref(v_body_1188_);
lean_dec(v_declName_1185_);
lean_dec_ref_known(v___y_1156_, 4);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1192_;
}
}
else
{
lean_dec_ref(v_body_1188_);
lean_dec(v_declName_1185_);
lean_dec_ref_known(v___y_1156_, 4);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1190_;
}
}
case 5:
{
lean_object* v_dummy_1202_; lean_object* v_nargs_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_dummy_1202_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1203_ = l_Lean_Expr_getAppNumArgs(v___y_1156_);
lean_inc(v_nargs_1203_);
v___x_1204_ = lean_mk_array(v_nargs_1203_, v_dummy_1202_);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_sub(v_nargs_1203_, v___x_1205_);
lean_dec(v_nargs_1203_);
v___x_1207_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1099_, v_post_1101_, v___y_1156_, v___x_1204_, v___x_1206_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1207_;
}
case 10:
{
lean_object* v_data_1208_; lean_object* v_expr_1209_; lean_object* v___x_1210_; 
v_data_1208_ = lean_ctor_get(v___y_1156_, 0);
v_expr_1209_ = lean_ctor_get(v___y_1156_, 1);
lean_inc_ref(v_expr_1209_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1210_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_expr_1209_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; size_t v___x_1212_; size_t v___x_1213_; uint8_t v___x_1214_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = lean_ptr_addr(v_expr_1209_);
v___x_1213_ = lean_ptr_addr(v_a_1211_);
v___x_1214_ = lean_usize_dec_eq(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_inc(v_data_1208_);
lean_dec_ref_known(v___y_1156_, 2);
v___x_1215_ = l_Lean_Expr_mdata___override(v_data_1208_, v_a_1211_);
v___x_1216_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1215_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1216_;
}
else
{
lean_object* v___x_1217_; 
lean_dec(v_a_1211_);
v___x_1217_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___y_1156_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1217_;
}
}
else
{
lean_dec_ref_known(v___y_1156_, 2);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1210_;
}
}
case 11:
{
lean_object* v_typeName_1218_; lean_object* v_idx_1219_; lean_object* v_struct_1220_; lean_object* v___x_1221_; 
v_typeName_1218_ = lean_ctor_get(v___y_1156_, 0);
v_idx_1219_ = lean_ctor_get(v___y_1156_, 1);
v_struct_1220_ = lean_ctor_get(v___y_1156_, 2);
lean_inc_ref(v_struct_1220_);
lean_inc_ref(v_post_1101_);
lean_inc_ref(v_pre_1099_);
v___x_1221_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1099_, v_post_1101_, v_struct_1220_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; size_t v___x_1223_; size_t v___x_1224_; uint8_t v___x_1225_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = lean_ptr_addr(v_struct_1220_);
v___x_1224_ = lean_ptr_addr(v_a_1222_);
v___x_1225_ = lean_usize_dec_eq(v___x_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_inc(v_idx_1219_);
lean_inc(v_typeName_1218_);
lean_dec_ref_known(v___y_1156_, 3);
v___x_1226_ = l_Lean_Expr_proj___override(v_typeName_1218_, v_idx_1219_, v_a_1222_);
v___x_1227_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1226_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_a_1222_);
v___x_1228_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___y_1156_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1228_;
}
}
else
{
lean_dec_ref_known(v___y_1156_, 3);
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_pre_1099_);
return v___x_1221_;
}
}
default: 
{
lean_object* v___x_1229_; 
v___x_1229_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___y_1156_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1229_;
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_e_1100_);
lean_dec_ref(v_pre_1099_);
v_a_1241_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1150_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1150_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref(v_post_1101_);
lean_dec_ref(v_e_1100_);
lean_dec_ref(v_pre_1099_);
v_a_1249_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1149_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1149_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
v___jp_1106_:
{
if (v___y_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___y_1111_);
v___x_1115_ = l_Lean_Expr_letE___override(v___y_1108_, v___y_1110_, v___y_1107_, v___y_1109_, v___y_1113_);
v___x_1116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1115_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1116_;
}
else
{
size_t v___x_1117_; size_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1117_ = lean_ptr_addr(v___y_1112_);
lean_dec_ref(v___y_1112_);
v___x_1118_ = lean_ptr_addr(v___y_1109_);
v___x_1119_ = lean_usize_dec_eq(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v___y_1111_);
v___x_1120_ = l_Lean_Expr_letE___override(v___y_1108_, v___y_1110_, v___y_1107_, v___y_1109_, v___y_1113_);
v___x_1121_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1120_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
v___x_1122_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___y_1111_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1122_;
}
}
}
v___jp_1123_:
{
if (v___y_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec_ref(v___y_1126_);
v___x_1130_ = l_Lean_Expr_lam___override(v___y_1127_, v___y_1124_, v___y_1125_, v___y_1128_);
v___x_1131_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1130_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1131_;
}
else
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Lean_instBEqBinderInfo_beq(v___y_1128_, v___y_1128_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v___y_1126_);
v___x_1133_ = l_Lean_Expr_lam___override(v___y_1127_, v___y_1124_, v___y_1125_, v___y_1128_);
v___x_1134_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1133_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; 
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v___y_1124_);
v___x_1135_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___y_1126_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1135_;
}
}
}
v___jp_1136_:
{
if (v___y_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref(v___y_1138_);
v___x_1143_ = l_Lean_Expr_forallE___override(v___y_1140_, v___y_1139_, v___y_1137_, v___y_1141_);
v___x_1144_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1143_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1144_;
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = l_Lean_instBEqBinderInfo_beq(v___y_1141_, v___y_1141_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v___y_1138_);
v___x_1146_ = l_Lean_Expr_forallE___override(v___y_1140_, v___y_1139_, v___y_1137_, v___y_1141_);
v___x_1147_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___x_1146_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec_ref(v___y_1137_);
v___x_1148_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1099_, v_post_1101_, v___y_1138_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1257_, lean_object* v_pre_1258_, lean_object* v_e_1259_, lean_object* v_post_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1257_, v_pre_1258_, v_e_1259_, v_post_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1266_, lean_object* v_post_1267_, lean_object* v_e_1268_, lean_object* v_a_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_inc(v_a_1269_);
v___x_1273_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1273_, 0, lean_box(0));
lean_closure_set(v___x_1273_, 1, lean_box(0));
lean_closure_set(v___x_1273_, 2, v_a_1269_);
v___x_1274_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1273_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1306_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1306_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1306_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1275_, v_e_1268_);
lean_dec(v_a_1275_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; 
lean_del_object(v___x_1277_);
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1268_);
v___f_1281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1281_, 0, v___x_1280_);
lean_closure_set(v___f_1281_, 1, v_pre_1266_);
lean_closure_set(v___f_1281_, 2, v_e_1268_);
lean_closure_set(v___f_1281_, 3, v_post_1267_);
v___x_1282_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1281_, v_a_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___f_1284_; lean_object* v___x_1285_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_n(v_a_1283_, 2);
lean_dec_ref_known(v___x_1282_, 1);
lean_inc(v_a_1269_);
v___f_1284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1284_, 0, v_a_1269_);
lean_closure_set(v___f_1284_, 1, v_e_1268_);
lean_closure_set(v___f_1284_, 2, v_a_1283_);
v___x_1285_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1284_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1285_, 0);
lean_dec(v_unused_1293_);
v___x_1287_ = v___x_1285_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v___x_1285_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_a_1283_);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1283_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_a_1283_);
v_a_1294_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1285_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1285_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_dec_ref(v_e_1268_);
return v___x_1282_;
}
}
else
{
lean_object* v_val_1302_; lean_object* v___x_1304_; 
lean_dec_ref(v_e_1268_);
lean_dec_ref(v_post_1267_);
lean_dec_ref(v_pre_1266_);
v_val_1302_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1302_);
lean_dec_ref_known(v___x_1279_, 1);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v_val_1302_);
v___x_1304_ = v___x_1277_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_val_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v_e_1268_);
lean_dec_ref(v_post_1267_);
lean_dec_ref(v_pre_1266_);
v_a_1307_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1274_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1274_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1315_, lean_object* v_post_1316_, lean_object* v_e_1317_, lean_object* v_a_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
lean_inc_ref(v_post_1316_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc_ref(v_e_1317_);
v___x_1322_ = lean_apply_4(v_post_1316_, v_e_1317_, v___y_1319_, v___y_1320_, lean_box(0));
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1341_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1341_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1341_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
switch(lean_obj_tag(v_a_1323_))
{
case 0:
{
lean_object* v_e_1327_; lean_object* v___x_1329_; 
lean_dec_ref(v_e_1317_);
lean_dec_ref(v_post_1316_);
lean_dec_ref(v_pre_1315_);
v_e_1327_ = lean_ctor_get(v_a_1323_, 0);
lean_inc_ref(v_e_1327_);
lean_dec_ref_known(v_a_1323_, 1);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v_e_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_e_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
case 1:
{
lean_object* v_e_1331_; lean_object* v___x_1332_; 
lean_del_object(v___x_1325_);
lean_dec_ref(v_e_1317_);
v_e_1331_ = lean_ctor_get(v_a_1323_, 0);
lean_inc_ref(v_e_1331_);
lean_dec_ref_known(v_a_1323_, 1);
v___x_1332_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1315_, v_post_1316_, v_e_1331_, v_a_1318_, v___y_1319_, v___y_1320_);
return v___x_1332_;
}
default: 
{
lean_object* v_e_x3f_1333_; 
lean_dec_ref(v_post_1316_);
lean_dec_ref(v_pre_1315_);
v_e_x3f_1333_ = lean_ctor_get(v_a_1323_, 0);
lean_inc(v_e_x3f_1333_);
lean_dec_ref_known(v_a_1323_, 1);
if (lean_obj_tag(v_e_x3f_1333_) == 0)
{
lean_object* v___x_1335_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v_e_1317_);
v___x_1335_ = v___x_1325_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_e_1317_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1339_; 
lean_dec_ref(v_e_1317_);
v_val_1337_ = lean_ctor_get(v_e_x3f_1333_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v_e_x3f_1333_, 1);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v_val_1337_);
v___x_1339_ = v___x_1325_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_val_1337_);
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
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_e_1317_);
lean_dec_ref(v_post_1316_);
lean_dec_ref(v_pre_1315_);
v_a_1342_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1322_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1322_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1350_, lean_object* v_post_1351_, lean_object* v_e_1352_, lean_object* v_a_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1350_, v_post_1351_, v_e_1352_, v_a_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_a_1353_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1358_, lean_object* v_post_1359_, lean_object* v_sz_1360_, lean_object* v_i_1361_, lean_object* v_bs_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
size_t v_sz_boxed_1367_; size_t v_i_boxed_1368_; lean_object* v_res_1369_; 
v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1360_);
lean_dec(v_sz_1360_);
v_i_boxed_1368_ = lean_unbox_usize(v_i_1361_);
lean_dec(v_i_1361_);
v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1358_, v_post_1359_, v_sz_boxed_1367_, v_i_boxed_1368_, v_bs_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1370_, lean_object* v_post_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1370_, v_post_1371_, v_x_1372_, v_x_1373_, v_x_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1380_, lean_object* v_post_1381_, lean_object* v_e_1382_, lean_object* v_a_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1380_, v_post_1381_, v_e_1382_, v_a_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v_a_1383_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1388_, lean_object* v_x_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_apply_1(v_x_1389_, lean_box(0));
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1395_, v_x_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1400_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_unsigned_to_nat(16u);
v___x_1403_ = lean_mk_array(v___x_1402_, v___x_1401_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
return v___x_1406_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1408_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1408_, 0, lean_box(0));
lean_closure_set(v___x_1408_, 1, lean_box(0));
lean_closure_set(v___x_1408_, 2, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1409_, lean_object* v_pre_1410_, lean_object* v_post_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_a_1417_; lean_object* v___x_1418_; 
v___x_1415_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1416_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1415_, v___y_1412_, v___y_1413_);
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1410_, v_post_1411_, v_input_1409_, v_a_1417_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1420_, 0, lean_box(0));
lean_closure_set(v___x_1420_, 1, lean_box(0));
lean_closure_set(v___x_1420_, 2, v_a_1417_);
v___x_1421_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1420_, v___y_1412_, v___y_1413_);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v___x_1421_, 0);
lean_dec(v_unused_1429_);
v___x_1423_ = v___x_1421_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v___x_1421_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_a_1419_);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1419_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_dec(v_a_1417_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1430_, lean_object* v_pre_1431_, lean_object* v_post_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1430_, v_pre_1431_, v_post_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; 
v___f_1443_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1444_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1445_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1439_, v___f_1443_, v___f_1444_, v_a_1440_, v_a_1441_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1451_, lean_object* v_m_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1452_, v_a_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1455_, lean_object* v_m_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1455_, v_m_1456_, v_a_1457_);
lean_dec_ref(v_a_1457_);
lean_dec_ref(v_m_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1459_, lean_object* v_ref_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1460_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1465_, lean_object* v_ref_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1465_, v_ref_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1488_, v_x_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1495_, lean_object* v_m_1496_, lean_object* v_a_1497_, lean_object* v_b_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1496_, v_a_1497_, v_b_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1500_, lean_object* v_a_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1501_, v_x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1504_, lean_object* v_a_1505_, lean_object* v_x_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1504_, v_a_1505_, v_x_1506_);
lean_dec(v_x_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1507_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1508_, lean_object* v_a_1509_, lean_object* v_x_1510_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1509_, v_x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1512_, lean_object* v_a_1513_, lean_object* v_x_1514_){
_start:
{
uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_res_1515_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1512_, v_a_1513_, v_x_1514_);
lean_dec(v_x_1514_);
lean_dec_ref(v_a_1513_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1517_, lean_object* v_data_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1520_, lean_object* v_a_1521_, lean_object* v_b_1522_, lean_object* v_x_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1521_, v_b_1522_, v_x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1525_, lean_object* v_i_1526_, lean_object* v_source_1527_, lean_object* v_target_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1526_, v_source_1527_, v_target_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1531_, v_x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v_env_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1537_ = lean_st_ref_get(v___y_1535_);
v_env_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc_ref(v_env_1538_);
lean_dec(v___x_1537_);
v___x_1539_ = l_Lean_isRecCore(v_env_1538_, v_declName_1534_);
v___x_1540_ = lean_box(v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1542_, v___y_1543_);
lean_dec(v___y_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1546_, v___y_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v_env_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1563_ = lean_st_ref_get(v___y_1561_);
v_env_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_env_1564_);
lean_dec(v___x_1563_);
v___x_1565_ = l_Lean_getReducibilityStatusCore(v_env_1564_, v_declName_1560_);
v___x_1566_ = lean_box(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1568_, v___y_1569_);
lean_dec(v___y_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1594_; 
v___x_1578_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1572_, v___y_1576_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1594_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1594_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_unbox(v_a_1579_);
lean_dec(v_a_1579_);
if (v___x_1583_ == 0)
{
uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1584_ = 1;
v___x_1585_ = lean_box(v___x_1584_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
else
{
uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1589_ = 0;
v___x_1590_ = lean_box(v___x_1589_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1590_);
v___x_1592_ = v___x_1581_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1602_, lean_object* v_b_1603_){
_start:
{
lean_object* v_array_1605_; lean_object* v_start_1606_; lean_object* v_stop_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1624_; 
v_array_1605_ = lean_ctor_get(v_a_1602_, 0);
v_start_1606_ = lean_ctor_get(v_a_1602_, 1);
v_stop_1607_ = lean_ctor_get(v_a_1602_, 2);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_a_1602_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1609_ = v_a_1602_;
v_isShared_1610_ = v_isSharedCheck_1624_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_stop_1607_);
lean_inc(v_start_1606_);
lean_inc(v_array_1605_);
lean_dec(v_a_1602_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1624_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_nat_dec_lt(v_start_1606_, v_stop_1607_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_del_object(v___x_1609_);
lean_dec(v_stop_1607_);
lean_dec(v_start_1606_);
lean_dec_ref(v_array_1605_);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_b_1603_);
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_add(v_start_1606_, v___x_1614_);
lean_inc_ref(v_array_1605_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v___x_1615_);
v___x_1617_ = v___x_1609_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_array_1605_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_stop_1607_);
v___x_1617_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = lean_array_fget(v_array_1605_, v_start_1606_);
lean_dec(v_start_1606_);
lean_dec_ref(v_array_1605_);
v___x_1619_ = l_Lean_Expr_hasExprMVar(v___x_1618_);
lean_dec(v___x_1618_);
if (v___x_1619_ == 0)
{
v_a_1602_ = v___x_1617_;
v_b_1603_ = v___x_1613_;
goto _start;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_dec_ref_known(v___x_1621_, 1);
v_a_1602_ = v___x_1617_;
v_b_1603_ = v___x_1613_;
goto _start;
}
else
{
lean_dec_ref(v___x_1617_);
return v___x_1621_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1625_, lean_object* v_b_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1625_, v_b_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1637_, uint8_t v_isMatch_1638_, uint8_t v_root_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___y_1646_; lean_object* v_b_1647_; lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1637_, v_root_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1821_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1821_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1821_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___y_1664_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; 
if (v_root_1639_ == 0)
{
lean_object* v___x_1809_; 
lean_inc(v_a_1659_);
v___x_1809_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1659_);
if (lean_obj_tag(v___x_1809_) == 1)
{
lean_object* v_val_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1820_; 
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v_val_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_val_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set_tag(v___x_1812_, 2);
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_val_1810_);
v___x_1815_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
}
else
{
lean_dec(v___x_1809_);
v___y_1674_ = v_a_1640_;
v___y_1675_ = v_a_1641_;
v___y_1676_ = v_a_1642_;
v___y_1677_ = v_a_1643_;
goto v___jp_1673_;
}
}
else
{
v___y_1674_ = v_a_1640_;
v___y_1675_ = v_a_1641_;
v___y_1676_ = v_a_1642_;
v___y_1677_ = v_a_1643_;
goto v___jp_1673_;
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1665_ = l_Lean_Expr_getAppNumArgs(v_a_1659_);
lean_inc(v___x_1665_);
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___y_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_mk_empty_array_with_capacity(v___x_1665_);
lean_dec(v___x_1665_);
v___x_1668_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1659_, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1666_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1669_);
v___x_1671_ = v___x_1661_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
v___jp_1673_:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Expr_getAppFn(v_a_1659_);
switch(lean_obj_tag(v___x_1678_))
{
case 1:
{
lean_object* v_fvarId_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_del_object(v___x_1661_);
v_fvarId_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_fvarId_1679_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1680_ = l_Lean_Expr_getAppNumArgs(v_a_1659_);
lean_inc(v___x_1680_);
v___x_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_fvarId_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_mk_empty_array_with_capacity(v___x_1680_);
lean_dec(v___x_1680_);
v___x_1683_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1659_, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1681_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
case 2:
{
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
if (v_isMatch_1638_ == 0)
{
lean_object* v_mvarId_1686_; lean_object* v___x_1687_; uint8_t v_isDefEqStuckEx_1688_; 
v_mvarId_1686_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_mvarId_1686_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1687_ = l_Lean_Meta_Context_config(v___y_1674_);
v_isDefEqStuckEx_1688_ = lean_ctor_get_uint8(v___x_1687_, 4);
lean_dec_ref(v___x_1687_);
if (v_isDefEqStuckEx_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1686_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1703_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_unbox(v_a_1690_);
lean_dec(v_a_1690_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1695_);
v___x_1697_ = v___x_1692_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1699_);
v___x_1701_ = v___x_1692_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_a_1704_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1689_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1689_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v_mvarId_1686_);
v___x_1712_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref_known(v___x_1678_, 1);
v___x_1714_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
}
case 4:
{
lean_object* v_declName_1716_; lean_object* v___x_1717_; uint8_t v_isDefEqStuckEx_1718_; 
v_declName_1716_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_declName_1716_);
lean_dec_ref_known(v___x_1678_, 2);
v___x_1717_ = l_Lean_Meta_Context_config(v___y_1674_);
v_isDefEqStuckEx_1718_ = lean_ctor_get_uint8(v___x_1717_, 4);
lean_dec_ref(v___x_1717_);
if (v_isDefEqStuckEx_1718_ == 0)
{
v___y_1664_ = v_declName_1716_;
goto v___jp_1663_;
}
else
{
uint8_t v___x_1719_; 
v___x_1719_ = l_Lean_Expr_hasExprMVar(v_a_1659_);
if (v___x_1719_ == 0)
{
v___y_1664_ = v_declName_1716_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1720_; 
lean_inc(v_declName_1716_);
v___x_1720_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1716_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = lean_unbox(v_a_1721_);
lean_dec(v_a_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v_env_1724_; lean_object* v___x_1725_; 
v___x_1723_ = lean_st_ref_get(v___y_1677_);
v_env_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_ref(v_env_1724_);
lean_dec(v___x_1723_);
v___x_1725_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1724_, v_a_1659_);
if (lean_obj_tag(v___x_1725_) == 1)
{
lean_object* v_val_1726_; lean_object* v_numDiscrs_1727_; lean_object* v_nargs_1728_; lean_object* v_dummy_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_val_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v_numDiscrs_1727_ = lean_ctor_get(v_val_1726_, 1);
lean_inc(v_numDiscrs_1727_);
v_nargs_1728_ = l_Lean_Expr_getAppNumArgs(v_a_1659_);
v_dummy_1729_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1728_);
v___x_1730_ = lean_mk_array(v_nargs_1728_, v_dummy_1729_);
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_sub(v_nargs_1728_, v___x_1731_);
lean_dec(v_nargs_1728_);
lean_inc(v_a_1659_);
v___x_1733_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1659_, v___x_1730_, v___x_1732_);
v___x_1734_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1726_);
lean_dec(v_val_1726_);
v___x_1735_ = lean_nat_add(v___x_1734_, v_numDiscrs_1727_);
lean_dec(v_numDiscrs_1727_);
v___x_1736_ = l_Array_toSubarray___redArg(v___x_1733_, v___x_1734_, v___x_1735_);
v___x_1737_ = lean_box(0);
v___x_1738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1736_, v___x_1737_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref_known(v___x_1738_, 1);
v___y_1664_ = v_declName_1716_;
goto v___jp_1663_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_declName_1716_);
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v_a_1748_; uint8_t v___x_1749_; 
lean_dec(v___x_1725_);
lean_inc(v_declName_1716_);
v___x_1747_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1716_, v___y_1677_);
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = lean_unbox(v_a_1748_);
lean_dec(v_a_1748_);
if (v___x_1749_ == 0)
{
v___y_1664_ = v_declName_1716_;
goto v___jp_1663_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_dec_ref_known(v___x_1750_, 1);
v___y_1664_ = v_declName_1716_;
goto v___jp_1663_;
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_declName_1716_);
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
else
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_dec_ref_known(v___x_1759_, 1);
v___y_1664_ = v_declName_1716_;
goto v___jp_1663_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_declName_1716_);
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec(v_declName_1716_);
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v_a_1768_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1720_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1720_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1776_; lean_object* v_body_1777_; uint8_t v___x_1778_; 
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v_binderType_1776_ = lean_ctor_get(v___x_1678_, 1);
lean_inc_ref(v_binderType_1776_);
v_body_1777_ = lean_ctor_get(v___x_1678_, 2);
lean_inc_ref(v_body_1777_);
lean_dec_ref_known(v___x_1678_, 3);
v___x_1778_ = l_Lean_Expr_hasLooseBVars(v_body_1777_);
if (v___x_1778_ == 0)
{
v___y_1646_ = v_binderType_1776_;
v_b_1647_ = v_body_1777_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1777_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___y_1646_ = v_binderType_1776_;
v_b_1647_ = v_a_1780_;
goto v___jp_1645_;
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_binderType_1776_);
v_a_1781_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1779_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v_a_1789_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_a_1789_);
lean_dec_ref_known(v___x_1678_, 1);
v___x_1790_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1789_);
v___x_1791_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
case 11:
{
lean_object* v_typeName_1794_; lean_object* v_idx_1795_; lean_object* v_struct_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_del_object(v___x_1661_);
v_typeName_1794_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_typeName_1794_);
v_idx_1795_ = lean_ctor_get(v___x_1678_, 1);
lean_inc(v_idx_1795_);
v_struct_1796_ = lean_ctor_get(v___x_1678_, 2);
lean_inc_ref(v_struct_1796_);
lean_dec_ref_known(v___x_1678_, 3);
v___x_1797_ = l_Lean_Expr_getAppNumArgs(v_a_1659_);
lean_inc(v___x_1797_);
v___x_1798_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1798_, 0, v_typeName_1794_);
lean_ctor_set(v___x_1798_, 1, v_idx_1795_);
lean_ctor_set(v___x_1798_, 2, v___x_1797_);
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_mk_empty_array_with_capacity(v___x_1799_);
v___x_1801_ = lean_array_push(v___x_1800_, v_struct_1796_);
v___x_1802_ = lean_mk_empty_array_with_capacity(v___x_1797_);
lean_dec(v___x_1797_);
v___x_1803_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1659_, v___x_1802_);
v___x_1804_ = l_Array_append___redArg(v___x_1801_, v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1798_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
default: 
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec_ref(v___x_1678_);
lean_del_object(v___x_1661_);
lean_dec(v_a_1659_);
v___x_1807_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1658_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1658_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
v___jp_1645_:
{
uint8_t v___x_1648_; 
v___x_1648_ = l_Lean_Expr_hasLooseBVars(v_b_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1649_ = lean_box(5);
v___x_1650_ = lean_unsigned_to_nat(2u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_array_push(v___x_1651_, v___y_1646_);
v___x_1653_ = lean_array_push(v___x_1652_, v_b_1647_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1649_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec_ref(v_b_1647_);
lean_dec_ref(v___y_1646_);
v___x_1656_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1830_, lean_object* v_isMatch_1831_, lean_object* v_root_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
uint8_t v_isMatch_boxed_1838_; uint8_t v_root_boxed_1839_; lean_object* v_res_1840_; 
v_isMatch_boxed_1838_ = lean_unbox(v_isMatch_1831_);
v_root_boxed_1839_ = lean_unbox(v_root_1832_);
v_res_1840_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1830_, v_isMatch_boxed_1838_, v_root_boxed_1839_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1841_, v___y_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1855_, lean_object* v_R_1856_, lean_object* v_a_1857_, lean_object* v_b_1858_, lean_object* v_c_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1857_, v_b_1858_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1866_, lean_object* v_R_1867_, lean_object* v_a_1868_, lean_object* v_b_1869_, lean_object* v_c_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1866_, v_R_1867_, v_a_1868_, v_b_1869_, v_c_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1877_, uint8_t v_root_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
uint8_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = 1;
v___x_1885_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1877_, v___x_1884_, v_root_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1886_, lean_object* v_root_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
uint8_t v_root_boxed_1893_; lean_object* v_res_1894_; 
v_root_boxed_1893_ = lean_unbox(v_root_1887_);
v_res_1894_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1886_, v_root_boxed_1893_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
return v_res_1894_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_unsigned_to_nat(16u);
v___x_1899_ = lean_mk_array(v___x_1898_, v___x_1897_);
return v___x_1899_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1900_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1905_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_1906_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1909_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v___x_1907_);
lean_ctor_set(v___x_1909_, 2, v___x_1906_);
lean_ctor_set(v___x_1909_, 3, v___x_1905_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1920_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1918_);
lean_ctor_set(v___x_1920_, 2, v___x_1917_);
lean_ctor_set(v___x_1920_, 3, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v_values_1925_; lean_object* v_star_1926_; lean_object* v_children_1927_; lean_object* v_pending_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1936_; 
v_values_1925_ = lean_ctor_get(v_x_1923_, 0);
v_star_1926_ = lean_ctor_get(v_x_1923_, 1);
v_children_1927_ = lean_ctor_get(v_x_1923_, 2);
v_pending_1928_ = lean_ctor_get(v_x_1923_, 3);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_x_1923_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1930_ = v_x_1923_;
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_pending_1928_);
lean_inc(v_children_1927_);
lean_inc(v_star_1926_);
lean_inc(v_values_1925_);
lean_dec(v_x_1923_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_array_push(v_pending_1928_, v_x_1924_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 3, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_values_1925_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_star_1926_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_children_1927_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v___x_1932_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1938_, v_x_1939_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1941_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1942_ = lean_unsigned_to_nat(1u);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1942_);
v___x_1944_ = lean_array_push(v___x_1943_, v___x_1941_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1946_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v_env_1957_; lean_object* v___x_1958_; lean_object* v_mctx_1959_; lean_object* v_lctx_1960_; lean_object* v_options_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1956_ = lean_st_ref_get(v___y_1954_);
v_env_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc_ref(v_env_1957_);
lean_dec(v___x_1956_);
v___x_1958_ = lean_st_ref_get(v___y_1952_);
v_mctx_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref(v_mctx_1959_);
lean_dec(v___x_1958_);
v_lctx_1960_ = lean_ctor_get(v___y_1951_, 2);
v_options_1961_ = lean_ctor_get(v___y_1953_, 2);
lean_inc_ref(v_options_1961_);
lean_inc_ref(v_lctx_1960_);
v___x_1962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1962_, 0, v_env_1957_);
lean_ctor_set(v___x_1962_, 1, v_mctx_1959_);
lean_ctor_set(v___x_1962_, 2, v_lctx_1960_);
lean_ctor_set(v___x_1962_, 3, v_options_1961_);
v___x_1963_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v_msgData_1950_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_ref_1978_; lean_object* v___x_1979_; lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_ref_1978_ = lean_ctor_get(v___y_1975_, 5);
v___x_1979_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
lean_inc(v_ref_1978_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_ref_1978_);
lean_ctor_set(v___x_1984_, 1, v_a_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 1);
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
return v_res_1995_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1999_, lean_object* v_todo_2000_, lean_object* v_e_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_2001_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2001_, v_root_1999_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2148_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2148_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2148_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_v_2014_; lean_object* v___x_2020_; lean_object* v_k_2022_; lean_object* v_nargs_2023_; lean_object* v_todo_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; 
v___x_2020_ = l_Lean_Expr_getAppFn(v_a_2009_);
switch(lean_obj_tag(v___x_2020_))
{
case 9:
{
lean_object* v_a_2067_; 
lean_dec(v_a_2009_);
v_a_2067_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_ref(v_a_2067_);
lean_dec_ref_known(v___x_2020_, 1);
v_v_2014_ = v_a_2067_;
goto v___jp_2013_;
}
case 4:
{
lean_object* v_declName_2068_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; 
v_declName_2068_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_declName_2068_);
if (v_root_1999_ == 0)
{
lean_object* v___x_2076_; 
lean_inc(v_a_2009_);
v___x_2076_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_2009_);
if (lean_obj_tag(v___x_2076_) == 1)
{
lean_object* v_val_2077_; 
lean_dec(v_declName_2068_);
lean_dec_ref_known(v___x_2020_, 2);
lean_dec(v_a_2009_);
v_val_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v_v_2014_ = v_val_2077_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2078_; 
lean_dec(v___x_2076_);
lean_del_object(v___x_2011_);
v___x_2078_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2068_, v_a_2009_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2089_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_unbox(v_a_2079_);
lean_dec(v_a_2079_);
if (v___x_2083_ == 0)
{
lean_del_object(v___x_2081_);
v___y_2070_ = v_a_2002_;
v___y_2071_ = v_a_2003_;
v___y_2072_ = v_a_2004_;
v___y_2073_ = v_a_2005_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
lean_dec(v_declName_2068_);
lean_dec_ref_known(v___x_2020_, 2);
lean_dec(v_a_2009_);
v___x_2084_ = lean_box(3);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v_todo_2000_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2085_);
v___x_2087_ = v___x_2081_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v_declName_2068_);
lean_dec_ref_known(v___x_2020_, 2);
lean_dec(v_a_2009_);
lean_dec_ref(v_todo_2000_);
v_a_2090_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2078_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2078_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_del_object(v___x_2011_);
v___y_2070_ = v_a_2002_;
v___y_2071_ = v_a_2003_;
v___y_2072_ = v_a_2004_;
v___y_2073_ = v_a_2005_;
goto v___jp_2069_;
}
v___jp_2069_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = l_Lean_Expr_getAppNumArgs(v_a_2009_);
lean_inc(v___x_2074_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_declName_2068_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v_k_2022_ = v___x_2075_;
v_nargs_2023_ = v___x_2074_;
v_todo_2024_ = v_todo_2000_;
v___y_2025_ = v___y_2070_;
v___y_2026_ = v___y_2071_;
v___y_2027_ = v___y_2072_;
v___y_2028_ = v___y_2073_;
goto v___jp_2021_;
}
}
case 11:
{
lean_object* v_typeName_2098_; lean_object* v_idx_2099_; lean_object* v_struct_2100_; lean_object* v___x_2101_; lean_object* v___y_2103_; lean_object* v_env_2107_; uint8_t v___x_2108_; 
lean_del_object(v___x_2011_);
v_typeName_2098_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_typeName_2098_);
v_idx_2099_ = lean_ctor_get(v___x_2020_, 1);
lean_inc(v_idx_2099_);
v_struct_2100_ = lean_ctor_get(v___x_2020_, 2);
lean_inc_ref(v_struct_2100_);
v___x_2101_ = lean_st_ref_get(v_a_2005_);
v_env_2107_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_ref(v_env_2107_);
lean_dec(v___x_2101_);
v___x_2108_ = l_Lean_isClass(v_env_2107_, v_typeName_2098_);
if (v___x_2108_ == 0)
{
v___y_2103_ = v_struct_2100_;
goto v___jp_2102_;
}
else
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2100_);
v___y_2103_ = v___x_2109_;
goto v___jp_2102_;
}
v___jp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = l_Lean_Expr_getAppNumArgs(v_a_2009_);
lean_inc(v___x_2104_);
v___x_2105_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2105_, 0, v_typeName_2098_);
lean_ctor_set(v___x_2105_, 1, v_idx_2099_);
lean_ctor_set(v___x_2105_, 2, v___x_2104_);
v___x_2106_ = lean_array_push(v_todo_2000_, v___y_2103_);
v_k_2022_ = v___x_2105_;
v_nargs_2023_ = v___x_2104_;
v_todo_2024_ = v___x_2106_;
v___y_2025_ = v_a_2002_;
v___y_2026_ = v_a_2003_;
v___y_2027_ = v_a_2004_;
v___y_2028_ = v_a_2005_;
goto v___jp_2021_;
}
}
case 1:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec_ref_known(v___x_2020_, 1);
lean_del_object(v___x_2011_);
lean_dec(v_a_2009_);
v___x_2110_ = lean_box(3);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v_todo_2000_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
case 2:
{
lean_object* v_mvarId_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
lean_del_object(v___x_2011_);
lean_dec(v_a_2009_);
v_mvarId_2113_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_mvarId_2113_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2114_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2115_ = l_Lean_instBEqMVarId_beq(v_mvarId_2113_, v___x_2114_);
lean_dec(v_mvarId_2113_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec_ref(v_todo_2000_);
v___x_2116_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2117_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2116_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
return v___x_2117_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_box(3);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v_todo_2000_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
case 7:
{
lean_object* v_binderType_2121_; lean_object* v_body_2122_; lean_object* v_b_2124_; uint8_t v___x_2134_; 
lean_del_object(v___x_2011_);
lean_dec(v_a_2009_);
v_binderType_2121_ = lean_ctor_get(v___x_2020_, 1);
lean_inc_ref(v_binderType_2121_);
v_body_2122_ = lean_ctor_get(v___x_2020_, 2);
lean_inc_ref(v_body_2122_);
lean_dec_ref_known(v___x_2020_, 3);
v___x_2134_ = l_Lean_Expr_hasLooseBVars(v_body_2122_);
if (v___x_2134_ == 0)
{
v_b_2124_ = v_body_2122_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2122_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v_b_2124_ = v_a_2136_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v_binderType_2121_);
lean_dec_ref(v_todo_2000_);
v_a_2137_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2135_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
v___jp_2123_:
{
uint8_t v___x_2125_; 
v___x_2125_ = l_Lean_Expr_hasLooseBVars(v_b_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2126_ = lean_box(5);
v___x_2127_ = lean_array_push(v_todo_2000_, v_binderType_2121_);
v___x_2128_ = lean_array_push(v___x_2127_, v_b_2124_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2126_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref(v_b_2124_);
lean_dec_ref(v_binderType_2121_);
v___x_2131_ = lean_box(4);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v_todo_2000_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
}
default: 
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref(v___x_2020_);
lean_del_object(v___x_2011_);
lean_dec(v_a_2009_);
v___x_2145_ = lean_box(4);
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v_todo_2000_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
v___jp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2015_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_v_2014_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set(v___x_2016_, 1, v_todo_2000_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2016_);
v___x_2018_ = v___x_2011_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
v___jp_2021_:
{
lean_object* v___x_2029_; 
lean_inc(v_nargs_2023_);
v___x_2029_ = l_Lean_Meta_getFunInfoNArgs(v___x_2020_, v_nargs_2023_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v_paramInfo_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2057_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v_paramInfo_2031_ = lean_ctor_get(v_a_2030_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_a_2030_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_a_2030_, 1);
lean_dec(v_unused_2058_);
v___x_2033_ = v_a_2030_;
v_isShared_2034_ = v_isSharedCheck_2057_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_paramInfo_2031_);
lean_dec(v_a_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2057_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_nat_sub(v_nargs_2023_, v___x_2035_);
lean_dec(v_nargs_2023_);
v___x_2037_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2031_, v___x_2036_, v_a_2009_, v_todo_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec_ref(v_paramInfo_2031_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2048_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2048_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2048_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_a_2038_);
lean_ctor_set(v___x_2033_, 0, v_k_2022_);
v___x_2043_ = v___x_2033_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_k_2022_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2045_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2043_);
v___x_2045_ = v___x_2040_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_del_object(v___x_2033_);
lean_dec(v_k_2022_);
v_a_2049_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2037_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2037_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_todo_2024_);
lean_dec(v_nargs_2023_);
lean_dec(v_k_2022_);
lean_dec(v_a_2009_);
v_a_2059_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2029_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2029_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v_todo_2000_);
v_a_2149_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2008_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2008_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref(v_e_2001_);
v___x_2157_ = lean_box(3);
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v_todo_2000_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2160_, lean_object* v_todo_2161_, lean_object* v_e_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
uint8_t v_root_boxed_2168_; lean_object* v_res_2169_; 
v_root_boxed_2168_ = lean_unbox(v_root_2160_);
v_res_2169_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2168_, v_todo_2161_, v_e_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2170_, lean_object* v_msg_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2178_, lean_object* v_msg_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2178_, v_msg_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2185_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_unsigned_to_nat(8u);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = 1;
v___x_2194_ = lean_unsigned_to_nat(8u);
v___x_2195_ = lean_mk_empty_array_with_capacity(v___x_2194_);
v___x_2196_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2193_, v___x_2195_, v_e_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2204_, uint8_t v_root_2205_, lean_object* v_todo_2206_, lean_object* v_keys_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2213_ = lean_array_get_size(v_todo_2206_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = lean_nat_dec_eq(v___x_2213_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_e_2219_; lean_object* v_todo_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2216_ = l_Lean_instInhabitedExpr;
v___x_2217_ = lean_unsigned_to_nat(1u);
v___x_2218_ = lean_nat_sub(v___x_2213_, v___x_2217_);
v_e_2219_ = lean_array_get(v___x_2216_, v_todo_2206_, v___x_2218_);
lean_dec(v___x_2218_);
v_todo_2220_ = lean_array_pop(v_todo_2206_);
v___x_2221_ = lean_box(v_root_2205_);
lean_inc_ref(v_op_2204_);
lean_inc(v_a_2211_);
lean_inc_ref(v_a_2210_);
lean_inc(v_a_2209_);
lean_inc_ref(v_a_2208_);
v___x_2222_ = lean_apply_8(v_op_2204_, v___x_2221_, v_todo_2220_, v_e_2219_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, lean_box(0));
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v_fst_2224_; lean_object* v_snd_2225_; lean_object* v___x_2226_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v_fst_2224_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_fst_2224_);
v_snd_2225_ = lean_ctor_get(v_a_2223_, 1);
lean_inc(v_snd_2225_);
lean_dec(v_a_2223_);
v___x_2226_ = lean_array_push(v_keys_2207_, v_fst_2224_);
v_root_2205_ = v___x_2215_;
v_todo_2206_ = v_snd_2225_;
v_keys_2207_ = v___x_2226_;
goto _start;
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_keys_2207_);
lean_dec_ref(v_op_2204_);
v_a_2228_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2222_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2222_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v___x_2236_; 
lean_dec_ref(v_todo_2206_);
lean_dec_ref(v_op_2204_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_keys_2207_);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2237_, lean_object* v_root_2238_, lean_object* v_todo_2239_, lean_object* v_keys_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
uint8_t v_root_boxed_2246_; lean_object* v_res_2247_; 
v_root_boxed_2246_ = lean_unbox(v_root_2238_);
v_res_2247_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2237_, v_root_boxed_2246_, v_todo_2239_, v_keys_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_op_2255_; lean_object* v___x_2256_; lean_object* v_todo_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_op_2255_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2256_ = lean_unsigned_to_nat(8u);
v_todo_2257_ = lean_mk_empty_array_with_capacity(v___x_2256_);
v___x_2258_ = 1;
lean_inc_ref(v_todo_2257_);
v___x_2259_ = lean_array_push(v_todo_2257_, v_e_2249_);
v___x_2260_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2255_, v___x_2258_, v___x_2259_, v_todo_2257_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2268_, lean_object* v_todo_2269_, lean_object* v_e_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = 1;
v___x_2277_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2270_, v___x_2276_, v_root_2268_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2295_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2295_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2295_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2294_; 
v_fst_2282_ = lean_ctor_get(v_a_2278_, 0);
v_snd_2283_ = lean_ctor_get(v_a_2278_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_a_2278_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2285_ = v_a_2278_;
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_snd_2283_);
lean_inc(v_fst_2282_);
lean_dec(v_a_2278_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = l_Array_append___redArg(v_todo_2269_, v_snd_2283_);
lean_dec(v_snd_2283_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___x_2287_);
v___x_2289_ = v___x_2285_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_fst_2282_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2291_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2289_);
v___x_2291_ = v___x_2280_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2269_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2296_, lean_object* v_todo_2297_, lean_object* v_e_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
uint8_t v_root_boxed_2304_; lean_object* v_res_2305_; 
v_root_boxed_2304_ = lean_unbox(v_root_2296_);
v_res_2305_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2304_, v_todo_2297_, v_e_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_op_2313_; lean_object* v___x_2314_; lean_object* v_todo_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_op_2313_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2314_ = lean_unsigned_to_nat(8u);
v_todo_2315_ = lean_mk_empty_array_with_capacity(v___x_2314_);
v___x_2316_ = 1;
lean_inc_ref(v_todo_2315_);
v___x_2317_ = lean_array_push(v_todo_2315_, v_e_2307_);
v___x_2318_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2313_, v___x_2316_, v___x_2317_, v_todo_2315_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
return v_res_2325_;
}
}
static uint64_t _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0(void){
_start:
{
uint8_t v___x_2326_; uint64_t v___x_2327_; 
v___x_2326_ = 2;
v___x_2327_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2328_, lean_object* v_m_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_tries_2335_; lean_object* v_roots_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2408_; 
v_tries_2335_ = lean_ctor_get(v_d_2328_, 0);
v_roots_2336_ = lean_ctor_get(v_d_2328_, 1);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_d_2328_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2338_ = v_d_2328_;
v_isShared_2339_ = v_isSharedCheck_2408_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_roots_2336_);
lean_inc(v_tries_2335_);
lean_dec(v_d_2328_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2408_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; uint8_t v_foApprox_2341_; uint8_t v_ctxApprox_2342_; uint8_t v_quasiPatternApprox_2343_; uint8_t v_constApprox_2344_; uint8_t v_isDefEqStuckEx_2345_; uint8_t v_unificationHints_2346_; uint8_t v_proofIrrelevance_2347_; uint8_t v_assignSyntheticOpaque_2348_; uint8_t v_offsetCnstrs_2349_; uint8_t v_etaStruct_2350_; uint8_t v_univApprox_2351_; uint8_t v_iota_2352_; uint8_t v_beta_2353_; uint8_t v_proj_2354_; uint8_t v_zeta_2355_; uint8_t v_zetaDelta_2356_; uint8_t v_zetaUnused_2357_; uint8_t v_zetaHave_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2407_; 
v___x_2340_ = l_Lean_Meta_Context_config(v_a_2330_);
v_foApprox_2341_ = lean_ctor_get_uint8(v___x_2340_, 0);
v_ctxApprox_2342_ = lean_ctor_get_uint8(v___x_2340_, 1);
v_quasiPatternApprox_2343_ = lean_ctor_get_uint8(v___x_2340_, 2);
v_constApprox_2344_ = lean_ctor_get_uint8(v___x_2340_, 3);
v_isDefEqStuckEx_2345_ = lean_ctor_get_uint8(v___x_2340_, 4);
v_unificationHints_2346_ = lean_ctor_get_uint8(v___x_2340_, 5);
v_proofIrrelevance_2347_ = lean_ctor_get_uint8(v___x_2340_, 6);
v_assignSyntheticOpaque_2348_ = lean_ctor_get_uint8(v___x_2340_, 7);
v_offsetCnstrs_2349_ = lean_ctor_get_uint8(v___x_2340_, 8);
v_etaStruct_2350_ = lean_ctor_get_uint8(v___x_2340_, 10);
v_univApprox_2351_ = lean_ctor_get_uint8(v___x_2340_, 11);
v_iota_2352_ = lean_ctor_get_uint8(v___x_2340_, 12);
v_beta_2353_ = lean_ctor_get_uint8(v___x_2340_, 13);
v_proj_2354_ = lean_ctor_get_uint8(v___x_2340_, 14);
v_zeta_2355_ = lean_ctor_get_uint8(v___x_2340_, 15);
v_zetaDelta_2356_ = lean_ctor_get_uint8(v___x_2340_, 16);
v_zetaUnused_2357_ = lean_ctor_get_uint8(v___x_2340_, 17);
v_zetaHave_2358_ = lean_ctor_get_uint8(v___x_2340_, 18);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2360_ = v___x_2340_;
v_isShared_2361_ = v_isSharedCheck_2407_;
goto v_resetjp_2359_;
}
else
{
lean_dec(v___x_2340_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2407_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; uint8_t v_trackZetaDelta_2363_; lean_object* v_zetaDeltaSet_2364_; lean_object* v_lctx_2365_; lean_object* v_localInstances_2366_; lean_object* v_defEqCtx_x3f_2367_; lean_object* v_synthPendingDepth_2368_; lean_object* v_canUnfold_x3f_2369_; uint8_t v_univApprox_2370_; uint8_t v_inTypeClassResolution_2371_; uint8_t v_cacheInferType_2372_; uint8_t v___x_2373_; lean_object* v_config_2375_; 
v___x_2362_ = lean_st_mk_ref(v_tries_2335_);
v_trackZetaDelta_2363_ = lean_ctor_get_uint8(v_a_2330_, sizeof(void*)*7);
v_zetaDeltaSet_2364_ = lean_ctor_get(v_a_2330_, 1);
v_lctx_2365_ = lean_ctor_get(v_a_2330_, 2);
v_localInstances_2366_ = lean_ctor_get(v_a_2330_, 3);
v_defEqCtx_x3f_2367_ = lean_ctor_get(v_a_2330_, 4);
v_synthPendingDepth_2368_ = lean_ctor_get(v_a_2330_, 5);
v_canUnfold_x3f_2369_ = lean_ctor_get(v_a_2330_, 6);
v_univApprox_2370_ = lean_ctor_get_uint8(v_a_2330_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2371_ = lean_ctor_get_uint8(v_a_2330_, sizeof(void*)*7 + 2);
v_cacheInferType_2372_ = lean_ctor_get_uint8(v_a_2330_, sizeof(void*)*7 + 3);
v___x_2373_ = 2;
if (v_isShared_2361_ == 0)
{
v_config_2375_ = v___x_2360_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 0, v_foApprox_2341_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 1, v_ctxApprox_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 2, v_quasiPatternApprox_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 3, v_constApprox_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 4, v_isDefEqStuckEx_2345_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 5, v_unificationHints_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 6, v_proofIrrelevance_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 7, v_assignSyntheticOpaque_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 8, v_offsetCnstrs_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 10, v_etaStruct_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 11, v_univApprox_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 12, v_iota_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 13, v_beta_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 14, v_proj_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 15, v_zeta_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 16, v_zetaDelta_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 17, v_zetaUnused_2357_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, 18, v_zetaHave_2358_);
v_config_2375_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
uint64_t v___x_2376_; uint64_t v___x_2377_; uint64_t v___x_2378_; uint64_t v___x_2379_; uint64_t v___x_2380_; uint64_t v_key_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_ctor_set_uint8(v_config_2375_, 9, v___x_2373_);
v___x_2376_ = l_Lean_Meta_Context_configKey(v_a_2330_);
v___x_2377_ = 3ULL;
v___x_2378_ = lean_uint64_shift_right(v___x_2376_, v___x_2377_);
v___x_2379_ = lean_uint64_shift_left(v___x_2378_, v___x_2377_);
v___x_2380_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_2381_ = lean_uint64_lor(v___x_2379_, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2382_, 0, v_config_2375_);
lean_ctor_set_uint64(v___x_2382_, sizeof(void*)*1, v_key_2381_);
lean_inc(v_canUnfold_x3f_2369_);
lean_inc(v_synthPendingDepth_2368_);
lean_inc(v_defEqCtx_x3f_2367_);
lean_inc_ref(v_localInstances_2366_);
lean_inc_ref(v_lctx_2365_);
lean_inc(v_zetaDeltaSet_2364_);
v___x_2383_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v_zetaDeltaSet_2364_);
lean_ctor_set(v___x_2383_, 2, v_lctx_2365_);
lean_ctor_set(v___x_2383_, 3, v_localInstances_2366_);
lean_ctor_set(v___x_2383_, 4, v_defEqCtx_x3f_2367_);
lean_ctor_set(v___x_2383_, 5, v_synthPendingDepth_2368_);
lean_ctor_set(v___x_2383_, 6, v_canUnfold_x3f_2369_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7, v_trackZetaDelta_2363_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 1, v_univApprox_2370_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2371_);
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*7 + 3, v_cacheInferType_2372_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
lean_inc(v_a_2331_);
lean_inc(v___x_2362_);
v___x_2384_ = lean_apply_6(v_m_2329_, v___x_2362_, v___x_2383_, v_a_2331_, v_a_2332_, v_a_2333_, lean_box(0));
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2397_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_st_ref_get(v___x_2362_);
lean_dec(v___x_2362_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2389_);
v___x_2391_ = v___x_2338_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_roots_2336_);
v___x_2391_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_a_2385_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2392_);
v___x_2394_ = v___x_2387_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v___x_2362_);
lean_del_object(v___x_2338_);
lean_dec_ref(v_roots_2336_);
v_a_2398_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2384_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2384_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2409_, lean_object* v_m_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2409_, v_m_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2417_, lean_object* v_00_u03b2_2418_, lean_object* v_d_2419_, lean_object* v_m_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2419_, v_m_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2427_, lean_object* v_00_u03b2_2428_, lean_object* v_d_2429_, lean_object* v_m_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2427_, v_00_u03b2_2428_, v_d_2429_, v_m_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2437_, lean_object* v_v_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2441_ = lean_st_ref_take(v_a_2439_);
v___x_2442_ = lean_array_set(v___x_2441_, v_i_2437_, v_v_2438_);
v___x_2443_ = lean_st_ref_set(v_a_2439_, v___x_2442_);
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2446_, lean_object* v_v_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2446_, v_v_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec(v_i_2446_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2451_, lean_object* v_i_2452_, lean_object* v_v_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2452_, v_v_2453_, v_a_2454_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_i_2462_, lean_object* v_v_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2461_, v_i_2462_, v_v_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec(v_i_2462_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_sz_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_sz_2473_ = lean_array_get_size(v_a_2472_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2476_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = lean_mk_empty_array_with_capacity(v___x_2477_);
v___x_2479_ = lean_array_push(v___x_2478_, v_e_2471_);
v___x_2480_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2475_);
lean_ctor_set(v___x_2480_, 1, v___x_2474_);
lean_ctor_set(v___x_2480_, 2, v___x_2476_);
lean_ctor_set(v___x_2480_, 3, v___x_2479_);
v___x_2481_ = lean_array_push(v_a_2472_, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_sz_2473_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2483_, lean_object* v_e_2484_){
_start:
{
lean_object* v_modifyGet_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; 
v_modifyGet_2485_ = lean_ctor_get(v_inst_2483_, 2);
lean_inc(v_modifyGet_2485_);
lean_dec_ref(v_inst_2483_);
v___f_2486_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2486_, 0, v_e_2484_);
v___x_2487_ = lean_apply_2(v_modifyGet_2485_, lean_box(0), v___f_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2488_, lean_object* v_00_u03b1_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_e_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2491_, v_e_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2494_, lean_object* v_00_u03b1_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_e_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2494_, v_00_u03b1_2495_, v_inst_2496_, v_inst_2497_, v_e_2498_);
lean_dec_ref(v_inst_2496_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2500_, lean_object* v_e_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v___x_2504_; lean_object* v_fst_2506_; lean_object* v_snd_2507_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2504_ = lean_st_ref_take(v_a_2502_);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_array_get_size(v___x_2504_);
v___x_2512_ = lean_nat_dec_lt(v_i_2500_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_dec_ref(v_e_2501_);
v_fst_2506_ = v___x_2510_;
v_snd_2507_ = v___x_2504_;
goto v___jp_2505_;
}
else
{
lean_object* v_v_2513_; lean_object* v_xs_x27_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_v_2513_ = lean_array_fget(v___x_2504_, v_i_2500_);
v_xs_x27_2514_ = lean_array_fset(v___x_2504_, v_i_2500_, v___x_2510_);
v___x_2515_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2513_, v_e_2501_);
v___x_2516_ = lean_array_fset(v_xs_x27_2514_, v_i_2500_, v___x_2515_);
v_fst_2506_ = v___x_2510_;
v_snd_2507_ = v___x_2516_;
goto v___jp_2505_;
}
v___jp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_st_ref_set(v_a_2502_, v_snd_2507_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_fst_2506_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2517_, lean_object* v_e_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2517_, v_e_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec(v_i_2517_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2522_, lean_object* v_i_2523_, lean_object* v_e_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2523_, v_e_2524_, v_a_2525_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2532_, lean_object* v_i_2533_, lean_object* v_e_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2532_, v_i_2533_, v_e_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec(v_i_2533_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2549_; 
lean_inc(v___y_2543_);
v___x_2549_ = lean_apply_6(v_x_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, lean_box(0));
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2551_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2558_, lean_object* v_localInsts_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___f_2567_; lean_object* v___x_2568_; 
lean_inc(v___y_2561_);
v___f_2567_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2567_, 0, v_x_2560_);
lean_closure_set(v___f_2567_, 1, v___y_2561_);
v___x_2568_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2558_, v_localInsts_2559_, v___f_2567_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2568_) == 0)
{
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2577_, lean_object* v_localInsts_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2577_, v_localInsts_2578_, v_x_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2587_, lean_object* v_00_u03b1_2588_, lean_object* v_lctx_2589_, lean_object* v_localInsts_2590_, lean_object* v_x_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2589_, v_localInsts_2590_, v_x_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2599_, lean_object* v_00_u03b1_2600_, lean_object* v_lctx_2601_, lean_object* v_localInsts_2602_, lean_object* v_x_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2599_, v_00_u03b1_2600_, v_lctx_2601_, v_localInsts_2602_, v_x_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; lean_object* v_sz_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2614_ = lean_st_ref_take(v___y_2612_);
v_sz_2615_ = lean_array_get_size(v___x_2614_);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2618_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2619_ = lean_unsigned_to_nat(1u);
v___x_2620_ = lean_mk_empty_array_with_capacity(v___x_2619_);
v___x_2621_ = lean_array_push(v___x_2620_, v_e_2611_);
v___x_2622_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2617_);
lean_ctor_set(v___x_2622_, 1, v___x_2616_);
lean_ctor_set(v___x_2622_, 2, v___x_2618_);
lean_ctor_set(v___x_2622_, 3, v___x_2621_);
v___x_2623_ = lean_array_push(v___x_2614_, v___x_2622_);
v___x_2624_ = lean_st_ref_set(v___y_2612_, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_sz_2615_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2626_, v___y_2627_);
lean_dec(v___y_2627_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2630_, lean_object* v_e_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2631_, v___y_2632_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2639_, lean_object* v_e_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2639_, v_e_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2648_, lean_object* v_todo_2649_, lean_object* v_e_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2648_, v_todo_2649_, v_e_2650_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2658_, lean_object* v_todo_2659_, lean_object* v_e_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
uint8_t v___x_4138__boxed_2667_; lean_object* v_res_2668_; 
v___x_4138__boxed_2667_ = lean_unbox(v___x_2658_);
v_res_2668_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_4138__boxed_2667_, v_todo_2659_, v_e_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2669_, lean_object* v_b_2670_, lean_object* v_x_2671_){
_start:
{
if (lean_obj_tag(v_x_2671_) == 0)
{
lean_dec(v_b_2670_);
lean_dec(v_a_2669_);
return v_x_2671_;
}
else
{
lean_object* v_key_2672_; lean_object* v_value_2673_; lean_object* v_tail_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2686_; 
v_key_2672_ = lean_ctor_get(v_x_2671_, 0);
v_value_2673_ = lean_ctor_get(v_x_2671_, 1);
v_tail_2674_ = lean_ctor_get(v_x_2671_, 2);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_x_2671_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2676_ = v_x_2671_;
v_isShared_2677_ = v_isSharedCheck_2686_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_tail_2674_);
lean_inc(v_value_2673_);
lean_inc(v_key_2672_);
lean_dec(v_x_2671_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2686_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
uint8_t v___x_2678_; 
v___x_2678_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2672_, v_a_2669_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2679_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2669_, v_b_2670_, v_tail_2674_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 2, v___x_2679_);
v___x_2681_ = v___x_2676_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_value_2673_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
else
{
lean_object* v___x_2684_; 
lean_dec(v_value_2673_);
lean_dec(v_key_2672_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 1, v_b_2670_);
lean_ctor_set(v___x_2676_, 0, v_a_2669_);
v___x_2684_ = v___x_2676_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2669_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_b_2670_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_tail_2674_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2687_, lean_object* v_x_2688_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
uint8_t v___x_2689_; 
v___x_2689_ = 0;
return v___x_2689_;
}
else
{
lean_object* v_key_2690_; lean_object* v_tail_2691_; uint8_t v___x_2692_; 
v_key_2690_ = lean_ctor_get(v_x_2688_, 0);
v_tail_2691_ = lean_ctor_get(v_x_2688_, 2);
v___x_2692_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2690_, v_a_2687_);
if (v___x_2692_ == 0)
{
v_x_2688_ = v_tail_2691_;
goto _start;
}
else
{
return v___x_2692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2694_, lean_object* v_x_2695_){
_start:
{
uint8_t v_res_2696_; lean_object* v_r_2697_; 
v_res_2696_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2694_, v_x_2695_);
lean_dec(v_x_2695_);
lean_dec(v_a_2694_);
v_r_2697_ = lean_box(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
if (lean_obj_tag(v_x_2699_) == 0)
{
return v_x_2698_;
}
else
{
lean_object* v_key_2700_; lean_object* v_value_2701_; lean_object* v_tail_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2725_; 
v_key_2700_ = lean_ctor_get(v_x_2699_, 0);
v_value_2701_ = lean_ctor_get(v_x_2699_, 1);
v_tail_2702_ = lean_ctor_get(v_x_2699_, 2);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_x_2699_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2704_ = v_x_2699_;
v_isShared_2705_ = v_isSharedCheck_2725_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_tail_2702_);
lean_inc(v_value_2701_);
lean_inc(v_key_2700_);
lean_dec(v_x_2699_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2725_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; uint64_t v___x_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; uint64_t v_fold_2710_; uint64_t v___x_2711_; uint64_t v___x_2712_; uint64_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2706_ = lean_array_get_size(v_x_2698_);
v___x_2707_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2700_);
v___x_2708_ = 32ULL;
v___x_2709_ = lean_uint64_shift_right(v___x_2707_, v___x_2708_);
v_fold_2710_ = lean_uint64_xor(v___x_2707_, v___x_2709_);
v___x_2711_ = 16ULL;
v___x_2712_ = lean_uint64_shift_right(v_fold_2710_, v___x_2711_);
v___x_2713_ = lean_uint64_xor(v_fold_2710_, v___x_2712_);
v___x_2714_ = lean_uint64_to_usize(v___x_2713_);
v___x_2715_ = lean_usize_of_nat(v___x_2706_);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_sub(v___x_2715_, v___x_2716_);
v___x_2718_ = lean_usize_land(v___x_2714_, v___x_2717_);
v___x_2719_ = lean_array_uget_borrowed(v_x_2698_, v___x_2718_);
lean_inc(v___x_2719_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 2, v___x_2719_);
v___x_2721_ = v___x_2704_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_key_2700_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_value_2701_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_array_uset(v_x_2698_, v___x_2718_, v___x_2721_);
v_x_2698_ = v___x_2722_;
v_x_2699_ = v_tail_2702_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2726_, lean_object* v_source_2727_, lean_object* v_target_2728_){
_start:
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = lean_array_get_size(v_source_2727_);
v___x_2730_ = lean_nat_dec_lt(v_i_2726_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_dec_ref(v_source_2727_);
lean_dec(v_i_2726_);
return v_target_2728_;
}
else
{
lean_object* v_es_2731_; lean_object* v___x_2732_; lean_object* v_source_2733_; lean_object* v_target_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_es_2731_ = lean_array_fget(v_source_2727_, v_i_2726_);
v___x_2732_ = lean_box(0);
v_source_2733_ = lean_array_fset(v_source_2727_, v_i_2726_, v___x_2732_);
v_target_2734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2728_, v_es_2731_);
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_add(v_i_2726_, v___x_2735_);
lean_dec(v_i_2726_);
v_i_2726_ = v___x_2736_;
v_source_2727_ = v_source_2733_;
v_target_2728_ = v_target_2734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2738_){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v_nbuckets_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2739_ = lean_array_get_size(v_data_2738_);
v___x_2740_ = lean_unsigned_to_nat(2u);
v_nbuckets_2741_ = lean_nat_mul(v___x_2739_, v___x_2740_);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_mk_array(v_nbuckets_2741_, v___x_2743_);
v___x_2745_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2742_, v_data_2738_, v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2746_, lean_object* v_a_2747_, lean_object* v_b_2748_){
_start:
{
lean_object* v_size_2749_; lean_object* v_buckets_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2793_; 
v_size_2749_ = lean_ctor_get(v_m_2746_, 0);
v_buckets_2750_ = lean_ctor_get(v_m_2746_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_m_2746_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2752_ = v_m_2746_;
v_isShared_2753_ = v_isSharedCheck_2793_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_buckets_2750_);
lean_inc(v_size_2749_);
lean_dec(v_m_2746_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2793_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; uint64_t v___x_2755_; uint64_t v___x_2756_; uint64_t v___x_2757_; uint64_t v_fold_2758_; uint64_t v___x_2759_; uint64_t v___x_2760_; uint64_t v___x_2761_; size_t v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; size_t v___x_2766_; lean_object* v_bkt_2767_; uint8_t v___x_2768_; 
v___x_2754_ = lean_array_get_size(v_buckets_2750_);
v___x_2755_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2747_);
v___x_2756_ = 32ULL;
v___x_2757_ = lean_uint64_shift_right(v___x_2755_, v___x_2756_);
v_fold_2758_ = lean_uint64_xor(v___x_2755_, v___x_2757_);
v___x_2759_ = 16ULL;
v___x_2760_ = lean_uint64_shift_right(v_fold_2758_, v___x_2759_);
v___x_2761_ = lean_uint64_xor(v_fold_2758_, v___x_2760_);
v___x_2762_ = lean_uint64_to_usize(v___x_2761_);
v___x_2763_ = lean_usize_of_nat(v___x_2754_);
v___x_2764_ = ((size_t)1ULL);
v___x_2765_ = lean_usize_sub(v___x_2763_, v___x_2764_);
v___x_2766_ = lean_usize_land(v___x_2762_, v___x_2765_);
v_bkt_2767_ = lean_array_uget_borrowed(v_buckets_2750_, v___x_2766_);
v___x_2768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2747_, v_bkt_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v_size_x27_2770_; lean_object* v___x_2771_; lean_object* v_buckets_x27_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2769_ = lean_unsigned_to_nat(1u);
v_size_x27_2770_ = lean_nat_add(v_size_2749_, v___x_2769_);
lean_dec(v_size_2749_);
lean_inc(v_bkt_2767_);
v___x_2771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2747_);
lean_ctor_set(v___x_2771_, 1, v_b_2748_);
lean_ctor_set(v___x_2771_, 2, v_bkt_2767_);
v_buckets_x27_2772_ = lean_array_uset(v_buckets_2750_, v___x_2766_, v___x_2771_);
v___x_2773_ = lean_unsigned_to_nat(4u);
v___x_2774_ = lean_nat_mul(v_size_x27_2770_, v___x_2773_);
v___x_2775_ = lean_unsigned_to_nat(3u);
v___x_2776_ = lean_nat_div(v___x_2774_, v___x_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_array_get_size(v_buckets_x27_2772_);
v___x_2778_ = lean_nat_dec_le(v___x_2776_, v___x_2777_);
lean_dec(v___x_2776_);
if (v___x_2778_ == 0)
{
lean_object* v_val_2779_; lean_object* v___x_2781_; 
v_val_2779_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2772_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v_val_2779_);
lean_ctor_set(v___x_2752_, 0, v_size_x27_2770_);
v___x_2781_ = v___x_2752_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_size_x27_2770_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_val_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
else
{
lean_object* v___x_2784_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v_buckets_x27_2772_);
lean_ctor_set(v___x_2752_, 0, v_size_x27_2770_);
v___x_2784_ = v___x_2752_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_size_x27_2770_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_buckets_x27_2772_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
else
{
lean_object* v___x_2786_; lean_object* v_buckets_x27_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
lean_inc(v_bkt_2767_);
v___x_2786_ = lean_box(0);
v_buckets_x27_2787_ = lean_array_uset(v_buckets_2750_, v___x_2766_, v___x_2786_);
v___x_2788_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2747_, v_b_2748_, v_bkt_2767_);
v___x_2789_ = lean_array_uset(v_buckets_x27_2787_, v___x_2766_, v___x_2788_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v___x_2789_);
v___x_2791_ = v___x_2752_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_size_2749_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2794_, lean_object* v_x_2795_){
_start:
{
if (lean_obj_tag(v_x_2795_) == 0)
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_box(0);
return v___x_2796_;
}
else
{
lean_object* v_key_2797_; lean_object* v_value_2798_; lean_object* v_tail_2799_; uint8_t v___x_2800_; 
v_key_2797_ = lean_ctor_get(v_x_2795_, 0);
v_value_2798_ = lean_ctor_get(v_x_2795_, 1);
v_tail_2799_ = lean_ctor_get(v_x_2795_, 2);
v___x_2800_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2797_, v_a_2794_);
if (v___x_2800_ == 0)
{
v_x_2795_ = v_tail_2799_;
goto _start;
}
else
{
lean_object* v___x_2802_; 
lean_inc(v_value_2798_);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_value_2798_);
return v___x_2802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2803_, v_x_2804_);
lean_dec(v_x_2804_);
lean_dec(v_a_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_buckets_2808_; lean_object* v___x_2809_; uint64_t v___x_2810_; uint64_t v___x_2811_; uint64_t v___x_2812_; uint64_t v_fold_2813_; uint64_t v___x_2814_; uint64_t v___x_2815_; uint64_t v___x_2816_; size_t v___x_2817_; size_t v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_buckets_2808_ = lean_ctor_get(v_m_2806_, 1);
v___x_2809_ = lean_array_get_size(v_buckets_2808_);
v___x_2810_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2807_);
v___x_2811_ = 32ULL;
v___x_2812_ = lean_uint64_shift_right(v___x_2810_, v___x_2811_);
v_fold_2813_ = lean_uint64_xor(v___x_2810_, v___x_2812_);
v___x_2814_ = 16ULL;
v___x_2815_ = lean_uint64_shift_right(v_fold_2813_, v___x_2814_);
v___x_2816_ = lean_uint64_xor(v_fold_2813_, v___x_2815_);
v___x_2817_ = lean_uint64_to_usize(v___x_2816_);
v___x_2818_ = lean_usize_of_nat(v___x_2809_);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_sub(v___x_2818_, v___x_2819_);
v___x_2821_ = lean_usize_land(v___x_2817_, v___x_2820_);
v___x_2822_ = lean_array_uget_borrowed(v_buckets_2808_, v___x_2821_);
v___x_2823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2807_, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2824_, v_a_2825_);
lean_dec(v_a_2825_);
lean_dec_ref(v_m_2824_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2827_, lean_object* v_entry_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_snd_2835_; lean_object* v_snd_2836_; lean_object* v_fst_2837_; lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v_fst_2840_; lean_object* v_fst_2841_; lean_object* v_snd_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_snd_2835_ = lean_ctor_get(v_p_2827_, 1);
v_snd_2836_ = lean_ctor_get(v_entry_2828_, 1);
lean_inc(v_snd_2836_);
v_fst_2837_ = lean_ctor_get(v_p_2827_, 0);
v_fst_2838_ = lean_ctor_get(v_snd_2835_, 0);
v_snd_2839_ = lean_ctor_get(v_snd_2835_, 1);
v_fst_2840_ = lean_ctor_get(v_entry_2828_, 0);
lean_inc(v_fst_2840_);
lean_dec_ref(v_entry_2828_);
v_fst_2841_ = lean_ctor_get(v_snd_2836_, 0);
lean_inc(v_fst_2841_);
v_snd_2842_ = lean_ctor_get(v_snd_2836_, 1);
v___x_2843_ = lean_array_get_size(v_fst_2840_);
v___x_2844_ = lean_unsigned_to_nat(0u);
v___x_2845_ = lean_nat_dec_eq(v___x_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v_fst_2846_; lean_object* v_snd_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2952_; 
v_fst_2846_ = lean_ctor_get(v_fst_2841_, 0);
v_snd_2847_ = lean_ctor_get(v_fst_2841_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_fst_2841_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2849_ = v_fst_2841_;
v_isShared_2850_ = v_isSharedCheck_2952_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_snd_2847_);
lean_inc(v_fst_2846_);
lean_dec(v_fst_2841_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2952_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v_e_2854_; lean_object* v_todo_2855_; lean_object* v___x_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; 
v___x_2851_ = l_Lean_instInhabitedExpr;
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = lean_nat_sub(v___x_2843_, v___x_2852_);
v_e_2854_ = lean_array_get(v___x_2851_, v_fst_2840_, v___x_2853_);
lean_dec(v___x_2853_);
v_todo_2855_ = lean_array_pop(v_fst_2840_);
v___x_2856_ = lean_box(v___x_2845_);
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2857_, 0, v___x_2856_);
lean_closure_set(v___f_2857_, 1, v_todo_2855_);
lean_closure_set(v___f_2857_, 2, v_e_2854_);
v___x_2858_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2846_, v_snd_2847_, v___f_2857_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v_fst_2860_; lean_object* v_snd_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2943_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v_fst_2860_ = lean_ctor_get(v_a_2859_, 0);
v_snd_2861_ = lean_ctor_get(v_a_2859_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_a_2859_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2863_ = v_a_2859_;
v_isShared_2864_ = v_isSharedCheck_2943_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_snd_2861_);
lean_inc(v_fst_2860_);
lean_dec(v_a_2859_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2943_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = lean_box(3);
v___x_2866_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2860_, v___x_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2839_, v_fst_2860_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v___x_2869_; 
lean_inc(v_snd_2839_);
lean_inc(v_fst_2838_);
lean_inc(v_fst_2837_);
lean_dec_ref(v_p_2827_);
lean_inc(v_snd_2836_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v_snd_2836_);
lean_ctor_set(v___x_2863_, 0, v_snd_2861_);
v___x_2869_ = v___x_2863_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_snd_2861_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_snd_2836_);
v___x_2869_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2889_; 
v_isSharedCheck_2889_ = !lean_is_exclusive(v_snd_2836_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; lean_object* v_unused_2891_; 
v_unused_2890_ = lean_ctor_get(v_snd_2836_, 1);
lean_dec(v_unused_2890_);
v_unused_2891_ = lean_ctor_get(v_snd_2836_, 0);
lean_dec(v_unused_2891_);
v___x_2871_ = v_snd_2836_;
v_isShared_2872_ = v_isSharedCheck_2889_;
goto v_resetjp_2870_;
}
else
{
lean_dec(v_snd_2836_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2889_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2888_; 
v___x_2873_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2869_, v_a_2829_);
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2888_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2888_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2878_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2839_, v_fst_2860_, v_a_2874_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2878_);
lean_ctor_set(v___x_2849_, 0, v_fst_2838_);
v___x_2880_ = v___x_2849_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_fst_2838_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 1, v___x_2880_);
lean_ctor_set(v___x_2871_, 0, v_fst_2837_);
v___x_2882_ = v___x_2871_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_fst_2837_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2882_);
v___x_2884_ = v___x_2876_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2893_; lean_object* v___x_2895_; 
lean_dec(v_fst_2860_);
lean_del_object(v___x_2849_);
v_val_2893_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_val_2893_);
lean_dec_ref_known(v___x_2867_, 1);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v_snd_2836_);
lean_ctor_set(v___x_2863_, 0, v_snd_2861_);
v___x_2895_ = v___x_2863_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_snd_2861_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_snd_2836_);
v___x_2895_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v___x_2896_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2893_, v___x_2895_, v_a_2829_);
lean_dec(v_val_2893_);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v___x_2896_, 0);
lean_dec(v_unused_2904_);
v___x_2898_ = v___x_2896_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v___x_2896_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v_p_2827_);
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_p_2827_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
else
{
uint8_t v___x_2906_; 
lean_dec(v_fst_2860_);
v___x_2906_ = lean_nat_dec_eq(v_fst_2838_, v___x_2844_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2908_; 
lean_del_object(v___x_2849_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v_snd_2836_);
lean_ctor_set(v___x_2863_, 0, v_snd_2861_);
v___x_2908_ = v___x_2863_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_snd_2861_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_snd_2836_);
v___x_2908_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v___x_2909_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2838_, v___x_2908_, v_a_2829_);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v___x_2909_, 0);
lean_dec(v_unused_2917_);
v___x_2911_ = v___x_2909_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_dec(v___x_2909_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v_p_2827_);
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_p_2827_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v___x_2920_; 
lean_inc(v_snd_2839_);
lean_inc(v_fst_2837_);
lean_dec_ref(v_p_2827_);
lean_inc(v_snd_2836_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 1, v_snd_2836_);
lean_ctor_set(v___x_2863_, 0, v_snd_2861_);
v___x_2920_ = v___x_2863_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_snd_2861_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_snd_2836_);
v___x_2920_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2939_; 
v_isSharedCheck_2939_ = !lean_is_exclusive(v_snd_2836_);
if (v_isSharedCheck_2939_ == 0)
{
lean_object* v_unused_2940_; lean_object* v_unused_2941_; 
v_unused_2940_ = lean_ctor_get(v_snd_2836_, 1);
lean_dec(v_unused_2940_);
v_unused_2941_ = lean_ctor_get(v_snd_2836_, 0);
lean_dec(v_unused_2941_);
v___x_2922_ = v_snd_2836_;
v_isShared_2923_ = v_isSharedCheck_2939_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v_snd_2836_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2939_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2938_; 
v___x_2924_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2920_, v_a_2829_);
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2938_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2938_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v_snd_2839_);
lean_ctor_set(v___x_2849_, 0, v_a_2925_);
v___x_2930_ = v___x_2849_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2925_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_snd_2839_);
v___x_2930_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2932_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v___x_2930_);
lean_ctor_set(v___x_2922_, 0, v_fst_2837_);
v___x_2932_ = v___x_2922_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_fst_2837_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2934_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2932_);
v___x_2934_ = v___x_2927_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
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
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_del_object(v___x_2849_);
lean_dec(v_snd_2836_);
lean_dec_ref(v_p_2827_);
v_a_2944_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2858_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2858_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
else
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2961_; 
lean_inc(v_snd_2842_);
lean_inc(v_fst_2837_);
lean_inc(v_snd_2835_);
lean_dec(v_fst_2841_);
lean_dec(v_fst_2840_);
lean_dec_ref(v_p_2827_);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_snd_2836_);
if (v_isSharedCheck_2961_ == 0)
{
lean_object* v_unused_2962_; lean_object* v_unused_2963_; 
v_unused_2962_ = lean_ctor_get(v_snd_2836_, 1);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v_snd_2836_, 0);
lean_dec(v_unused_2963_);
v___x_2954_ = v_snd_2836_;
v_isShared_2955_ = v_isSharedCheck_2961_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v_snd_2836_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2961_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_values_2956_; lean_object* v___x_2958_; 
v_values_2956_ = lean_array_push(v_fst_2837_, v_snd_2842_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v_snd_2835_);
lean_ctor_set(v___x_2954_, 0, v_values_2956_);
v___x_2958_ = v___x_2954_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_values_2956_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v_snd_2835_);
v___x_2958_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2964_, lean_object* v_entry_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2964_, v_entry_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2973_, lean_object* v_p_2974_, lean_object* v_entry_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2974_, v_entry_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2983_, lean_object* v_p_2984_, lean_object* v_entry_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2983_, v_p_2984_, v_entry_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2993_, lean_object* v_m_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2994_, v_a_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2997_, lean_object* v_m_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2997_, v_m_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_m_2998_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_3001_, lean_object* v_m_3002_, lean_object* v_a_3003_, lean_object* v_b_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_3002_, v_a_3003_, v_b_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_3006_, lean_object* v_a_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_3007_, v_x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3010_, lean_object* v_a_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_3010_, v_a_3011_, v_x_3012_);
lean_dec(v_x_3012_);
lean_dec(v_a_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_3014_, lean_object* v_a_3015_, lean_object* v_x_3016_){
_start:
{
uint8_t v___x_3017_; 
v___x_3017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_3015_, v_x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3018_, lean_object* v_a_3019_, lean_object* v_x_3020_){
_start:
{
uint8_t v_res_3021_; lean_object* v_r_3022_; 
v_res_3021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_3018_, v_a_3019_, v_x_3020_);
lean_dec(v_x_3020_);
lean_dec(v_a_3019_);
v_r_3022_ = lean_box(v_res_3021_);
return v_r_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_3023_, lean_object* v_data_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3026_, lean_object* v_a_3027_, lean_object* v_b_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3027_, v_b_3028_, v_x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3031_, lean_object* v_i_3032_, lean_object* v_source_3033_, lean_object* v_target_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3032_, v_source_3033_, v_target_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3036_, lean_object* v_x_3037_, lean_object* v_x_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3037_, v_x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3040_, size_t v_i_3041_, size_t v_stop_3042_, lean_object* v_b_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_eq(v_i_3041_, v_stop_3042_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_array_uget_borrowed(v_as_3040_, v_i_3041_);
lean_inc(v___x_3051_);
v___x_3052_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3043_, v___x_3051_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; size_t v___x_3054_; size_t v___x_3055_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = ((size_t)1ULL);
v___x_3055_ = lean_usize_add(v_i_3041_, v___x_3054_);
v_i_3041_ = v___x_3055_;
v_b_3043_ = v_a_3053_;
goto _start;
}
else
{
return v___x_3052_;
}
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_b_3043_);
return v___x_3057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3058_, lean_object* v_i_3059_, lean_object* v_stop_3060_, lean_object* v_b_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
size_t v_i_boxed_3068_; size_t v_stop_boxed_3069_; lean_object* v_res_3070_; 
v_i_boxed_3068_ = lean_unbox_usize(v_i_3059_);
lean_dec(v_i_3059_);
v_stop_boxed_3069_ = lean_unbox_usize(v_stop_3060_);
lean_dec(v_stop_3060_);
v_res_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3058_, v_i_boxed_3068_, v_stop_boxed_3069_, v_b_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v_as_3058_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3071_, lean_object* v_starIdx_3072_, lean_object* v_children_3073_, lean_object* v_entries_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v_starIdx_3072_);
lean_ctor_set(v___x_3081_, 1, v_children_3073_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v_values_3071_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = lean_array_get_size(v_entries_3074_);
v___x_3085_ = lean_nat_dec_lt(v___x_3083_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3082_);
return v___x_3086_;
}
else
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_nat_dec_le(v___x_3084_, v___x_3084_);
if (v___x_3087_ == 0)
{
if (v___x_3085_ == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3082_);
return v___x_3088_;
}
else
{
size_t v___x_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((size_t)0ULL);
v___x_3090_ = lean_usize_of_nat(v___x_3084_);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3074_, v___x_3089_, v___x_3090_, v___x_3082_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3091_;
}
}
else
{
size_t v___x_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((size_t)0ULL);
v___x_3093_ = lean_usize_of_nat(v___x_3084_);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3074_, v___x_3092_, v___x_3093_, v___x_3082_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3095_, lean_object* v_starIdx_3096_, lean_object* v_children_3097_, lean_object* v_entries_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3095_, v_starIdx_3096_, v_children_3097_, v_entries_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_entries_3098_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3106_, lean_object* v_values_3107_, lean_object* v_starIdx_3108_, lean_object* v_children_3109_, lean_object* v_entries_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3107_, v_starIdx_3108_, v_children_3109_, v_entries_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_values_3119_, lean_object* v_starIdx_3120_, lean_object* v_children_3121_, lean_object* v_entries_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3118_, v_values_3119_, v_starIdx_3120_, v_children_3121_, v_entries_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_entries_3122_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3130_, lean_object* v_as_3131_, size_t v_i_3132_, size_t v_stop_3133_, lean_object* v_b_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3131_, v_i_3132_, v_stop_3133_, v_b_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3142_, lean_object* v_as_3143_, lean_object* v_i_3144_, lean_object* v_stop_3145_, lean_object* v_b_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
size_t v_i_boxed_3153_; size_t v_stop_boxed_3154_; lean_object* v_res_3155_; 
v_i_boxed_3153_ = lean_unbox_usize(v_i_3144_);
lean_dec(v_i_3144_);
v_stop_boxed_3154_ = lean_unbox_usize(v_stop_3145_);
lean_dec(v_stop_3145_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3142_, v_as_3143_, v_i_boxed_3153_, v_stop_boxed_3154_, v_b_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v_as_3143_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v_values_3166_; lean_object* v_star_3167_; lean_object* v_children_3168_; lean_object* v_pending_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3199_; 
v___x_3163_ = lean_st_ref_get(v_a_3157_);
v___x_3164_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3165_ = lean_array_get(v___x_3164_, v___x_3163_, v_c_3156_);
lean_dec(v___x_3163_);
v_values_3166_ = lean_ctor_get(v___x_3165_, 0);
v_star_3167_ = lean_ctor_get(v___x_3165_, 1);
v_children_3168_ = lean_ctor_get(v___x_3165_, 2);
v_pending_3169_ = lean_ctor_get(v___x_3165_, 3);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3171_ = v___x_3165_;
v_isShared_3172_ = v_isSharedCheck_3199_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_pending_3169_);
lean_inc(v_children_3168_);
lean_inc(v_star_3167_);
lean_inc(v_values_3166_);
lean_dec(v___x_3165_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3199_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3173_ = lean_array_get_size(v_pending_3169_);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_nat_dec_eq(v___x_3173_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3156_, v___x_3164_, v_a_3157_);
lean_dec_ref(v___x_3176_);
v___x_3177_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3166_, v_star_3167_, v_children_3168_, v_pending_3169_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
lean_dec_ref(v_pending_3169_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v_snd_3179_; lean_object* v_fst_3180_; lean_object* v_fst_3181_; lean_object* v_snd_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v_snd_3179_ = lean_ctor_get(v_a_3178_, 1);
v_fst_3180_ = lean_ctor_get(v_a_3178_, 0);
v_fst_3181_ = lean_ctor_get(v_snd_3179_, 0);
v_snd_3182_ = lean_ctor_get(v_snd_3179_, 1);
v___x_3183_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
lean_inc(v_snd_3182_);
lean_inc(v_fst_3181_);
lean_inc(v_fst_3180_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 3, v___x_3183_);
lean_ctor_set(v___x_3171_, 2, v_snd_3182_);
lean_ctor_set(v___x_3171_, 1, v_fst_3181_);
lean_ctor_set(v___x_3171_, 0, v_fst_3180_);
v___x_3185_ = v___x_3171_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_fst_3180_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_fst_3181_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_snd_3182_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
v___x_3186_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3156_, v___x_3185_, v_a_3157_);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v___x_3186_, 0);
lean_dec(v_unused_3194_);
v___x_3188_ = v___x_3186_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_dec(v___x_3186_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v_a_3178_);
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3178_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_del_object(v___x_3171_);
return v___x_3177_;
}
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
lean_del_object(v___x_3171_);
lean_dec_ref(v_pending_3169_);
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v_star_3167_);
lean_ctor_set(v___x_3196_, 1, v_children_3168_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_values_3166_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
return v___x_3198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec(v_a_3201_);
lean_dec(v_c_3200_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3208_, lean_object* v_c_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3217_, lean_object* v_c_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3217_, v_c_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec(v_c_3218_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3226_, lean_object* v_fallback_3227_, lean_object* v_x_3228_){
_start:
{
if (lean_obj_tag(v_x_3228_) == 0)
{
lean_inc(v_fallback_3227_);
return v_fallback_3227_;
}
else
{
lean_object* v_key_3229_; lean_object* v_value_3230_; lean_object* v_tail_3231_; uint8_t v___x_3232_; 
v_key_3229_ = lean_ctor_get(v_x_3228_, 0);
v_value_3230_ = lean_ctor_get(v_x_3228_, 1);
v_tail_3231_ = lean_ctor_get(v_x_3228_, 2);
v___x_3232_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3229_, v_a_3226_);
if (v___x_3232_ == 0)
{
v_x_3228_ = v_tail_3231_;
goto _start;
}
else
{
lean_inc(v_value_3230_);
return v_value_3230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3234_, lean_object* v_fallback_3235_, lean_object* v_x_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3234_, v_fallback_3235_, v_x_3236_);
lean_dec(v_x_3236_);
lean_dec(v_fallback_3235_);
lean_dec(v_a_3234_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3238_, lean_object* v_a_3239_, lean_object* v_fallback_3240_){
_start:
{
lean_object* v_buckets_3241_; lean_object* v___x_3242_; uint64_t v___x_3243_; uint64_t v___x_3244_; uint64_t v___x_3245_; uint64_t v_fold_3246_; uint64_t v___x_3247_; uint64_t v___x_3248_; uint64_t v___x_3249_; size_t v___x_3250_; size_t v___x_3251_; size_t v___x_3252_; size_t v___x_3253_; size_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_buckets_3241_ = lean_ctor_get(v_m_3238_, 1);
v___x_3242_ = lean_array_get_size(v_buckets_3241_);
v___x_3243_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3239_);
v___x_3244_ = 32ULL;
v___x_3245_ = lean_uint64_shift_right(v___x_3243_, v___x_3244_);
v_fold_3246_ = lean_uint64_xor(v___x_3243_, v___x_3245_);
v___x_3247_ = 16ULL;
v___x_3248_ = lean_uint64_shift_right(v_fold_3246_, v___x_3247_);
v___x_3249_ = lean_uint64_xor(v_fold_3246_, v___x_3248_);
v___x_3250_ = lean_uint64_to_usize(v___x_3249_);
v___x_3251_ = lean_usize_of_nat(v___x_3242_);
v___x_3252_ = ((size_t)1ULL);
v___x_3253_ = lean_usize_sub(v___x_3251_, v___x_3252_);
v___x_3254_ = lean_usize_land(v___x_3250_, v___x_3253_);
v___x_3255_ = lean_array_uget_borrowed(v_buckets_3241_, v___x_3254_);
v___x_3256_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3239_, v_fallback_3240_, v___x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3257_, lean_object* v_a_3258_, lean_object* v_fallback_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3257_, v_a_3258_, v_fallback_3259_);
lean_dec(v_fallback_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_m_3257_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3261_, lean_object* v_rest_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3269_ = lean_unsigned_to_nat(0u);
v___x_3270_ = lean_nat_dec_eq(v_next_3261_, v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3261_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3297_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3297_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3297_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_snd_3276_; 
v_snd_3276_ = lean_ctor_get(v_a_3272_, 1);
lean_inc(v_snd_3276_);
lean_dec(v_a_3272_);
if (lean_obj_tag(v_rest_3262_) == 0)
{
lean_object* v_fst_3277_; lean_object* v_snd_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v_fst_3277_ = lean_ctor_get(v_snd_3276_, 0);
lean_inc(v_fst_3277_);
v_snd_3278_ = lean_ctor_get(v_snd_3276_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_snd_3276_);
v___x_3279_ = lean_st_ref_take(v_a_3263_);
v___x_3280_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3281_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v_fst_3277_);
lean_ctor_set(v___x_3281_, 2, v_snd_3278_);
lean_ctor_set(v___x_3281_, 3, v___x_3280_);
v___x_3282_ = lean_array_set(v___x_3279_, v_next_3261_, v___x_3281_);
lean_dec(v_next_3261_);
v___x_3283_ = lean_st_ref_set(v_a_3263_, v___x_3282_);
v___x_3284_ = lean_box(0);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3284_);
v___x_3286_ = v___x_3274_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
else
{
lean_object* v_fst_3288_; lean_object* v_snd_3289_; lean_object* v_head_3290_; lean_object* v_tail_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
lean_del_object(v___x_3274_);
lean_dec(v_next_3261_);
v_fst_3288_ = lean_ctor_get(v_snd_3276_, 0);
lean_inc(v_fst_3288_);
v_snd_3289_ = lean_ctor_get(v_snd_3276_, 1);
lean_inc(v_snd_3289_);
lean_dec(v_snd_3276_);
v_head_3290_ = lean_ctor_get(v_rest_3262_, 0);
v_tail_3291_ = lean_ctor_get(v_rest_3262_, 1);
v___x_3292_ = lean_box(3);
v___x_3293_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3290_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; 
lean_dec(v_fst_3288_);
v___x_3294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3289_, v_head_3290_, v___x_3269_);
lean_dec(v_snd_3289_);
v_next_3261_ = v___x_3294_;
v_rest_3262_ = v_tail_3291_;
goto _start;
}
else
{
lean_dec(v_snd_3289_);
v_next_3261_ = v_fst_3288_;
v_rest_3262_ = v_tail_3291_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec(v_next_3261_);
v_a_3298_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3271_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3271_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec(v_next_3261_);
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3308_, lean_object* v_rest_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3308_, v_rest_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec(v_rest_3309_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3317_, lean_object* v_next_3318_, lean_object* v_rest_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3318_, v_rest_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3327_, lean_object* v_next_3328_, lean_object* v_rest_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3327_, v_next_3328_, v_rest_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec(v_rest_3329_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3337_, lean_object* v_m_3338_, lean_object* v_a_3339_, lean_object* v_fallback_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3338_, v_a_3339_, v_fallback_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3342_, lean_object* v_m_3343_, lean_object* v_a_3344_, lean_object* v_fallback_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3342_, v_m_3343_, v_a_3344_, v_fallback_3345_);
lean_dec(v_fallback_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_m_3343_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3347_, lean_object* v_a_3348_, lean_object* v_fallback_3349_, lean_object* v_x_3350_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3348_, v_fallback_3349_, v_x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3352_, lean_object* v_a_3353_, lean_object* v_fallback_3354_, lean_object* v_x_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3352_, v_a_3353_, v_fallback_3354_, v_x_3355_);
lean_dec(v_x_3355_);
lean_dec(v_fallback_3354_);
lean_dec(v_a_3353_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3357_, lean_object* v_path_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
if (lean_obj_tag(v_path_3358_) == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_t_3357_);
return v___x_3364_;
}
else
{
lean_object* v_head_3365_; lean_object* v_tail_3366_; lean_object* v_roots_3367_; lean_object* v___x_3368_; lean_object* v_idx_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_head_3365_ = lean_ctor_get(v_path_3358_, 0);
lean_inc(v_head_3365_);
v_tail_3366_ = lean_ctor_get(v_path_3358_, 1);
lean_inc(v_tail_3366_);
lean_dec_ref_known(v_path_3358_, 2);
v_roots_3367_ = lean_ctor_get(v_t_3357_, 1);
v___x_3368_ = lean_unsigned_to_nat(0u);
v_idx_3369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3367_, v_head_3365_, v___x_3368_);
lean_dec(v_head_3365_);
v___x_3370_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3370_, 0, lean_box(0));
lean_closure_set(v___x_3370_, 1, v_idx_3369_);
lean_closure_set(v___x_3370_, 2, v_tail_3366_);
v___x_3371_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3357_, v___x_3370_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3380_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3380_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_snd_3376_; lean_object* v___x_3378_; 
v_snd_3376_ = lean_ctor_get(v_a_3372_, 1);
lean_inc(v_snd_3376_);
lean_dec(v_a_3372_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v_snd_3376_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_snd_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v_a_3381_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3371_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3371_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3389_, lean_object* v_path_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3389_, v_path_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3397_, lean_object* v_t_3398_, lean_object* v_path_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3398_, v_path_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3406_, lean_object* v_t_3407_, lean_object* v_path_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3406_, v_t_3407_, v_path_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_a_3410_);
lean_dec_ref(v_a_3409_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3417_, lean_object* v_e_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = lean_array_get_size(v_a_3419_);
v___x_3421_ = lean_nat_dec_lt(v___x_3420_, v_score_3417_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3422_ = lean_unsigned_to_nat(1u);
v___x_3423_ = lean_mk_empty_array_with_capacity(v___x_3422_);
v___x_3424_ = lean_array_push(v___x_3423_, v_e_3418_);
v___x_3425_ = lean_array_push(v_a_3419_, v___x_3424_);
return v___x_3425_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3427_ = lean_array_push(v_a_3419_, v___x_3426_);
v_a_3419_ = v___x_3427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3429_, lean_object* v_e_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3429_, v_e_3430_, v_a_3431_);
lean_dec(v_score_3429_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3433_, lean_object* v_score_3434_, lean_object* v_e_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3434_, v_e_3435_, v_a_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3438_, lean_object* v_score_3439_, lean_object* v_e_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3438_, v_score_3439_, v_e_3440_, v_a_3441_);
lean_dec(v_score_3439_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3443_, lean_object* v_score_3444_, lean_object* v_e_3445_){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3446_ = lean_array_get_size(v_e_3445_);
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = lean_nat_dec_eq(v___x_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = lean_array_get_size(v_r_3443_);
v___x_3450_ = lean_nat_dec_lt(v_score_3444_, v___x_3449_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
v___x_3451_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3444_, v_e_3445_, v_r_3443_);
return v___x_3451_;
}
else
{
if (v___x_3450_ == 0)
{
lean_dec_ref(v_e_3445_);
return v_r_3443_;
}
else
{
lean_object* v_v_3452_; lean_object* v___x_3453_; lean_object* v_xs_x27_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_v_3452_ = lean_array_fget(v_r_3443_, v_score_3444_);
v___x_3453_ = lean_box(0);
v_xs_x27_3454_ = lean_array_fset(v_r_3443_, v_score_3444_, v___x_3453_);
v___x_3455_ = lean_array_push(v_v_3452_, v_e_3445_);
v___x_3456_ = lean_array_fset(v_xs_x27_3454_, v_score_3444_, v___x_3455_);
return v___x_3456_;
}
}
}
else
{
lean_dec_ref(v_e_3445_);
return v_r_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3457_, lean_object* v_score_3458_, lean_object* v_e_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3457_, v_score_3458_, v_e_3459_);
lean_dec(v_score_3458_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3461_, lean_object* v_r_3462_, lean_object* v_score_3463_, lean_object* v_e_3464_){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3462_, v_score_3463_, v_e_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3466_, lean_object* v_r_3467_, lean_object* v_score_3468_, lean_object* v_e_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3466_, v_r_3467_, v_score_3468_, v_e_3469_);
lean_dec(v_score_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3471_, size_t v_i_3472_, size_t v_stop_3473_, lean_object* v_b_3474_){
_start:
{
uint8_t v___x_3475_; 
v___x_3475_ = lean_usize_dec_eq(v_i_3472_, v_stop_3473_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; size_t v___x_3479_; size_t v___x_3480_; 
v___x_3476_ = lean_array_uget_borrowed(v_as_3471_, v_i_3472_);
v___x_3477_ = lean_array_get_size(v___x_3476_);
v___x_3478_ = lean_nat_add(v_b_3474_, v___x_3477_);
lean_dec(v_b_3474_);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3472_, v___x_3479_);
v_i_3472_ = v___x_3480_;
v_b_3474_ = v___x_3478_;
goto _start;
}
else
{
return v_b_3474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3482_, lean_object* v_i_3483_, lean_object* v_stop_3484_, lean_object* v_b_3485_){
_start:
{
size_t v_i_boxed_3486_; size_t v_stop_boxed_3487_; lean_object* v_res_3488_; 
v_i_boxed_3486_ = lean_unbox_usize(v_i_3483_);
lean_dec(v_i_3483_);
v_stop_boxed_3487_ = lean_unbox_usize(v_stop_3484_);
lean_dec(v_stop_3484_);
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3482_, v_i_boxed_3486_, v_stop_boxed_3487_, v_b_3485_);
lean_dec_ref(v_as_3482_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3489_, size_t v_i_3490_, size_t v_stop_3491_, lean_object* v_b_3492_){
_start:
{
lean_object* v___y_3494_; uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_eq(v_i_3490_, v_stop_3491_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3499_ = lean_array_uget_borrowed(v_as_3489_, v_i_3490_);
v___x_3500_ = lean_unsigned_to_nat(0u);
v___x_3501_ = lean_array_get_size(v___x_3499_);
v___x_3502_ = lean_nat_dec_lt(v___x_3500_, v___x_3501_);
if (v___x_3502_ == 0)
{
v___y_3494_ = v_b_3492_;
goto v___jp_3493_;
}
else
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_nat_dec_le(v___x_3501_, v___x_3501_);
if (v___x_3503_ == 0)
{
if (v___x_3502_ == 0)
{
v___y_3494_ = v_b_3492_;
goto v___jp_3493_;
}
else
{
size_t v___x_3504_; size_t v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((size_t)0ULL);
v___x_3505_ = lean_usize_of_nat(v___x_3501_);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3499_, v___x_3504_, v___x_3505_, v_b_3492_);
v___y_3494_ = v___x_3506_;
goto v___jp_3493_;
}
}
else
{
size_t v___x_3507_; size_t v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = ((size_t)0ULL);
v___x_3508_ = lean_usize_of_nat(v___x_3501_);
v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3499_, v___x_3507_, v___x_3508_, v_b_3492_);
v___y_3494_ = v___x_3509_;
goto v___jp_3493_;
}
}
}
else
{
return v_b_3492_;
}
v___jp_3493_:
{
size_t v___x_3495_; size_t v___x_3496_; 
v___x_3495_ = ((size_t)1ULL);
v___x_3496_ = lean_usize_add(v_i_3490_, v___x_3495_);
v_i_3490_ = v___x_3496_;
v_b_3492_ = v___y_3494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3510_, lean_object* v_i_3511_, lean_object* v_stop_3512_, lean_object* v_b_3513_){
_start:
{
size_t v_i_boxed_3514_; size_t v_stop_boxed_3515_; lean_object* v_res_3516_; 
v_i_boxed_3514_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_stop_boxed_3515_ = lean_unbox_usize(v_stop_3512_);
lean_dec(v_stop_3512_);
v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3510_, v_i_boxed_3514_, v_stop_boxed_3515_, v_b_3513_);
lean_dec_ref(v_as_3510_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3517_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_unsigned_to_nat(0u);
v___x_3519_ = lean_array_get_size(v_mr_3517_);
v___x_3520_ = lean_nat_dec_lt(v___x_3518_, v___x_3519_);
if (v___x_3520_ == 0)
{
return v___x_3518_;
}
else
{
uint8_t v___x_3521_; 
v___x_3521_ = lean_nat_dec_le(v___x_3519_, v___x_3519_);
if (v___x_3521_ == 0)
{
if (v___x_3520_ == 0)
{
return v___x_3518_;
}
else
{
size_t v___x_3522_; size_t v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = ((size_t)0ULL);
v___x_3523_ = lean_usize_of_nat(v___x_3519_);
v___x_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3517_, v___x_3522_, v___x_3523_, v___x_3518_);
return v___x_3524_;
}
}
else
{
size_t v___x_3525_; size_t v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = ((size_t)0ULL);
v___x_3526_ = lean_usize_of_nat(v___x_3519_);
v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3517_, v___x_3525_, v___x_3526_, v___x_3518_);
return v___x_3527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3528_);
lean_dec_ref(v_mr_3528_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3530_, lean_object* v_mr_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3533_, lean_object* v_mr_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3533_, v_mr_3534_);
lean_dec_ref(v_mr_3534_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3536_, lean_object* v_as_3537_, size_t v_i_3538_, size_t v_stop_3539_, lean_object* v_b_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3537_, v_i_3538_, v_stop_3539_, v_b_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_as_3543_, lean_object* v_i_3544_, lean_object* v_stop_3545_, lean_object* v_b_3546_){
_start:
{
size_t v_i_boxed_3547_; size_t v_stop_boxed_3548_; lean_object* v_res_3549_; 
v_i_boxed_3547_ = lean_unbox_usize(v_i_3544_);
lean_dec(v_i_3544_);
v_stop_boxed_3548_ = lean_unbox_usize(v_stop_3545_);
lean_dec(v_stop_3545_);
v_res_3549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3542_, v_as_3543_, v_i_boxed_3547_, v_stop_boxed_3548_, v_b_3546_);
lean_dec_ref(v_as_3543_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3550_, lean_object* v_as_3551_, size_t v_i_3552_, size_t v_stop_3553_, lean_object* v_b_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3551_, v_i_3552_, v_stop_3553_, v_b_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3556_, lean_object* v_as_3557_, lean_object* v_i_3558_, lean_object* v_stop_3559_, lean_object* v_b_3560_){
_start:
{
size_t v_i_boxed_3561_; size_t v_stop_boxed_3562_; lean_object* v_res_3563_; 
v_i_boxed_3561_ = lean_unbox_usize(v_i_3558_);
lean_dec(v_i_3558_);
v_stop_boxed_3562_ = lean_unbox_usize(v_stop_3559_);
lean_dec(v_stop_3559_);
v_res_3563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3556_, v_as_3557_, v_i_boxed_3561_, v_stop_boxed_3562_, v_b_3560_);
lean_dec_ref(v_as_3557_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3564_, lean_object* v_j_3565_, lean_object* v_x_3566_){
_start:
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_apply_2(v_f_3564_, v_j_3565_, v_x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3587_, lean_object* v_x1_3588_, lean_object* v_x2_3589_){
_start:
{
lean_object* v___x_3590_; size_t v_sz_3591_; size_t v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3590_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3591_ = lean_array_size(v_x2_3589_);
v___x_3592_ = ((size_t)0ULL);
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3590_, v___f_3587_, v_sz_3591_, v___x_3592_, v_x2_3589_);
v___x_3594_ = l_Array_append___redArg(v_x1_3588_, v___x_3593_);
lean_dec(v___x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3595_, lean_object* v_mr_3596_, lean_object* v_f_3597_, lean_object* v_i_3598_, lean_object* v_x_3599_, lean_object* v_r_3600_){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_j_3603_; lean_object* v_b_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3601_ = lean_unsigned_to_nat(1u);
v___x_3602_ = lean_nat_sub(v_n_3595_, v___x_3601_);
v_j_3603_ = lean_nat_sub(v___x_3602_, v_i_3598_);
lean_dec(v___x_3602_);
v_b_3604_ = lean_array_fget_borrowed(v_mr_3596_, v_j_3603_);
v___x_3605_ = lean_unsigned_to_nat(0u);
v___x_3606_ = lean_array_get_size(v_b_3604_);
v___x_3607_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3608_ = lean_nat_dec_lt(v___x_3605_, v___x_3606_);
if (v___x_3608_ == 0)
{
lean_dec(v_j_3603_);
lean_dec(v_f_3597_);
return v_r_3600_;
}
else
{
lean_object* v___f_3609_; lean_object* v___f_3610_; uint8_t v___x_3611_; 
v___f_3609_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3609_, 0, v_f_3597_);
lean_closure_set(v___f_3609_, 1, v_j_3603_);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3610_, 0, v___f_3609_);
v___x_3611_ = lean_nat_dec_le(v___x_3606_, v___x_3606_);
if (v___x_3611_ == 0)
{
if (v___x_3608_ == 0)
{
lean_dec_ref(v___f_3610_);
return v_r_3600_;
}
else
{
size_t v___x_3612_; size_t v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = lean_usize_of_nat(v___x_3606_);
lean_inc(v_b_3604_);
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3607_, v___f_3610_, v_b_3604_, v___x_3612_, v___x_3613_, v_r_3600_);
return v___x_3614_;
}
}
else
{
size_t v___x_3615_; size_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = ((size_t)0ULL);
v___x_3616_ = lean_usize_of_nat(v___x_3606_);
lean_inc(v_b_3604_);
v___x_3617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3607_, v___f_3610_, v_b_3604_, v___x_3615_, v___x_3616_, v_r_3600_);
return v___x_3617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3618_, lean_object* v_mr_3619_, lean_object* v_f_3620_, lean_object* v_i_3621_, lean_object* v_x_3622_, lean_object* v_r_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3618_, v_mr_3619_, v_f_3620_, v_i_3621_, v_x_3622_, v_r_3623_);
lean_dec(v_i_3621_);
lean_dec_ref(v_mr_3619_);
lean_dec(v_n_3618_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3625_, lean_object* v_a_3626_, lean_object* v_f_3627_){
_start:
{
lean_object* v_n_3628_; lean_object* v___f_3629_; lean_object* v___x_3630_; 
v_n_3628_ = lean_array_get_size(v_mr_3625_);
v___f_3629_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3629_, 0, v_n_3628_);
lean_closure_set(v___f_3629_, 1, v_mr_3625_);
lean_closure_set(v___f_3629_, 2, v_f_3627_);
v___x_3630_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3628_, v___f_3629_, v_n_3628_, lean_box(0), v_a_3626_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3631_, lean_object* v_00_u03b2_3632_, lean_object* v_mr_3633_, lean_object* v_a_3634_, lean_object* v_f_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3633_, v_a_3634_, v_f_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3637_, size_t v_i_3638_, lean_object* v_bs_3639_){
_start:
{
uint8_t v___x_3640_; 
v___x_3640_ = lean_usize_dec_lt(v_i_3638_, v_sz_3637_);
if (v___x_3640_ == 0)
{
return v_bs_3639_;
}
else
{
lean_object* v_v_3641_; lean_object* v___x_3642_; lean_object* v_bs_x27_3643_; size_t v___x_3644_; size_t v___x_3645_; lean_object* v___x_3646_; 
v_v_3641_ = lean_array_uget(v_bs_3639_, v_i_3638_);
v___x_3642_ = lean_unsigned_to_nat(0u);
v_bs_x27_3643_ = lean_array_uset(v_bs_3639_, v_i_3638_, v___x_3642_);
v___x_3644_ = ((size_t)1ULL);
v___x_3645_ = lean_usize_add(v_i_3638_, v___x_3644_);
v___x_3646_ = lean_array_uset(v_bs_x27_3643_, v_i_3638_, v_v_3641_);
v_i_3638_ = v___x_3645_;
v_bs_3639_ = v___x_3646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3648_, lean_object* v_i_3649_, lean_object* v_bs_3650_){
_start:
{
size_t v_sz_boxed_3651_; size_t v_i_boxed_3652_; lean_object* v_res_3653_; 
v_sz_boxed_3651_ = lean_unbox_usize(v_sz_3648_);
lean_dec(v_sz_3648_);
v_i_boxed_3652_ = lean_unbox_usize(v_i_3649_);
lean_dec(v_i_3649_);
v_res_3653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3651_, v_i_boxed_3652_, v_bs_3650_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3654_, size_t v_i_3655_, size_t v_stop_3656_, lean_object* v_b_3657_){
_start:
{
uint8_t v___x_3658_; 
v___x_3658_ = lean_usize_dec_eq(v_i_3655_, v_stop_3656_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; size_t v_sz_3660_; size_t v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; size_t v___x_3664_; size_t v___x_3665_; 
v___x_3659_ = lean_array_uget_borrowed(v_as_3654_, v_i_3655_);
v_sz_3660_ = lean_array_size(v___x_3659_);
v___x_3661_ = ((size_t)0ULL);
lean_inc(v___x_3659_);
v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3660_, v___x_3661_, v___x_3659_);
v___x_3663_ = l_Array_append___redArg(v_b_3657_, v___x_3662_);
lean_dec_ref(v___x_3662_);
v___x_3664_ = ((size_t)1ULL);
v___x_3665_ = lean_usize_add(v_i_3655_, v___x_3664_);
v_i_3655_ = v___x_3665_;
v_b_3657_ = v___x_3663_;
goto _start;
}
else
{
return v_b_3657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3667_, lean_object* v_i_3668_, lean_object* v_stop_3669_, lean_object* v_b_3670_){
_start:
{
size_t v_i_boxed_3671_; size_t v_stop_boxed_3672_; lean_object* v_res_3673_; 
v_i_boxed_3671_ = lean_unbox_usize(v_i_3668_);
lean_dec(v_i_3668_);
v_stop_boxed_3672_ = lean_unbox_usize(v_stop_3669_);
lean_dec(v_stop_3669_);
v_res_3673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3667_, v_i_boxed_3671_, v_stop_boxed_3672_, v_b_3670_);
lean_dec_ref(v_as_3667_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3674_, lean_object* v_aa_3675_, lean_object* v_n_3676_, lean_object* v_j_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v_zero_3679_; uint8_t v_isZero_3680_; 
v_zero_3679_ = lean_unsigned_to_nat(0u);
v_isZero_3680_ = lean_nat_dec_eq(v_j_3677_, v_zero_3679_);
if (v_isZero_3680_ == 1)
{
lean_dec(v_j_3677_);
return v_a_3678_;
}
else
{
lean_object* v_one_3681_; lean_object* v_n_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v_j_3685_; lean_object* v_b_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v_one_3681_ = lean_unsigned_to_nat(1u);
v_n_3682_ = lean_nat_sub(v_j_3677_, v_one_3681_);
v___x_3683_ = lean_nat_sub(v_n_3676_, v_j_3677_);
lean_dec(v_j_3677_);
v___x_3684_ = lean_nat_sub(v_n_3674_, v_one_3681_);
v_j_3685_ = lean_nat_sub(v___x_3684_, v___x_3683_);
lean_dec(v___x_3683_);
lean_dec(v___x_3684_);
v_b_3686_ = lean_array_fget_borrowed(v_aa_3675_, v_j_3685_);
lean_dec(v_j_3685_);
v___x_3687_ = lean_array_get_size(v_b_3686_);
v___x_3688_ = lean_nat_dec_lt(v_zero_3679_, v___x_3687_);
if (v___x_3688_ == 0)
{
v_j_3677_ = v_n_3682_;
goto _start;
}
else
{
uint8_t v___x_3690_; 
v___x_3690_ = lean_nat_dec_le(v___x_3687_, v___x_3687_);
if (v___x_3690_ == 0)
{
if (v___x_3688_ == 0)
{
v_j_3677_ = v_n_3682_;
goto _start;
}
else
{
size_t v___x_3692_; size_t v___x_3693_; lean_object* v___x_3694_; 
v___x_3692_ = ((size_t)0ULL);
v___x_3693_ = lean_usize_of_nat(v___x_3687_);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3686_, v___x_3692_, v___x_3693_, v_a_3678_);
v_j_3677_ = v_n_3682_;
v_a_3678_ = v___x_3694_;
goto _start;
}
}
else
{
size_t v___x_3696_; size_t v___x_3697_; lean_object* v___x_3698_; 
v___x_3696_ = ((size_t)0ULL);
v___x_3697_ = lean_usize_of_nat(v___x_3687_);
v___x_3698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3686_, v___x_3696_, v___x_3697_, v_a_3678_);
v_j_3677_ = v_n_3682_;
v_a_3678_ = v___x_3698_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3700_, lean_object* v_aa_3701_, lean_object* v_n_3702_, lean_object* v_j_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3700_, v_aa_3701_, v_n_3702_, v_j_3703_, v_a_3704_);
lean_dec(v_n_3702_);
lean_dec_ref(v_aa_3701_);
lean_dec(v_n_3700_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_n_3708_; lean_object* v___x_3709_; 
v_n_3708_ = lean_array_get_size(v_mr_3706_);
v___x_3709_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3708_, v_mr_3706_, v_n_3708_, v_n_3708_, v_a_3707_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3710_, v_a_3711_);
lean_dec_ref(v_mr_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3713_, v_a_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3716_, v_a_3717_);
lean_dec_ref(v_mr_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3719_, lean_object* v_mr_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3720_, v_a_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3723_, lean_object* v_mr_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3723_, v_mr_3724_, v_a_3725_);
lean_dec_ref(v_mr_3724_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3727_, lean_object* v_mr_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3728_, v_a_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_mr_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3731_, v_mr_3732_, v_a_3733_);
lean_dec_ref(v_mr_3732_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3735_, size_t v_sz_3736_, size_t v_i_3737_, lean_object* v_bs_3738_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3736_, v_i_3737_, v_bs_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3740_, lean_object* v_sz_3741_, lean_object* v_i_3742_, lean_object* v_bs_3743_){
_start:
{
size_t v_sz_boxed_3744_; size_t v_i_boxed_3745_; lean_object* v_res_3746_; 
v_sz_boxed_3744_ = lean_unbox_usize(v_sz_3741_);
lean_dec(v_sz_3741_);
v_i_boxed_3745_ = lean_unbox_usize(v_i_3742_);
lean_dec(v_i_3742_);
v_res_3746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3740_, v_sz_boxed_3744_, v_i_boxed_3745_, v_bs_3743_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3747_, lean_object* v_as_3748_, size_t v_i_3749_, size_t v_stop_3750_, lean_object* v_b_3751_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3748_, v_i_3749_, v_stop_3750_, v_b_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3753_, lean_object* v_as_3754_, lean_object* v_i_3755_, lean_object* v_stop_3756_, lean_object* v_b_3757_){
_start:
{
size_t v_i_boxed_3758_; size_t v_stop_boxed_3759_; lean_object* v_res_3760_; 
v_i_boxed_3758_ = lean_unbox_usize(v_i_3755_);
lean_dec(v_i_3755_);
v_stop_boxed_3759_ = lean_unbox_usize(v_stop_3756_);
lean_dec(v_stop_3756_);
v_res_3760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3753_, v_as_3754_, v_i_boxed_3758_, v_stop_boxed_3759_, v_b_3757_);
lean_dec_ref(v_as_3754_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3761_, lean_object* v_n_3762_, lean_object* v_aa_3763_, lean_object* v_n_3764_, lean_object* v_j_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3762_, v_aa_3763_, v_n_3764_, v_j_3765_, v_a_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3769_, lean_object* v_n_3770_, lean_object* v_aa_3771_, lean_object* v_n_3772_, lean_object* v_j_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3769_, v_n_3770_, v_aa_3771_, v_n_3772_, v_j_3773_, v_a_3774_, v_a_3775_);
lean_dec(v_n_3772_);
lean_dec_ref(v_aa_3771_);
lean_dec(v_n_3770_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3784_, lean_object* v___x_3785_, lean_object* v_score_3786_, lean_object* v___x_3787_, lean_object* v_k_3788_, lean_object* v_args_3789_, lean_object* v_cases_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3784_, v_k_3788_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_dec_ref(v___x_3785_);
return v_cases_3790_;
}
else
{
lean_object* v_val_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_val_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_val_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l_Array_append___redArg(v___x_3785_, v_args_3789_);
v___x_3794_ = lean_nat_add(v_score_3786_, v___x_3787_);
v___x_3795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
lean_ctor_set(v___x_3795_, 2, v_val_3792_);
v___x_3796_ = lean_array_push(v_cases_3790_, v___x_3795_);
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3797_, lean_object* v___x_3798_, lean_object* v_score_3799_, lean_object* v___x_3800_, lean_object* v_k_3801_, lean_object* v_args_3802_, lean_object* v_cases_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3797_, v___x_3798_, v_score_3799_, v___x_3800_, v_k_3801_, v_args_3802_, v_cases_3803_);
lean_dec_ref(v_args_3802_);
lean_dec(v_k_3801_);
lean_dec(v___x_3800_);
lean_dec(v_score_3799_);
lean_dec_ref(v_snd_3797_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3805_, lean_object* v_result_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v___x_3813_ = lean_array_get_size(v_cases_3805_);
v___x_3814_ = lean_unsigned_to_nat(0u);
v___x_3815_ = lean_nat_dec_eq(v___x_3813_, v___x_3814_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v_ca_3819_; lean_object* v_todo_3820_; lean_object* v_score_3821_; lean_object* v_c_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3888_; 
v___x_3816_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3817_ = lean_unsigned_to_nat(1u);
v___x_3818_ = lean_nat_sub(v___x_3813_, v___x_3817_);
v_ca_3819_ = lean_array_get(v___x_3816_, v_cases_3805_, v___x_3818_);
lean_dec(v___x_3818_);
v_todo_3820_ = lean_ctor_get(v_ca_3819_, 0);
v_score_3821_ = lean_ctor_get(v_ca_3819_, 1);
v_c_3822_ = lean_ctor_get(v_ca_3819_, 2);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_ca_3819_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3824_ = v_ca_3819_;
v_isShared_3825_ = v_isSharedCheck_3888_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_c_3822_);
lean_inc(v_score_3821_);
lean_inc(v_todo_3820_);
lean_dec(v_ca_3819_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3888_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3822_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec(v_c_3822_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___y_3829_; uint8_t v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v_snd_3855_; lean_object* v_fst_3856_; lean_object* v_fst_3857_; lean_object* v_snd_3858_; lean_object* v_cases_3859_; lean_object* v___x_3860_; uint8_t v___y_3862_; uint8_t v___x_3874_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v_snd_3855_ = lean_ctor_get(v_a_3827_, 1);
lean_inc(v_snd_3855_);
v_fst_3856_ = lean_ctor_get(v_a_3827_, 0);
lean_inc(v_fst_3856_);
lean_dec(v_a_3827_);
v_fst_3857_ = lean_ctor_get(v_snd_3855_, 0);
lean_inc(v_fst_3857_);
v_snd_3858_ = lean_ctor_get(v_snd_3855_, 1);
lean_inc(v_snd_3858_);
lean_dec(v_snd_3855_);
v_cases_3859_ = lean_array_pop(v_cases_3805_);
v___x_3860_ = lean_array_get_size(v_todo_3820_);
v___x_3874_ = lean_nat_dec_eq(v___x_3860_, v___x_3814_);
if (v___x_3874_ == 0)
{
uint8_t v___x_3875_; 
lean_dec(v_fst_3856_);
v___x_3875_ = lean_nat_dec_eq(v_fst_3857_, v___x_3814_);
if (v___x_3875_ == 0)
{
v___y_3862_ = v___x_3875_;
goto v___jp_3861_;
}
else
{
lean_object* v_size_3876_; uint8_t v___x_3877_; 
v_size_3876_ = lean_ctor_get(v_snd_3858_, 0);
v___x_3877_ = lean_nat_dec_eq(v_size_3876_, v___x_3814_);
v___y_3862_ = v___x_3877_;
goto v___jp_3861_;
}
}
else
{
lean_object* v___x_3878_; 
lean_dec(v_snd_3858_);
lean_dec(v_fst_3857_);
lean_del_object(v___x_3824_);
lean_dec_ref(v_todo_3820_);
v___x_3878_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3806_, v_score_3821_, v_fst_3856_);
lean_dec(v_score_3821_);
v_cases_3805_ = v_cases_3859_;
v_result_3806_ = v___x_3878_;
goto _start;
}
v___jp_3828_:
{
uint8_t v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = 1;
v___x_3834_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3829_, v___x_3833_, v___y_3830_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v_fst_3836_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
v_fst_3836_ = lean_ctor_get(v_a_3835_, 0);
lean_inc(v_fst_3836_);
switch(lean_obj_tag(v_fst_3836_))
{
case 3:
{
lean_dec(v_a_3835_);
lean_dec_ref(v___y_3831_);
v_cases_3805_ = v___y_3832_;
goto _start;
}
case 5:
{
lean_object* v_snd_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_snd_3838_ = lean_ctor_get(v_a_3835_, 1);
lean_inc(v_snd_3838_);
lean_dec(v_a_3835_);
v___x_3839_ = lean_box(4);
v___x_3840_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3831_);
v___x_3841_ = lean_apply_3(v___y_3831_, v___x_3839_, v___x_3840_, v___y_3832_);
v___x_3842_ = lean_apply_3(v___y_3831_, v_fst_3836_, v_snd_3838_, v___x_3841_);
v_cases_3805_ = v___x_3842_;
goto _start;
}
default: 
{
lean_object* v_snd_3844_; lean_object* v___x_3845_; 
v_snd_3844_ = lean_ctor_get(v_a_3835_, 1);
lean_inc(v_snd_3844_);
lean_dec(v_a_3835_);
v___x_3845_ = lean_apply_3(v___y_3831_, v_fst_3836_, v_snd_3844_, v___y_3832_);
v_cases_3805_ = v___x_3845_;
goto _start;
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec_ref(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec_ref(v_result_3806_);
v_a_3847_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3834_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3834_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
v___jp_3861_:
{
if (v___y_3862_ == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___f_3867_; uint8_t v___x_3868_; 
v___x_3863_ = l_Lean_instInhabitedExpr;
v___x_3864_ = lean_nat_sub(v___x_3860_, v___x_3817_);
v___x_3865_ = lean_array_get(v___x_3863_, v_todo_3820_, v___x_3864_);
lean_dec(v___x_3864_);
v___x_3866_ = lean_array_pop(v_todo_3820_);
lean_inc(v_score_3821_);
lean_inc_ref(v___x_3866_);
v___f_3867_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3867_, 0, v_snd_3858_);
lean_closure_set(v___f_3867_, 1, v___x_3866_);
lean_closure_set(v___f_3867_, 2, v_score_3821_);
lean_closure_set(v___f_3867_, 3, v___x_3817_);
v___x_3868_ = lean_nat_dec_eq(v_fst_3857_, v___x_3814_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3870_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 2, v_fst_3857_);
lean_ctor_set(v___x_3824_, 0, v___x_3866_);
v___x_3870_ = v___x_3824_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_score_3821_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_fst_3857_);
v___x_3870_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_array_push(v_cases_3859_, v___x_3870_);
v___y_3829_ = v___x_3865_;
v___y_3830_ = v___y_3862_;
v___y_3831_ = v___f_3867_;
v___y_3832_ = v___x_3871_;
goto v___jp_3828_;
}
}
else
{
lean_dec_ref(v___x_3866_);
lean_dec(v_fst_3857_);
lean_del_object(v___x_3824_);
lean_dec(v_score_3821_);
v___y_3829_ = v___x_3865_;
v___y_3830_ = v___y_3862_;
v___y_3831_ = v___f_3867_;
v___y_3832_ = v_cases_3859_;
goto v___jp_3828_;
}
}
else
{
lean_dec(v_snd_3858_);
lean_dec(v_fst_3857_);
lean_del_object(v___x_3824_);
lean_dec(v_score_3821_);
lean_dec_ref(v_todo_3820_);
v_cases_3805_ = v_cases_3859_;
goto _start;
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_del_object(v___x_3824_);
lean_dec(v_score_3821_);
lean_dec_ref(v_todo_3820_);
lean_dec_ref(v_result_3806_);
lean_dec_ref(v_cases_3805_);
v_a_3880_ = lean_ctor_get(v___x_3826_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3826_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3826_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
else
{
lean_object* v___x_3889_; 
lean_dec_ref(v_cases_3805_);
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v_result_3806_);
return v___x_3889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3890_, lean_object* v_result_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3890_, v_result_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3899_, lean_object* v_cases_3900_, lean_object* v_result_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3900_, v_result_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3909_, lean_object* v_cases_3910_, lean_object* v_result_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3909_, v_cases_3910_, v_result_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = lean_box(3);
v___x_3929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3921_, v___x_3928_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
return v___x_3931_;
}
else
{
lean_object* v_val_3932_; lean_object* v___x_3933_; 
v_val_3932_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_val_3932_);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3933_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3932_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec(v_val_3932_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3945_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3936_ = v___x_3933_;
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v_fst_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3943_; 
v_fst_3938_ = lean_ctor_get(v_a_3934_, 0);
lean_inc(v_fst_3938_);
lean_dec(v_a_3934_);
v___x_3939_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3939_, v___x_3940_, v_fst_3938_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v___x_3941_);
v___x_3943_ = v___x_3936_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
v_a_3946_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3933_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3933_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_root_3954_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3962_, lean_object* v_root_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3971_, lean_object* v_root_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3971_, v_root_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec_ref(v_root_3972_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3980_, lean_object* v_k_3981_, lean_object* v_args_3982_, lean_object* v_cases_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3980_, v_k_3981_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_dec_ref(v_args_3982_);
return v_cases_3983_;
}
else
{
lean_object* v_val_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_val_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_val_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = lean_unsigned_to_nat(1u);
v___x_3987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3987_, 0, v_args_3982_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
lean_ctor_set(v___x_3987_, 2, v_val_3985_);
v___x_3988_ = lean_array_push(v_cases_3983_, v___x_3987_);
return v___x_3988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3989_, lean_object* v_k_3990_, lean_object* v_args_3991_, lean_object* v_cases_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3989_, v_k_3990_, v_args_3991_, v_cases_3992_);
lean_dec(v_k_3990_);
lean_dec_ref(v_r_3989_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3996_, lean_object* v_e_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3996_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___x_4006_ = 1;
v___x_4007_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3997_, v___x_4006_, v___x_4006_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v_fst_4009_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v___x_4007_, 1);
v_fst_4009_ = lean_ctor_get(v_a_4008_, 0);
lean_inc(v_fst_4009_);
switch(lean_obj_tag(v_fst_4009_))
{
case 3:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec(v_a_4008_);
v___x_4010_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4011_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4010_, v_a_4005_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
return v___x_4011_;
}
case 5:
{
lean_object* v_snd_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v_snd_4012_ = lean_ctor_get(v_a_4008_, 1);
lean_inc(v_snd_4012_);
lean_dec(v_a_4008_);
v___x_4013_ = lean_box(4);
v___x_4014_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_4015_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3996_, v___x_4013_, v___x_4014_, v___x_4014_);
v___x_4016_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3996_, v_fst_4009_, v_snd_4012_, v___x_4015_);
v___x_4017_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4016_, v_a_4005_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
return v___x_4017_;
}
default: 
{
lean_object* v_snd_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_snd_4018_ = lean_ctor_get(v_a_4008_, 1);
lean_inc(v_snd_4018_);
lean_dec(v_a_4008_);
v___x_4019_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_4020_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3996_, v_fst_4009_, v_snd_4018_, v___x_4019_);
lean_dec(v_fst_4009_);
v___x_4021_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_4020_, v_a_4005_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
return v___x_4021_;
}
}
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v_a_4005_);
v_a_4022_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4007_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4007_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
else
{
lean_dec_ref(v_e_3997_);
return v___x_4004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_4030_, lean_object* v_e_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4030_, v_e_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_root_4030_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4039_, lean_object* v_root_4040_, lean_object* v_e_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4040_, v_e_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4049_, lean_object* v_root_4050_, lean_object* v_e_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4049_, v_root_4050_, v_e_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_root_4050_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4059_, lean_object* v_e_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_){
_start:
{
lean_object* v_roots_4066_; lean_object* v___x_4067_; uint8_t v_foApprox_4068_; uint8_t v_ctxApprox_4069_; uint8_t v_quasiPatternApprox_4070_; uint8_t v_constApprox_4071_; uint8_t v_isDefEqStuckEx_4072_; uint8_t v_unificationHints_4073_; uint8_t v_proofIrrelevance_4074_; uint8_t v_assignSyntheticOpaque_4075_; uint8_t v_offsetCnstrs_4076_; uint8_t v_etaStruct_4077_; uint8_t v_univApprox_4078_; uint8_t v_iota_4079_; uint8_t v_beta_4080_; uint8_t v_proj_4081_; uint8_t v_zeta_4082_; uint8_t v_zetaDelta_4083_; uint8_t v_zetaUnused_4084_; uint8_t v_zetaHave_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4113_; 
v_roots_4066_ = lean_ctor_get(v_d_4059_, 1);
v___x_4067_ = l_Lean_Meta_Context_config(v_a_4061_);
v_foApprox_4068_ = lean_ctor_get_uint8(v___x_4067_, 0);
v_ctxApprox_4069_ = lean_ctor_get_uint8(v___x_4067_, 1);
v_quasiPatternApprox_4070_ = lean_ctor_get_uint8(v___x_4067_, 2);
v_constApprox_4071_ = lean_ctor_get_uint8(v___x_4067_, 3);
v_isDefEqStuckEx_4072_ = lean_ctor_get_uint8(v___x_4067_, 4);
v_unificationHints_4073_ = lean_ctor_get_uint8(v___x_4067_, 5);
v_proofIrrelevance_4074_ = lean_ctor_get_uint8(v___x_4067_, 6);
v_assignSyntheticOpaque_4075_ = lean_ctor_get_uint8(v___x_4067_, 7);
v_offsetCnstrs_4076_ = lean_ctor_get_uint8(v___x_4067_, 8);
v_etaStruct_4077_ = lean_ctor_get_uint8(v___x_4067_, 10);
v_univApprox_4078_ = lean_ctor_get_uint8(v___x_4067_, 11);
v_iota_4079_ = lean_ctor_get_uint8(v___x_4067_, 12);
v_beta_4080_ = lean_ctor_get_uint8(v___x_4067_, 13);
v_proj_4081_ = lean_ctor_get_uint8(v___x_4067_, 14);
v_zeta_4082_ = lean_ctor_get_uint8(v___x_4067_, 15);
v_zetaDelta_4083_ = lean_ctor_get_uint8(v___x_4067_, 16);
v_zetaUnused_4084_ = lean_ctor_get_uint8(v___x_4067_, 17);
v_zetaHave_4085_ = lean_ctor_get_uint8(v___x_4067_, 18);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4087_ = v___x_4067_;
v_isShared_4088_ = v_isSharedCheck_4113_;
goto v_resetjp_4086_;
}
else
{
lean_dec(v___x_4067_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4113_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
uint8_t v_trackZetaDelta_4089_; lean_object* v_zetaDeltaSet_4090_; lean_object* v_lctx_4091_; lean_object* v_localInstances_4092_; lean_object* v_defEqCtx_x3f_4093_; lean_object* v_synthPendingDepth_4094_; lean_object* v_canUnfold_x3f_4095_; uint8_t v_univApprox_4096_; uint8_t v_inTypeClassResolution_4097_; uint8_t v_cacheInferType_4098_; uint8_t v___x_4099_; lean_object* v_config_4101_; 
v_trackZetaDelta_4089_ = lean_ctor_get_uint8(v_a_4061_, sizeof(void*)*7);
v_zetaDeltaSet_4090_ = lean_ctor_get(v_a_4061_, 1);
v_lctx_4091_ = lean_ctor_get(v_a_4061_, 2);
v_localInstances_4092_ = lean_ctor_get(v_a_4061_, 3);
v_defEqCtx_x3f_4093_ = lean_ctor_get(v_a_4061_, 4);
v_synthPendingDepth_4094_ = lean_ctor_get(v_a_4061_, 5);
v_canUnfold_x3f_4095_ = lean_ctor_get(v_a_4061_, 6);
v_univApprox_4096_ = lean_ctor_get_uint8(v_a_4061_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4097_ = lean_ctor_get_uint8(v_a_4061_, sizeof(void*)*7 + 2);
v_cacheInferType_4098_ = lean_ctor_get_uint8(v_a_4061_, sizeof(void*)*7 + 3);
v___x_4099_ = 2;
if (v_isShared_4088_ == 0)
{
v_config_4101_ = v___x_4087_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 0, v_foApprox_4068_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 1, v_ctxApprox_4069_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 2, v_quasiPatternApprox_4070_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 3, v_constApprox_4071_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 4, v_isDefEqStuckEx_4072_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 5, v_unificationHints_4073_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 6, v_proofIrrelevance_4074_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 7, v_assignSyntheticOpaque_4075_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 8, v_offsetCnstrs_4076_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 10, v_etaStruct_4077_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 11, v_univApprox_4078_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 12, v_iota_4079_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 13, v_beta_4080_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 14, v_proj_4081_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 15, v_zeta_4082_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 16, v_zetaDelta_4083_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 17, v_zetaUnused_4084_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, 18, v_zetaHave_4085_);
v_config_4101_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
uint64_t v___x_4102_; uint64_t v___x_4103_; uint64_t v___x_4104_; lean_object* v___x_4105_; uint64_t v___x_4106_; uint64_t v___x_4107_; uint64_t v_key_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_ctor_set_uint8(v_config_4101_, 9, v___x_4099_);
v___x_4102_ = l_Lean_Meta_Context_configKey(v_a_4061_);
v___x_4103_ = 3ULL;
v___x_4104_ = lean_uint64_shift_right(v___x_4102_, v___x_4103_);
lean_inc_ref(v_roots_4066_);
v___x_4105_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4105_, 0, lean_box(0));
lean_closure_set(v___x_4105_, 1, v_roots_4066_);
lean_closure_set(v___x_4105_, 2, v_e_4060_);
v___x_4106_ = lean_uint64_shift_left(v___x_4104_, v___x_4103_);
v___x_4107_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_4108_ = lean_uint64_lor(v___x_4106_, v___x_4107_);
v___x_4109_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4109_, 0, v_config_4101_);
lean_ctor_set_uint64(v___x_4109_, sizeof(void*)*1, v_key_4108_);
lean_inc(v_canUnfold_x3f_4095_);
lean_inc(v_synthPendingDepth_4094_);
lean_inc(v_defEqCtx_x3f_4093_);
lean_inc_ref(v_localInstances_4092_);
lean_inc_ref(v_lctx_4091_);
lean_inc(v_zetaDeltaSet_4090_);
v___x_4110_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
lean_ctor_set(v___x_4110_, 1, v_zetaDeltaSet_4090_);
lean_ctor_set(v___x_4110_, 2, v_lctx_4091_);
lean_ctor_set(v___x_4110_, 3, v_localInstances_4092_);
lean_ctor_set(v___x_4110_, 4, v_defEqCtx_x3f_4093_);
lean_ctor_set(v___x_4110_, 5, v_synthPendingDepth_4094_);
lean_ctor_set(v___x_4110_, 6, v_canUnfold_x3f_4095_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*7, v_trackZetaDelta_4089_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*7 + 1, v_univApprox_4096_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4097_);
lean_ctor_set_uint8(v___x_4110_, sizeof(void*)*7 + 3, v_cacheInferType_4098_);
v___x_4111_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4059_, v___x_4105_, v___x_4110_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec_ref_known(v___x_4110_, 7);
return v___x_4111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4114_, lean_object* v_e_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4114_, v_e_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4122_, lean_object* v_d_4123_, lean_object* v_e_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v___x_4130_; 
v___x_4130_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4123_, v_e_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4131_, lean_object* v_d_4132_, lean_object* v_e_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4131_, v_d_4132_, v_e_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
lean_dec(v_a_4137_);
lean_dec_ref(v_a_4136_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
return v_res_4139_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4143_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
lean_ctor_set(v___x_4144_, 1, v___x_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4145_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4146_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4148_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4150_, lean_object* v_k_4151_, lean_object* v_f_4152_){
_start:
{
lean_object* v_roots_4153_; lean_object* v_tries_4154_; lean_object* v___x_4155_; 
v_roots_4153_ = lean_ctor_get(v_d_4150_, 0);
v_tries_4154_ = lean_ctor_get(v_d_4150_, 1);
v___x_4155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4153_, v_k_4151_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4167_; 
lean_inc_ref(v_tries_4154_);
lean_inc_ref(v_roots_4153_);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_d_4150_);
if (v_isSharedCheck_4167_ == 0)
{
lean_object* v_unused_4168_; lean_object* v_unused_4169_; 
v_unused_4168_ = lean_ctor_get(v_d_4150_, 1);
lean_dec(v_unused_4168_);
v_unused_4169_ = lean_ctor_get(v_d_4150_, 0);
lean_dec(v_unused_4169_);
v___x_4157_ = v_d_4150_;
v_isShared_4158_ = v_isSharedCheck_4167_;
goto v_resetjp_4156_;
}
else
{
lean_dec(v_d_4150_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4167_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v_roots_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4159_ = lean_array_get_size(v_tries_4154_);
v_roots_4160_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4153_, v_k_4151_, v___x_4159_);
v___x_4161_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_4162_ = lean_apply_1(v_f_4152_, v___x_4161_);
v___x_4163_ = lean_array_push(v_tries_4154_, v___x_4162_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v___x_4163_);
lean_ctor_set(v___x_4157_, 0, v_roots_4160_);
v___x_4165_ = v___x_4157_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_roots_4160_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
else
{
lean_object* v_val_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
lean_dec(v_k_4151_);
v_val_4170_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_val_4170_);
lean_dec_ref_known(v___x_4155_, 1);
v___x_4171_ = lean_array_get_size(v_tries_4154_);
v___x_4172_ = lean_nat_dec_lt(v_val_4170_, v___x_4171_);
if (v___x_4172_ == 0)
{
lean_dec(v_val_4170_);
lean_dec_ref(v_f_4152_);
return v_d_4150_;
}
else
{
lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4184_; 
lean_inc_ref(v_tries_4154_);
lean_inc_ref(v_roots_4153_);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_d_4150_);
if (v_isSharedCheck_4184_ == 0)
{
lean_object* v_unused_4185_; lean_object* v_unused_4186_; 
v_unused_4185_ = lean_ctor_get(v_d_4150_, 1);
lean_dec(v_unused_4185_);
v_unused_4186_ = lean_ctor_get(v_d_4150_, 0);
lean_dec(v_unused_4186_);
v___x_4174_ = v_d_4150_;
v_isShared_4175_ = v_isSharedCheck_4184_;
goto v_resetjp_4173_;
}
else
{
lean_dec(v_d_4150_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4184_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v_v_4176_; lean_object* v___x_4177_; lean_object* v_xs_x27_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4182_; 
v_v_4176_ = lean_array_fget(v_tries_4154_, v_val_4170_);
v___x_4177_ = lean_box(0);
v_xs_x27_4178_ = lean_array_fset(v_tries_4154_, v_val_4170_, v___x_4177_);
v___x_4179_ = lean_apply_1(v_f_4152_, v_v_4176_);
v___x_4180_ = lean_array_fset(v_xs_x27_4178_, v_val_4170_, v___x_4179_);
lean_dec(v_val_4170_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 1, v___x_4180_);
v___x_4182_ = v___x_4174_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_roots_4153_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4187_, lean_object* v_d_4188_, lean_object* v_k_4189_, lean_object* v_f_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4188_, v_k_4189_, v_f_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4192_, lean_object* v_x_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = lean_array_push(v_x_4193_, v_e_4192_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4195_, lean_object* v_k_4196_, lean_object* v_e_4197_){
_start:
{
lean_object* v___f_4198_; lean_object* v___x_4199_; 
v___f_4198_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4198_, 0, v_e_4197_);
v___x_4199_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4195_, v_k_4196_, v___f_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4200_, lean_object* v_d_4201_, lean_object* v_k_4202_, lean_object* v_e_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4201_, v_k_4202_, v_e_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4205_, size_t v_i_4206_, lean_object* v_bs_4207_){
_start:
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_usize_dec_lt(v_i_4206_, v_sz_4205_);
if (v___x_4208_ == 0)
{
return v_bs_4207_;
}
else
{
lean_object* v_v_4209_; lean_object* v___x_4210_; lean_object* v_bs_x27_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; size_t v___x_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
v_v_4209_ = lean_array_uget(v_bs_4207_, v_i_4206_);
v___x_4210_ = lean_unsigned_to_nat(0u);
v_bs_x27_4211_ = lean_array_uset(v_bs_4207_, v_i_4206_, v___x_4210_);
v___x_4212_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4213_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4212_);
lean_ctor_set(v___x_4214_, 1, v___x_4210_);
lean_ctor_set(v___x_4214_, 2, v___x_4213_);
lean_ctor_set(v___x_4214_, 3, v_v_4209_);
v___x_4215_ = ((size_t)1ULL);
v___x_4216_ = lean_usize_add(v_i_4206_, v___x_4215_);
v___x_4217_ = lean_array_uset(v_bs_x27_4211_, v_i_4206_, v___x_4214_);
v_i_4206_ = v___x_4216_;
v_bs_4207_ = v___x_4217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4219_, lean_object* v_i_4220_, lean_object* v_bs_4221_){
_start:
{
size_t v_sz_boxed_4222_; size_t v_i_boxed_4223_; lean_object* v_res_4224_; 
v_sz_boxed_4222_ = lean_unbox_usize(v_sz_4219_);
lean_dec(v_sz_4219_);
v_i_boxed_4223_ = lean_unbox_usize(v_i_4220_);
lean_dec(v_i_4220_);
v_res_4224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4222_, v_i_boxed_4223_, v_bs_4221_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4225_, lean_object* v_x_4226_){
_start:
{
if (lean_obj_tag(v_x_4226_) == 0)
{
return v_x_4225_;
}
else
{
lean_object* v_key_4227_; lean_object* v_value_4228_; lean_object* v_tail_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v_key_4227_ = lean_ctor_get(v_x_4226_, 0);
lean_inc(v_key_4227_);
v_value_4228_ = lean_ctor_get(v_x_4226_, 1);
lean_inc(v_value_4228_);
v_tail_4229_ = lean_ctor_get(v_x_4226_, 2);
lean_inc(v_tail_4229_);
lean_dec_ref_known(v_x_4226_, 3);
v___x_4230_ = lean_unsigned_to_nat(1u);
v___x_4231_ = lean_nat_add(v_value_4228_, v___x_4230_);
lean_dec(v_value_4228_);
v___x_4232_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4225_, v_key_4227_, v___x_4231_);
v_x_4225_ = v___x_4232_;
v_x_4226_ = v_tail_4229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4234_, size_t v_i_4235_, size_t v_stop_4236_, lean_object* v_b_4237_){
_start:
{
uint8_t v___x_4238_; 
v___x_4238_ = lean_usize_dec_eq(v_i_4235_, v_stop_4236_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4240_; size_t v___x_4241_; size_t v___x_4242_; 
v___x_4239_ = lean_array_uget_borrowed(v_as_4234_, v_i_4235_);
lean_inc(v___x_4239_);
v___x_4240_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4237_, v___x_4239_);
v___x_4241_ = ((size_t)1ULL);
v___x_4242_ = lean_usize_add(v_i_4235_, v___x_4241_);
v_i_4235_ = v___x_4242_;
v_b_4237_ = v___x_4240_;
goto _start;
}
else
{
return v_b_4237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4244_, lean_object* v_i_4245_, lean_object* v_stop_4246_, lean_object* v_b_4247_){
_start:
{
size_t v_i_boxed_4248_; size_t v_stop_boxed_4249_; lean_object* v_res_4250_; 
v_i_boxed_4248_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_stop_boxed_4249_ = lean_unbox_usize(v_stop_4246_);
lean_dec(v_stop_4246_);
v_res_4250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4244_, v_i_boxed_4248_, v_stop_boxed_4249_, v_b_4247_);
lean_dec_ref(v_as_4244_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4251_){
_start:
{
lean_object* v_roots_4252_; lean_object* v_tries_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4280_; 
v_roots_4252_ = lean_ctor_get(v_d_4251_, 0);
v_tries_4253_ = lean_ctor_get(v_d_4251_, 1);
v_isSharedCheck_4280_ = !lean_is_exclusive(v_d_4251_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4255_ = v_d_4251_;
v_isShared_4256_ = v_isSharedCheck_4280_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_tries_4253_);
lean_inc(v_roots_4252_);
lean_dec(v_d_4251_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4280_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___y_4258_; lean_object* v_buckets_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; uint8_t v___x_4272_; 
v_buckets_4269_ = lean_ctor_get(v_roots_4252_, 1);
v___x_4270_ = lean_unsigned_to_nat(0u);
v___x_4271_ = lean_array_get_size(v_buckets_4269_);
v___x_4272_ = lean_nat_dec_lt(v___x_4270_, v___x_4271_);
if (v___x_4272_ == 0)
{
v___y_4258_ = v_roots_4252_;
goto v___jp_4257_;
}
else
{
uint8_t v___x_4273_; 
v___x_4273_ = lean_nat_dec_le(v___x_4271_, v___x_4271_);
if (v___x_4273_ == 0)
{
if (v___x_4272_ == 0)
{
v___y_4258_ = v_roots_4252_;
goto v___jp_4257_;
}
else
{
size_t v___x_4274_; size_t v___x_4275_; lean_object* v___x_4276_; 
lean_inc_ref(v_buckets_4269_);
v___x_4274_ = ((size_t)0ULL);
v___x_4275_ = lean_usize_of_nat(v___x_4271_);
v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4269_, v___x_4274_, v___x_4275_, v_roots_4252_);
lean_dec_ref(v_buckets_4269_);
v___y_4258_ = v___x_4276_;
goto v___jp_4257_;
}
}
else
{
size_t v___x_4277_; size_t v___x_4278_; lean_object* v___x_4279_; 
lean_inc_ref(v_buckets_4269_);
v___x_4277_ = ((size_t)0ULL);
v___x_4278_ = lean_usize_of_nat(v___x_4271_);
v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4269_, v___x_4277_, v___x_4278_, v_roots_4252_);
lean_dec_ref(v_buckets_4269_);
v___y_4258_ = v___x_4279_;
goto v___jp_4257_;
}
}
v___jp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; size_t v_sz_4262_; size_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4267_; 
v___x_4259_ = lean_unsigned_to_nat(1u);
v___x_4260_ = lean_mk_empty_array_with_capacity(v___x_4259_);
lean_dec_ref(v___x_4260_);
v___x_4261_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4262_ = lean_array_size(v_tries_4253_);
v___x_4263_ = ((size_t)0ULL);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4262_, v___x_4263_, v_tries_4253_);
v___x_4265_ = l_Array_append___redArg(v___x_4261_, v___x_4264_);
lean_dec_ref(v___x_4264_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 1, v___y_4258_);
lean_ctor_set(v___x_4255_, 0, v___x_4265_);
v___x_4267_ = v___x_4255_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
lean_ctor_set(v_reuseFailAlloc_4268_, 1, v___y_4258_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4281_, lean_object* v_d_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4284_, size_t v_sz_4285_, size_t v_i_4286_, lean_object* v_bs_4287_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4285_, v_i_4286_, v_bs_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4289_, lean_object* v_sz_4290_, lean_object* v_i_4291_, lean_object* v_bs_4292_){
_start:
{
size_t v_sz_boxed_4293_; size_t v_i_boxed_4294_; lean_object* v_res_4295_; 
v_sz_boxed_4293_ = lean_unbox_usize(v_sz_4290_);
lean_dec(v_sz_4290_);
v_i_boxed_4294_ = lean_unbox_usize(v_i_4291_);
lean_dec(v_i_4291_);
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4289_, v_sz_boxed_4293_, v_i_boxed_4294_, v_bs_4292_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4296_, lean_object* v_x_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Array_append___redArg(v_x_4297_, v_y_4296_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4299_, lean_object* v_x_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4299_, v_x_4300_);
lean_dec_ref(v_y_4299_);
return v_res_4301_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Array_instInhabited(lean_box(0));
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4303_, lean_object* v_snd_4304_, lean_object* v_x_4305_, lean_object* v_x_4306_){
_start:
{
if (lean_obj_tag(v_x_4306_) == 0)
{
lean_dec_ref(v_snd_4304_);
return v_x_4305_;
}
else
{
lean_object* v_key_4307_; lean_object* v_value_4308_; lean_object* v_tail_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_key_4307_ = lean_ctor_get(v_x_4306_, 0);
lean_inc(v_key_4307_);
v_value_4308_ = lean_ctor_get(v_x_4306_, 1);
lean_inc(v_value_4308_);
v_tail_4309_ = lean_ctor_get(v_x_4306_, 2);
lean_inc(v_tail_4309_);
lean_dec_ref_known(v_x_4306_, 3);
v___x_4310_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4311_ = lean_array_get_borrowed(v___x_4310_, v_tries_4303_, v_value_4308_);
lean_dec(v_value_4308_);
lean_inc_ref(v_snd_4304_);
lean_inc(v___x_4311_);
v___x_4312_ = lean_apply_1(v_snd_4304_, v___x_4311_);
v___x_4313_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4305_, v_key_4307_, v___x_4312_);
v_x_4305_ = v___x_4313_;
v_x_4306_ = v_tail_4309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4315_, lean_object* v_snd_4316_, lean_object* v_x_4317_, lean_object* v_x_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4315_, v_snd_4316_, v_x_4317_, v_x_4318_);
lean_dec_ref(v_tries_4315_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4320_, lean_object* v_snd_4321_, lean_object* v_as_4322_, size_t v_i_4323_, size_t v_stop_4324_, lean_object* v_b_4325_){
_start:
{
uint8_t v___x_4326_; 
v___x_4326_ = lean_usize_dec_eq(v_i_4323_, v_stop_4324_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; lean_object* v___x_4328_; size_t v___x_4329_; size_t v___x_4330_; 
v___x_4327_ = lean_array_uget_borrowed(v_as_4322_, v_i_4323_);
lean_inc(v___x_4327_);
lean_inc_ref(v_snd_4321_);
v___x_4328_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4320_, v_snd_4321_, v_b_4325_, v___x_4327_);
v___x_4329_ = ((size_t)1ULL);
v___x_4330_ = lean_usize_add(v_i_4323_, v___x_4329_);
v_i_4323_ = v___x_4330_;
v_b_4325_ = v___x_4328_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4321_);
return v_b_4325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4332_, lean_object* v_snd_4333_, lean_object* v_as_4334_, lean_object* v_i_4335_, lean_object* v_stop_4336_, lean_object* v_b_4337_){
_start:
{
size_t v_i_boxed_4338_; size_t v_stop_boxed_4339_; lean_object* v_res_4340_; 
v_i_boxed_4338_ = lean_unbox_usize(v_i_4335_);
lean_dec(v_i_4335_);
v_stop_boxed_4339_ = lean_unbox_usize(v_stop_4336_);
lean_dec(v_stop_4336_);
v_res_4340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4332_, v_snd_4333_, v_as_4334_, v_i_boxed_4338_, v_stop_boxed_4339_, v_b_4337_);
lean_dec_ref(v_as_4334_);
lean_dec_ref(v_tries_4332_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4343_, lean_object* v_y_4344_){
_start:
{
lean_object* v_fst_4346_; lean_object* v_buckets_4347_; lean_object* v_tries_4348_; lean_object* v_snd_4349_; lean_object* v_roots_4360_; lean_object* v_roots_4361_; lean_object* v_tries_4362_; lean_object* v_size_4363_; lean_object* v_buckets_4364_; lean_object* v_tries_4365_; lean_object* v_size_4366_; lean_object* v_buckets_4367_; uint8_t v___x_4368_; 
v_roots_4360_ = lean_ctor_get(v_y_4344_, 0);
v_roots_4361_ = lean_ctor_get(v_x_4343_, 0);
v_tries_4362_ = lean_ctor_get(v_y_4344_, 1);
v_size_4363_ = lean_ctor_get(v_roots_4360_, 0);
v_buckets_4364_ = lean_ctor_get(v_roots_4360_, 1);
v_tries_4365_ = lean_ctor_get(v_x_4343_, 1);
v_size_4366_ = lean_ctor_get(v_roots_4361_, 0);
v_buckets_4367_ = lean_ctor_get(v_roots_4361_, 1);
v___x_4368_ = lean_nat_dec_le(v_size_4363_, v_size_4366_);
if (v___x_4368_ == 0)
{
lean_object* v___f_4369_; 
lean_inc_ref(v_buckets_4367_);
lean_inc_ref(v_tries_4365_);
lean_dec_ref(v_x_4343_);
v___f_4369_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4346_ = v_y_4344_;
v_buckets_4347_ = v_buckets_4367_;
v_tries_4348_ = v_tries_4365_;
v_snd_4349_ = v___f_4369_;
goto v___jp_4345_;
}
else
{
lean_object* v___f_4370_; 
lean_inc_ref(v_buckets_4364_);
lean_inc_ref(v_tries_4362_);
lean_dec_ref(v_y_4344_);
v___f_4370_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4346_ = v_x_4343_;
v_buckets_4347_ = v_buckets_4364_;
v_tries_4348_ = v_tries_4362_;
v_snd_4349_ = v___f_4370_;
goto v___jp_4345_;
}
v___jp_4345_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4350_ = lean_unsigned_to_nat(0u);
v___x_4351_ = lean_array_get_size(v_buckets_4347_);
v___x_4352_ = lean_nat_dec_lt(v___x_4350_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_dec_ref(v_tries_4348_);
lean_dec_ref(v_buckets_4347_);
return v_fst_4346_;
}
else
{
uint8_t v___x_4353_; 
v___x_4353_ = lean_nat_dec_le(v___x_4351_, v___x_4351_);
if (v___x_4353_ == 0)
{
if (v___x_4352_ == 0)
{
lean_dec_ref(v_tries_4348_);
lean_dec_ref(v_buckets_4347_);
return v_fst_4346_;
}
else
{
size_t v___x_4354_; size_t v___x_4355_; lean_object* v___x_4356_; 
v___x_4354_ = ((size_t)0ULL);
v___x_4355_ = lean_usize_of_nat(v___x_4351_);
lean_inc_ref(v_snd_4349_);
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4348_, v_snd_4349_, v_buckets_4347_, v___x_4354_, v___x_4355_, v_fst_4346_);
lean_dec_ref(v_buckets_4347_);
lean_dec_ref(v_tries_4348_);
return v___x_4356_;
}
}
else
{
size_t v___x_4357_; size_t v___x_4358_; lean_object* v___x_4359_; 
v___x_4357_ = ((size_t)0ULL);
v___x_4358_ = lean_usize_of_nat(v___x_4351_);
lean_inc_ref(v_snd_4349_);
v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4348_, v_snd_4349_, v_buckets_4347_, v___x_4357_, v___x_4358_, v_fst_4346_);
lean_dec_ref(v_buckets_4347_);
lean_dec_ref(v_tries_4348_);
return v___x_4359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4371_, lean_object* v_x_4372_, lean_object* v_y_4373_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4372_, v_y_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4375_, lean_object* v_tries_4376_, lean_object* v_snd_4377_, lean_object* v_x_4378_, lean_object* v_x_4379_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4376_, v_snd_4377_, v_x_4378_, v_x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4381_, lean_object* v_tries_4382_, lean_object* v_snd_4383_, lean_object* v_x_4384_, lean_object* v_x_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4381_, v_tries_4382_, v_snd_4383_, v_x_4384_, v_x_4385_);
lean_dec_ref(v_tries_4382_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4387_, lean_object* v_tries_4388_, lean_object* v_snd_4389_, lean_object* v_as_4390_, size_t v_i_4391_, size_t v_stop_4392_, lean_object* v_b_4393_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4388_, v_snd_4389_, v_as_4390_, v_i_4391_, v_stop_4392_, v_b_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4395_, lean_object* v_tries_4396_, lean_object* v_snd_4397_, lean_object* v_as_4398_, lean_object* v_i_4399_, lean_object* v_stop_4400_, lean_object* v_b_4401_){
_start:
{
size_t v_i_boxed_4402_; size_t v_stop_boxed_4403_; lean_object* v_res_4404_; 
v_i_boxed_4402_ = lean_unbox_usize(v_i_4399_);
lean_dec(v_i_4399_);
v_stop_boxed_4403_ = lean_unbox_usize(v_stop_4400_);
lean_dec(v_stop_4400_);
v_res_4404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4395_, v_tries_4396_, v_snd_4397_, v_as_4398_, v_i_boxed_4402_, v_stop_boxed_4403_, v_b_4401_);
lean_dec_ref(v_as_4398_);
lean_dec_ref(v_tries_4396_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4406_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4408_, lean_object* v_value_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4408_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4437_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4418_ = v___x_4415_;
v_isShared_4419_ = v_isSharedCheck_4437_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4415_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4437_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v_fst_4420_; lean_object* v_snd_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4436_; 
v_fst_4420_ = lean_ctor_get(v_a_4416_, 0);
v_snd_4421_ = lean_ctor_get(v_a_4416_, 1);
v_isSharedCheck_4436_ = !lean_is_exclusive(v_a_4416_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4423_ = v_a_4416_;
v_isShared_4424_ = v_isSharedCheck_4436_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_snd_4421_);
lean_inc(v_fst_4420_);
lean_dec(v_a_4416_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4436_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v_lctx_4425_; lean_object* v_localInstances_4426_; lean_object* v___x_4428_; 
v_lctx_4425_ = lean_ctor_get(v_a_4410_, 2);
v_localInstances_4426_ = lean_ctor_get(v_a_4410_, 3);
lean_inc_ref(v_localInstances_4426_);
lean_inc_ref(v_lctx_4425_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 1, v_localInstances_4426_);
lean_ctor_set(v___x_4423_, 0, v_lctx_4425_);
v___x_4428_ = v___x_4423_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_lctx_4425_);
lean_ctor_set(v_reuseFailAlloc_4435_, 1, v_localInstances_4426_);
v___x_4428_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4433_; 
v___x_4429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
lean_ctor_set(v___x_4429_, 1, v_value_4409_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v_snd_4421_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4431_, 0, v_fst_4420_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4431_);
v___x_4433_ = v___x_4418_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_value_4409_);
v_a_4438_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4415_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4415_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4446_, lean_object* v_value_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4446_, v_value_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_);
lean_dec(v_a_4451_);
lean_dec_ref(v_a_4450_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4454_, lean_object* v_expr_4455_, lean_object* v_value_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4455_, v_value_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4463_, lean_object* v_expr_4464_, lean_object* v_value_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4463_, v_expr_4464_, v_value_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4472_, lean_object* v_idx_4473_, lean_object* v_value_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_){
_start:
{
lean_object* v_entry_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4526_; 
v_entry_4480_ = lean_ctor_get(v_e_4472_, 1);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_e_4472_);
if (v_isSharedCheck_4526_ == 0)
{
lean_object* v_unused_4527_; 
v_unused_4527_ = lean_ctor_get(v_e_4472_, 0);
lean_dec(v_unused_4527_);
v___x_4482_ = v_e_4472_;
v_isShared_4483_ = v_isSharedCheck_4526_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_entry_4480_);
lean_dec(v_e_4472_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4526_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v_snd_4484_; lean_object* v_fst_4485_; lean_object* v_fst_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4524_; 
v_snd_4484_ = lean_ctor_get(v_entry_4480_, 1);
lean_inc(v_snd_4484_);
v_fst_4485_ = lean_ctor_get(v_entry_4480_, 0);
lean_inc(v_fst_4485_);
lean_dec_ref(v_entry_4480_);
v_fst_4486_ = lean_ctor_get(v_snd_4484_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_snd_4484_);
if (v_isSharedCheck_4524_ == 0)
{
lean_object* v_unused_4525_; 
v_unused_4525_ = lean_ctor_get(v_snd_4484_, 1);
lean_dec(v_unused_4525_);
v___x_4488_ = v_snd_4484_;
v_isShared_4489_ = v_isSharedCheck_4524_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_fst_4486_);
lean_dec(v_snd_4484_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4524_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = l_Lean_instInhabitedExpr;
v___x_4491_ = lean_array_get(v___x_4490_, v_fst_4485_, v_idx_4473_);
lean_dec(v_fst_4485_);
v___x_4492_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4491_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4515_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4495_ = v___x_4492_;
v_isShared_4496_ = v_isSharedCheck_4515_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4515_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v_fst_4497_; lean_object* v_snd_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4514_; 
v_fst_4497_ = lean_ctor_get(v_a_4493_, 0);
v_snd_4498_ = lean_ctor_get(v_a_4493_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_a_4493_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4500_ = v_a_4493_;
v_isShared_4501_ = v_isSharedCheck_4514_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_snd_4498_);
lean_inc(v_fst_4497_);
lean_dec(v_a_4493_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4514_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 1, v_value_4474_);
lean_ctor_set(v___x_4500_, 0, v_fst_4486_);
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_fst_4486_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_value_4474_);
v___x_4503_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4505_; 
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 1, v___x_4503_);
lean_ctor_set(v___x_4488_, 0, v_snd_4498_);
v___x_4505_ = v___x_4488_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_snd_4498_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v___x_4503_);
v___x_4505_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4507_; 
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 1, v___x_4505_);
lean_ctor_set(v___x_4482_, 0, v_fst_4497_);
v___x_4507_ = v___x_4482_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_fst_4497_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4509_; 
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4507_);
v___x_4509_ = v___x_4495_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_del_object(v___x_4488_);
lean_dec(v_fst_4486_);
lean_del_object(v___x_4482_);
lean_dec(v_value_4474_);
v_a_4516_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4492_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4492_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4528_, lean_object* v_idx_4529_, lean_object* v_value_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4528_, v_idx_4529_, v_value_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_idx_4529_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4537_, lean_object* v_e_4538_, lean_object* v_idx_4539_, lean_object* v_value_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4538_, v_idx_4539_, v_value_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4547_, lean_object* v_e_4548_, lean_object* v_idx_4549_, lean_object* v_value_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4547_, v_e_4548_, v_idx_4549_, v_value_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_idx_4549_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4560_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4561_ = lean_st_mk_ref(v___x_4560_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4563_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4564_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
return v___x_4566_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
lean_ctor_set(v___x_4568_, 1, v___x_4567_);
return v___x_4568_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4570_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
lean_ctor_set(v___x_4570_, 2, v___x_4569_);
lean_ctor_set(v___x_4570_, 3, v___x_4569_);
lean_ctor_set(v___x_4570_, 4, v___x_4569_);
lean_ctor_set(v___x_4570_, 5, v___x_4569_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4571_){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4573_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4574_, 0, v_ngen_4571_);
lean_ctor_set(v___x_4574_, 1, v___x_4572_);
lean_ctor_set(v___x_4574_, 2, v___x_4573_);
return v___x_4574_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4575_, lean_object* v_declName_4576_){
_start:
{
uint8_t v___x_4577_; uint8_t v___x_4578_; 
v___x_4577_ = l_Lean_isPrivateName(v_declName_4576_);
v___x_4578_ = lean_bool_not(v___x_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4575_, v_declName_4576_);
if (lean_obj_tag(v___x_4579_) == 0)
{
uint8_t v___x_4580_; 
v___x_4580_ = 1;
return v___x_4580_;
}
else
{
lean_object* v_val_4581_; lean_object* v___x_4582_; uint8_t v_isModule_4583_; 
v_val_4581_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_val_4581_);
lean_dec_ref_known(v___x_4579_, 1);
v___x_4582_ = l_Lean_Environment_header(v_env_4575_);
v_isModule_4583_ = lean_ctor_get_uint8(v___x_4582_, sizeof(void*)*7 + 4);
if (v_isModule_4583_ == 0)
{
lean_dec_ref(v___x_4582_);
lean_dec(v_val_4581_);
return v_isModule_4583_;
}
else
{
lean_object* v_modules_4584_; lean_object* v___x_4585_; uint8_t v___x_4586_; 
v_modules_4584_ = lean_ctor_get(v___x_4582_, 3);
lean_inc_ref(v_modules_4584_);
lean_dec_ref(v___x_4582_);
v___x_4585_ = lean_array_get_size(v_modules_4584_);
v___x_4586_ = lean_nat_dec_lt(v_val_4581_, v___x_4585_);
if (v___x_4586_ == 0)
{
lean_dec_ref(v_modules_4584_);
lean_dec(v_val_4581_);
return v___x_4578_;
}
else
{
lean_object* v___x_4587_; lean_object* v_toImport_4588_; uint8_t v_importAll_4589_; 
v___x_4587_ = lean_array_fget(v_modules_4584_, v_val_4581_);
lean_dec(v_val_4581_);
lean_dec_ref(v_modules_4584_);
v_toImport_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc_ref(v_toImport_4588_);
lean_dec(v___x_4587_);
v_importAll_4589_ = lean_ctor_get_uint8(v_toImport_4588_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4588_);
return v_importAll_4589_;
}
}
}
}
else
{
uint8_t v___x_4590_; 
v___x_4590_ = 0;
return v___x_4590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4591_, lean_object* v_declName_4592_){
_start:
{
uint8_t v_res_4593_; lean_object* v_r_4594_; 
v_res_4593_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4591_, v_declName_4592_);
lean_dec(v_declName_4592_);
lean_dec_ref(v_env_4591_);
v_r_4594_ = lean_box(v_res_4593_);
return v_r_4594_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4600_, lean_object* v_declName_4601_){
_start:
{
uint8_t v___y_4603_; uint8_t v___y_4608_; uint8_t v___y_4613_; uint8_t v___x_4617_; uint8_t v___x_4618_; 
lean_inc(v_declName_4601_);
lean_inc_ref(v_env_4600_);
v___x_4617_ = l_Lean_Meta_allowCompletion(v_env_4600_, v_declName_4601_);
v___x_4618_ = lean_bool_not(v___x_4617_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; uint8_t v___x_4620_; 
v___x_4619_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4620_ = lean_name_eq(v_declName_4601_, v___x_4619_);
v___y_4613_ = v___x_4620_;
goto v___jp_4612_;
}
else
{
v___y_4613_ = v___x_4618_;
goto v___jp_4612_;
}
v___jp_4602_:
{
if (lean_obj_tag(v_declName_4601_) == 1)
{
lean_object* v_str_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; 
v_str_4604_ = lean_ctor_get(v_declName_4601_, 1);
lean_inc_ref(v_str_4604_);
lean_dec_ref_known(v_declName_4601_, 2);
v___x_4605_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0));
v___x_4606_ = lean_string_dec_eq(v_str_4604_, v___x_4605_);
lean_dec_ref(v_str_4604_);
if (v___x_4606_ == 0)
{
return v___y_4603_;
}
else
{
return v___x_4606_;
}
}
else
{
lean_dec(v_declName_4601_);
return v___y_4603_;
}
}
v___jp_4607_:
{
if (v___y_4608_ == 0)
{
if (lean_obj_tag(v_declName_4601_) == 1)
{
lean_object* v_str_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; 
v_str_4609_ = lean_ctor_get(v_declName_4601_, 1);
v___x_4610_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4611_ = lean_string_dec_eq(v_str_4609_, v___x_4610_);
if (v___x_4611_ == 0)
{
v___y_4603_ = v___y_4608_;
goto v___jp_4602_;
}
else
{
lean_dec_ref_known(v_declName_4601_, 2);
return v___x_4611_;
}
}
else
{
v___y_4603_ = v___y_4608_;
goto v___jp_4602_;
}
}
else
{
lean_dec(v_declName_4601_);
return v___y_4608_;
}
}
v___jp_4612_:
{
if (v___y_4613_ == 0)
{
uint8_t v___x_4614_; 
lean_inc(v_declName_4601_);
v___x_4614_ = l_Lean_Name_isInternalDetail(v_declName_4601_);
if (v___x_4614_ == 0)
{
lean_dec_ref(v_env_4600_);
v___y_4608_ = v___x_4614_;
goto v___jp_4607_;
}
else
{
uint8_t v___x_4615_; uint8_t v___x_4616_; 
v___x_4615_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4600_, v_declName_4601_);
lean_dec_ref(v_env_4600_);
v___x_4616_ = lean_bool_not(v___x_4615_);
v___y_4608_ = v___x_4616_;
goto v___jp_4607_;
}
}
else
{
lean_dec(v_declName_4601_);
lean_dec_ref(v_env_4600_);
return v___y_4613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4621_, lean_object* v_declName_4622_){
_start:
{
uint8_t v_res_4623_; lean_object* v_r_4624_; 
v_res_4623_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4621_, v_declName_4622_);
v_r_4624_ = lean_box(v_res_4623_);
return v_r_4624_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4625_, lean_object* v_opt_4626_){
_start:
{
lean_object* v_name_4627_; lean_object* v_defValue_4628_; lean_object* v_map_4629_; lean_object* v___x_4630_; 
v_name_4627_ = lean_ctor_get(v_opt_4626_, 0);
v_defValue_4628_ = lean_ctor_get(v_opt_4626_, 1);
v_map_4629_ = lean_ctor_get(v_opts_4625_, 0);
v___x_4630_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4629_, v_name_4627_);
if (lean_obj_tag(v___x_4630_) == 0)
{
uint8_t v___x_4631_; 
v___x_4631_ = lean_unbox(v_defValue_4628_);
return v___x_4631_;
}
else
{
lean_object* v_val_4632_; 
v_val_4632_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_val_4632_);
lean_dec_ref_known(v___x_4630_, 1);
if (lean_obj_tag(v_val_4632_) == 1)
{
uint8_t v_v_4633_; 
v_v_4633_ = lean_ctor_get_uint8(v_val_4632_, 0);
lean_dec_ref_known(v_val_4632_, 0);
return v_v_4633_;
}
else
{
uint8_t v___x_4634_; 
lean_dec(v_val_4632_);
v___x_4634_ = lean_unbox(v_defValue_4628_);
return v___x_4634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4635_, lean_object* v_opt_4636_){
_start:
{
uint8_t v_res_4637_; lean_object* v_r_4638_; 
v_res_4637_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4635_, v_opt_4636_);
lean_dec_ref(v_opt_4636_);
lean_dec_ref(v_opts_4635_);
v_r_4638_ = lean_box(v_res_4637_);
return v_r_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4639_, lean_object* v_opt_4640_){
_start:
{
lean_object* v_name_4641_; lean_object* v_defValue_4642_; lean_object* v_map_4643_; lean_object* v___x_4644_; 
v_name_4641_ = lean_ctor_get(v_opt_4640_, 0);
v_defValue_4642_ = lean_ctor_get(v_opt_4640_, 1);
v_map_4643_ = lean_ctor_get(v_opts_4639_, 0);
v___x_4644_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4643_, v_name_4641_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_inc(v_defValue_4642_);
return v_defValue_4642_;
}
else
{
lean_object* v_val_4645_; 
v_val_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_val_4645_);
lean_dec_ref_known(v___x_4644_, 1);
if (lean_obj_tag(v_val_4645_) == 3)
{
lean_object* v_v_4646_; 
v_v_4646_ = lean_ctor_get(v_val_4645_, 0);
lean_inc(v_v_4646_);
lean_dec_ref_known(v_val_4645_, 1);
return v_v_4646_;
}
else
{
lean_dec(v_val_4645_);
lean_inc(v_defValue_4642_);
return v_defValue_4642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4647_, lean_object* v_opt_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4647_, v_opt_4648_);
lean_dec_ref(v_opt_4648_);
lean_dec_ref(v_opts_4647_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4650_, size_t v_i_4651_, size_t v_stop_4652_, lean_object* v_b_4653_){
_start:
{
uint8_t v___x_4654_; 
v___x_4654_ = lean_usize_dec_eq(v_i_4651_, v_stop_4652_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; lean_object* v_key_4656_; lean_object* v_entry_4657_; lean_object* v___x_4658_; size_t v___x_4659_; size_t v___x_4660_; 
v___x_4655_ = lean_array_uget_borrowed(v_as_4650_, v_i_4651_);
v_key_4656_ = lean_ctor_get(v___x_4655_, 0);
v_entry_4657_ = lean_ctor_get(v___x_4655_, 1);
lean_inc_ref(v_entry_4657_);
lean_inc(v_key_4656_);
v___x_4658_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4653_, v_key_4656_, v_entry_4657_);
v___x_4659_ = ((size_t)1ULL);
v___x_4660_ = lean_usize_add(v_i_4651_, v___x_4659_);
v_i_4651_ = v___x_4660_;
v_b_4653_ = v___x_4658_;
goto _start;
}
else
{
return v_b_4653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4662_, lean_object* v_i_4663_, lean_object* v_stop_4664_, lean_object* v_b_4665_){
_start:
{
size_t v_i_boxed_4666_; size_t v_stop_boxed_4667_; lean_object* v_res_4668_; 
v_i_boxed_4666_ = lean_unbox_usize(v_i_4663_);
lean_dec(v_i_4663_);
v_stop_boxed_4667_ = lean_unbox_usize(v_stop_4664_);
lean_dec(v_stop_4664_);
v_res_4668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4662_, v_i_boxed_4666_, v_stop_boxed_4667_, v_b_4665_);
lean_dec_ref(v_as_4662_);
return v_res_4668_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4669_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
return v___x_4671_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4673_ = lean_unsigned_to_nat(0u);
v___x_4674_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
lean_ctor_set(v___x_4674_, 2, v___x_4673_);
lean_ctor_set(v___x_4674_, 3, v___x_4673_);
lean_ctor_set(v___x_4674_, 4, v___x_4672_);
lean_ctor_set(v___x_4674_, 5, v___x_4672_);
lean_ctor_set(v___x_4674_, 6, v___x_4672_);
lean_ctor_set(v___x_4674_, 7, v___x_4672_);
lean_ctor_set(v___x_4674_, 8, v___x_4672_);
lean_ctor_set(v___x_4674_, 9, v___x_4672_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = lean_unsigned_to_nat(32u);
v___x_4676_ = lean_mk_empty_array_with_capacity(v___x_4675_);
v___x_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
return v___x_4677_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4678_ = ((size_t)5ULL);
v___x_4679_ = lean_unsigned_to_nat(0u);
v___x_4680_ = lean_unsigned_to_nat(32u);
v___x_4681_ = lean_mk_empty_array_with_capacity(v___x_4680_);
v___x_4682_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4683_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
lean_ctor_set(v___x_4683_, 1, v___x_4681_);
lean_ctor_set(v___x_4683_, 2, v___x_4679_);
lean_ctor_set(v___x_4683_, 3, v___x_4679_);
lean_ctor_set_usize(v___x_4683_, 4, v___x_4678_);
return v___x_4683_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4684_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
lean_ctor_set(v___x_4685_, 2, v___x_4684_);
lean_ctor_set(v___x_4685_, 3, v___x_4684_);
lean_ctor_set(v___x_4685_, 4, v___x_4684_);
return v___x_4685_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4686_ = lean_box(1);
v___x_4687_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4688_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set(v___x_4689_, 1, v___x_4687_);
lean_ctor_set(v___x_4689_, 2, v___x_4686_);
return v___x_4689_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4692_ = lean_unsigned_to_nat(1u);
v___x_4693_ = l_Lean_firstFrontendMacroScope;
v___x_4694_ = lean_nat_add(v___x_4693_, v___x_4692_);
return v___x_4694_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4699_; uint64_t v___x_4700_; lean_object* v___x_4701_; 
v___x_4699_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4700_ = 0ULL;
v___x_4701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4701_, 0, v___x_4699_);
lean_ctor_set_uint64(v___x_4701_, sizeof(void*)*1, v___x_4700_);
return v___x_4701_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = l_Lean_NameSet_empty;
v___x_4703_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
lean_ctor_set(v___x_4704_, 1, v___x_4703_);
lean_ctor_set(v___x_4704_, 2, v___x_4702_);
return v___x_4704_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; lean_object* v___x_4708_; 
v___x_4705_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4706_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4707_ = 1;
v___x_4708_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4708_, 0, v___x_4706_);
lean_ctor_set(v___x_4708_, 1, v___x_4706_);
lean_ctor_set(v___x_4708_, 2, v___x_4705_);
lean_ctor_set_uint8(v___x_4708_, sizeof(void*)*3, v___x_4707_);
return v___x_4708_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
lean_ctor_set(v___x_4710_, 1, v___x_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4711_, lean_object* v_env_4712_, lean_object* v_modName_4713_, lean_object* v_d_4714_, lean_object* v_cacheRef_4715_, lean_object* v_tree_4716_, lean_object* v_act_4717_, lean_object* v_c_4718_){
_start:
{
uint8_t v___x_4720_; 
lean_inc_ref(v_c_4718_);
v___x_4720_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4718_);
if (v___x_4720_ == 0)
{
lean_object* v_name_4721_; uint8_t v___x_4722_; 
v_name_4721_ = lean_ctor_get(v_c_4718_, 0);
lean_inc_n(v_name_4721_, 2);
lean_inc_ref(v_env_4712_);
v___x_4722_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4712_, v_name_4721_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; lean_object* v_ngen_4724_; lean_object* v_core_4725_; lean_object* v_meta_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4861_; 
v___x_4723_ = lean_st_ref_get(v_cacheRef_4715_);
v_ngen_4724_ = lean_ctor_get(v___x_4723_, 0);
v_core_4725_ = lean_ctor_get(v___x_4723_, 1);
v_meta_4726_ = lean_ctor_get(v___x_4723_, 2);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4728_ = v___x_4723_;
v_isShared_4729_ = v_isSharedCheck_4861_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_meta_4726_);
lean_inc(v_core_4725_);
lean_inc(v_ngen_4724_);
lean_dec(v___x_4723_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4861_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; uint8_t v___x_4740_; uint8_t v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v_fileName_4758_; lean_object* v_fileMap_4759_; lean_object* v_options_4760_; lean_object* v_currRecDepth_4761_; lean_object* v_maxRecDepth_4762_; lean_object* v_ref_4763_; lean_object* v_currNamespace_4764_; lean_object* v_openDecls_4765_; lean_object* v_initHeartbeats_4766_; lean_object* v_maxHeartbeats_4767_; lean_object* v_quotContext_4768_; lean_object* v_currMacroScope_4769_; uint8_t v_diag_4770_; lean_object* v_cancelTk_x3f_4771_; uint8_t v_suppressElabErrors_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4859_; 
v___x_4730_ = lean_unsigned_to_nat(0u);
v___x_4731_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4732_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4733_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4724_);
v___x_4734_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4724_);
v___x_4735_ = lean_st_ref_set(v_cacheRef_4715_, v___x_4734_);
v___x_4736_ = lean_box(1);
v___x_4737_ = 1;
v___x_4738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4731_);
lean_ctor_set(v___x_4738_, 1, v_meta_4726_);
lean_ctor_set(v___x_4738_, 2, v___x_4736_);
lean_ctor_set(v___x_4738_, 3, v___x_4732_);
lean_ctor_set(v___x_4738_, 4, v___x_4733_);
v___x_4739_ = 2;
v___x_4740_ = 0;
v___x_4741_ = 2;
v___x_4742_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4742_, 0, v___x_4722_);
lean_ctor_set_uint8(v___x_4742_, 1, v___x_4722_);
lean_ctor_set_uint8(v___x_4742_, 2, v___x_4722_);
lean_ctor_set_uint8(v___x_4742_, 3, v___x_4722_);
lean_ctor_set_uint8(v___x_4742_, 4, v___x_4722_);
lean_ctor_set_uint8(v___x_4742_, 5, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 6, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 7, v___x_4722_);
lean_ctor_set_uint8(v___x_4742_, 8, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 9, v___x_4739_);
lean_ctor_set_uint8(v___x_4742_, 10, v___x_4740_);
lean_ctor_set_uint8(v___x_4742_, 11, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 12, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 13, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 14, v___x_4741_);
lean_ctor_set_uint8(v___x_4742_, 15, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 16, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 17, v___x_4737_);
lean_ctor_set_uint8(v___x_4742_, 18, v___x_4737_);
v___x_4743_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4742_);
v___x_4744_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4745_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4746_ = lean_box(0);
v___x_4747_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4747_, 0, v___x_4743_);
lean_ctor_set(v___x_4747_, 1, v___x_4736_);
lean_ctor_set(v___x_4747_, 2, v___x_4744_);
lean_ctor_set(v___x_4747_, 3, v___x_4745_);
lean_ctor_set(v___x_4747_, 4, v___x_4746_);
lean_ctor_set(v___x_4747_, 5, v___x_4730_);
lean_ctor_set(v___x_4747_, 6, v___x_4746_);
lean_ctor_set_uint8(v___x_4747_, sizeof(void*)*7, v___x_4722_);
lean_ctor_set_uint8(v___x_4747_, sizeof(void*)*7 + 1, v___x_4722_);
lean_ctor_set_uint8(v___x_4747_, sizeof(void*)*7 + 2, v___x_4722_);
lean_ctor_set_uint8(v___x_4747_, sizeof(void*)*7 + 3, v___x_4737_);
v___x_4748_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4749_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4750_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4751_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4752_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4753_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4753_, 0, v_env_4712_);
lean_ctor_set(v___x_4753_, 1, v___x_4748_);
lean_ctor_set(v___x_4753_, 2, v_ngen_4724_);
lean_ctor_set(v___x_4753_, 3, v___x_4749_);
lean_ctor_set(v___x_4753_, 4, v___x_4750_);
lean_ctor_set(v___x_4753_, 5, v_core_4725_);
lean_ctor_set(v___x_4753_, 6, v___x_4751_);
lean_ctor_set(v___x_4753_, 7, v___x_4752_);
lean_ctor_set(v___x_4753_, 8, v___x_4745_);
v___x_4754_ = lean_st_mk_ref(v___x_4753_);
v___x_4755_ = l_Lean_inheritedTraceOptions;
v___x_4756_ = lean_st_ref_get(v___x_4755_);
v___x_4757_ = lean_st_ref_get(v___x_4754_);
v_fileName_4758_ = lean_ctor_get(v_cctx_4711_, 0);
v_fileMap_4759_ = lean_ctor_get(v_cctx_4711_, 1);
v_options_4760_ = lean_ctor_get(v_cctx_4711_, 2);
v_currRecDepth_4761_ = lean_ctor_get(v_cctx_4711_, 3);
v_maxRecDepth_4762_ = lean_ctor_get(v_cctx_4711_, 4);
v_ref_4763_ = lean_ctor_get(v_cctx_4711_, 5);
v_currNamespace_4764_ = lean_ctor_get(v_cctx_4711_, 6);
v_openDecls_4765_ = lean_ctor_get(v_cctx_4711_, 7);
v_initHeartbeats_4766_ = lean_ctor_get(v_cctx_4711_, 8);
v_maxHeartbeats_4767_ = lean_ctor_get(v_cctx_4711_, 9);
v_quotContext_4768_ = lean_ctor_get(v_cctx_4711_, 10);
v_currMacroScope_4769_ = lean_ctor_get(v_cctx_4711_, 11);
v_diag_4770_ = lean_ctor_get_uint8(v_cctx_4711_, sizeof(void*)*14);
v_cancelTk_x3f_4771_ = lean_ctor_get(v_cctx_4711_, 12);
v_suppressElabErrors_4772_ = lean_ctor_get_uint8(v_cctx_4711_, sizeof(void*)*14 + 1);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_cctx_4711_);
if (v_isSharedCheck_4859_ == 0)
{
lean_object* v_unused_4860_; 
v_unused_4860_ = lean_ctor_get(v_cctx_4711_, 13);
lean_dec(v_unused_4860_);
v___x_4774_ = v_cctx_4711_;
v_isShared_4775_ = v_isSharedCheck_4859_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_cancelTk_x3f_4771_);
lean_inc(v_currMacroScope_4769_);
lean_inc(v_quotContext_4768_);
lean_inc(v_maxHeartbeats_4767_);
lean_inc(v_initHeartbeats_4766_);
lean_inc(v_openDecls_4765_);
lean_inc(v_currNamespace_4764_);
lean_inc(v_ref_4763_);
lean_inc(v_maxRecDepth_4762_);
lean_inc(v_currRecDepth_4761_);
lean_inc(v_options_4760_);
lean_inc(v_fileMap_4759_);
lean_inc(v_fileName_4758_);
lean_dec(v_cctx_4711_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4859_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v_env_4776_; lean_object* v___x_4778_; 
v_env_4776_ = lean_ctor_get(v___x_4757_, 0);
lean_inc_ref(v_env_4776_);
lean_dec(v___x_4757_);
lean_inc_ref(v_options_4760_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 13, v___x_4756_);
v___x_4778_ = v___x_4774_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_fileName_4758_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_fileMap_4759_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_options_4760_);
lean_ctor_set(v_reuseFailAlloc_4858_, 3, v_currRecDepth_4761_);
lean_ctor_set(v_reuseFailAlloc_4858_, 4, v_maxRecDepth_4762_);
lean_ctor_set(v_reuseFailAlloc_4858_, 5, v_ref_4763_);
lean_ctor_set(v_reuseFailAlloc_4858_, 6, v_currNamespace_4764_);
lean_ctor_set(v_reuseFailAlloc_4858_, 7, v_openDecls_4765_);
lean_ctor_set(v_reuseFailAlloc_4858_, 8, v_initHeartbeats_4766_);
lean_ctor_set(v_reuseFailAlloc_4858_, 9, v_maxHeartbeats_4767_);
lean_ctor_set(v_reuseFailAlloc_4858_, 10, v_quotContext_4768_);
lean_ctor_set(v_reuseFailAlloc_4858_, 11, v_currMacroScope_4769_);
lean_ctor_set(v_reuseFailAlloc_4858_, 12, v_cancelTk_x3f_4771_);
lean_ctor_set(v_reuseFailAlloc_4858_, 13, v___x_4756_);
lean_ctor_set_uint8(v_reuseFailAlloc_4858_, sizeof(void*)*14, v_diag_4770_);
lean_ctor_set_uint8(v_reuseFailAlloc_4858_, sizeof(void*)*14 + 1, v_suppressElabErrors_4772_);
v___x_4778_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
lean_object* v___x_4779_; uint8_t v___x_4780_; lean_object* v___y_4782_; lean_object* v___y_4783_; uint8_t v___y_4835_; uint8_t v___x_4857_; 
v___x_4779_ = l_Lean_diagnostics;
v___x_4780_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4760_, v___x_4779_);
v___x_4857_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4776_);
lean_dec_ref(v_env_4776_);
if (v___x_4857_ == 0)
{
if (v___x_4780_ == 0)
{
v___y_4835_ = v___x_4737_;
goto v___jp_4834_;
}
else
{
v___y_4835_ = v___x_4857_;
goto v___jp_4834_;
}
}
else
{
v___y_4835_ = v___x_4780_;
goto v___jp_4834_;
}
v___jp_4781_:
{
lean_object* v___x_4784_; lean_object* v_fileName_4785_; lean_object* v_fileMap_4786_; lean_object* v_currRecDepth_4787_; lean_object* v_ref_4788_; lean_object* v_currNamespace_4789_; lean_object* v_openDecls_4790_; lean_object* v_initHeartbeats_4791_; lean_object* v_maxHeartbeats_4792_; lean_object* v_quotContext_4793_; lean_object* v_currMacroScope_4794_; lean_object* v_cancelTk_x3f_4795_; uint8_t v_suppressElabErrors_4796_; lean_object* v_inheritedTraceOptions_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4831_; 
v___x_4784_ = lean_st_mk_ref(v___x_4738_);
v_fileName_4785_ = lean_ctor_get(v___y_4782_, 0);
v_fileMap_4786_ = lean_ctor_get(v___y_4782_, 1);
v_currRecDepth_4787_ = lean_ctor_get(v___y_4782_, 3);
v_ref_4788_ = lean_ctor_get(v___y_4782_, 5);
v_currNamespace_4789_ = lean_ctor_get(v___y_4782_, 6);
v_openDecls_4790_ = lean_ctor_get(v___y_4782_, 7);
v_initHeartbeats_4791_ = lean_ctor_get(v___y_4782_, 8);
v_maxHeartbeats_4792_ = lean_ctor_get(v___y_4782_, 9);
v_quotContext_4793_ = lean_ctor_get(v___y_4782_, 10);
v_currMacroScope_4794_ = lean_ctor_get(v___y_4782_, 11);
v_cancelTk_x3f_4795_ = lean_ctor_get(v___y_4782_, 12);
v_suppressElabErrors_4796_ = lean_ctor_get_uint8(v___y_4782_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4797_ = lean_ctor_get(v___y_4782_, 13);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___y_4782_);
if (v_isSharedCheck_4831_ == 0)
{
lean_object* v_unused_4832_; lean_object* v_unused_4833_; 
v_unused_4832_ = lean_ctor_get(v___y_4782_, 4);
lean_dec(v_unused_4832_);
v_unused_4833_ = lean_ctor_get(v___y_4782_, 2);
lean_dec(v_unused_4833_);
v___x_4799_ = v___y_4782_;
v_isShared_4800_ = v_isSharedCheck_4831_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_inheritedTraceOptions_4797_);
lean_inc(v_cancelTk_x3f_4795_);
lean_inc(v_currMacroScope_4794_);
lean_inc(v_quotContext_4793_);
lean_inc(v_maxHeartbeats_4792_);
lean_inc(v_initHeartbeats_4791_);
lean_inc(v_openDecls_4790_);
lean_inc(v_currNamespace_4789_);
lean_inc(v_ref_4788_);
lean_inc(v_currRecDepth_4787_);
lean_inc(v_fileMap_4786_);
lean_inc(v_fileName_4785_);
lean_dec(v___y_4782_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4831_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
v___x_4801_ = l_Lean_maxRecDepth;
v___x_4802_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4760_, v___x_4801_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 4, v___x_4802_);
lean_ctor_set(v___x_4799_, 2, v_options_4760_);
v___x_4804_ = v___x_4799_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_fileName_4785_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_fileMap_4786_);
lean_ctor_set(v_reuseFailAlloc_4830_, 2, v_options_4760_);
lean_ctor_set(v_reuseFailAlloc_4830_, 3, v_currRecDepth_4787_);
lean_ctor_set(v_reuseFailAlloc_4830_, 4, v___x_4802_);
lean_ctor_set(v_reuseFailAlloc_4830_, 5, v_ref_4788_);
lean_ctor_set(v_reuseFailAlloc_4830_, 6, v_currNamespace_4789_);
lean_ctor_set(v_reuseFailAlloc_4830_, 7, v_openDecls_4790_);
lean_ctor_set(v_reuseFailAlloc_4830_, 8, v_initHeartbeats_4791_);
lean_ctor_set(v_reuseFailAlloc_4830_, 9, v_maxHeartbeats_4792_);
lean_ctor_set(v_reuseFailAlloc_4830_, 10, v_quotContext_4793_);
lean_ctor_set(v_reuseFailAlloc_4830_, 11, v_currMacroScope_4794_);
lean_ctor_set(v_reuseFailAlloc_4830_, 12, v_cancelTk_x3f_4795_);
lean_ctor_set(v_reuseFailAlloc_4830_, 13, v_inheritedTraceOptions_4797_);
lean_ctor_set_uint8(v_reuseFailAlloc_4830_, sizeof(void*)*14 + 1, v_suppressElabErrors_4796_);
v___x_4804_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_object* v___x_4805_; 
lean_ctor_set_uint8(v___x_4804_, sizeof(void*)*14, v___x_4780_);
lean_inc(v___x_4784_);
lean_inc(v_name_4721_);
v___x_4805_ = lean_apply_7(v_act_4717_, v_name_4721_, v_c_4718_, v___x_4747_, v___x_4784_, v___x_4804_, v___y_4783_, lean_box(0));
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v_ngen_4809_; lean_object* v_cache_4810_; lean_object* v_cache_4811_; lean_object* v___x_4813_; 
lean_dec(v_name_4721_);
lean_dec(v_modName_4713_);
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v___x_4805_, 1);
v___x_4807_ = lean_st_ref_get(v___x_4784_);
lean_dec(v___x_4784_);
v___x_4808_ = lean_st_ref_get(v___x_4754_);
lean_dec(v___x_4754_);
v_ngen_4809_ = lean_ctor_get(v___x_4808_, 2);
lean_inc_ref(v_ngen_4809_);
v_cache_4810_ = lean_ctor_get(v___x_4808_, 5);
lean_inc_ref(v_cache_4810_);
lean_dec(v___x_4808_);
v_cache_4811_ = lean_ctor_get(v___x_4807_, 1);
lean_inc_ref(v_cache_4811_);
lean_dec(v___x_4807_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 2, v_cache_4811_);
lean_ctor_set(v___x_4728_, 1, v_cache_4810_);
lean_ctor_set(v___x_4728_, 0, v_ngen_4809_);
v___x_4813_ = v___x_4728_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_ngen_4809_);
lean_ctor_set(v_reuseFailAlloc_4824_, 1, v_cache_4810_);
lean_ctor_set(v_reuseFailAlloc_4824_, 2, v_cache_4811_);
v___x_4813_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; 
v___x_4814_ = lean_st_ref_set(v_cacheRef_4715_, v___x_4813_);
v___x_4815_ = lean_array_get_size(v_a_4806_);
v___x_4816_ = lean_nat_dec_lt(v___x_4730_, v___x_4815_);
if (v___x_4816_ == 0)
{
lean_dec(v_a_4806_);
return v_tree_4716_;
}
else
{
uint8_t v___x_4817_; 
v___x_4817_ = lean_nat_dec_le(v___x_4815_, v___x_4815_);
if (v___x_4817_ == 0)
{
if (v___x_4816_ == 0)
{
lean_dec(v_a_4806_);
return v_tree_4716_;
}
else
{
size_t v___x_4818_; size_t v___x_4819_; lean_object* v___x_4820_; 
v___x_4818_ = ((size_t)0ULL);
v___x_4819_ = lean_usize_of_nat(v___x_4815_);
v___x_4820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4806_, v___x_4818_, v___x_4819_, v_tree_4716_);
lean_dec(v_a_4806_);
return v___x_4820_;
}
}
else
{
size_t v___x_4821_; size_t v___x_4822_; lean_object* v___x_4823_; 
v___x_4821_ = ((size_t)0ULL);
v___x_4822_ = lean_usize_of_nat(v___x_4815_);
v___x_4823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4806_, v___x_4821_, v___x_4822_, v_tree_4716_);
lean_dec(v_a_4806_);
return v___x_4823_;
}
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
lean_dec(v___x_4784_);
lean_dec(v___x_4754_);
lean_del_object(v___x_4728_);
v_a_4825_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4805_, 1);
v___x_4826_ = lean_st_ref_take(v_d_4714_);
v___x_4827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4827_, 0, v_modName_4713_);
lean_ctor_set(v___x_4827_, 1, v_name_4721_);
lean_ctor_set(v___x_4827_, 2, v_a_4825_);
v___x_4828_ = lean_array_push(v___x_4826_, v___x_4827_);
v___x_4829_ = lean_st_ref_set(v_d_4714_, v___x_4828_);
return v_tree_4716_;
}
}
}
}
v___jp_4834_:
{
uint8_t v___x_4836_; 
v___x_4836_ = lean_bool_not(v___y_4835_);
if (v___x_4836_ == 0)
{
lean_inc(v___x_4754_);
v___y_4782_ = v___x_4778_;
v___y_4783_ = v___x_4754_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4837_; lean_object* v_env_4838_; lean_object* v_nextMacroScope_4839_; lean_object* v_ngen_4840_; lean_object* v_auxDeclNGen_4841_; lean_object* v_traceState_4842_; lean_object* v_messages_4843_; lean_object* v_infoState_4844_; lean_object* v_snapshotTasks_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4855_; 
v___x_4837_ = lean_st_ref_take(v___x_4754_);
v_env_4838_ = lean_ctor_get(v___x_4837_, 0);
v_nextMacroScope_4839_ = lean_ctor_get(v___x_4837_, 1);
v_ngen_4840_ = lean_ctor_get(v___x_4837_, 2);
v_auxDeclNGen_4841_ = lean_ctor_get(v___x_4837_, 3);
v_traceState_4842_ = lean_ctor_get(v___x_4837_, 4);
v_messages_4843_ = lean_ctor_get(v___x_4837_, 6);
v_infoState_4844_ = lean_ctor_get(v___x_4837_, 7);
v_snapshotTasks_4845_ = lean_ctor_get(v___x_4837_, 8);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4837_);
if (v_isSharedCheck_4855_ == 0)
{
lean_object* v_unused_4856_; 
v_unused_4856_ = lean_ctor_get(v___x_4837_, 5);
lean_dec(v_unused_4856_);
v___x_4847_ = v___x_4837_;
v_isShared_4848_ = v_isSharedCheck_4855_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_snapshotTasks_4845_);
lean_inc(v_infoState_4844_);
lean_inc(v_messages_4843_);
lean_inc(v_traceState_4842_);
lean_inc(v_auxDeclNGen_4841_);
lean_inc(v_ngen_4840_);
lean_inc(v_nextMacroScope_4839_);
lean_inc(v_env_4838_);
lean_dec(v___x_4837_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4855_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___x_4849_ = l_Lean_Kernel_enableDiag(v_env_4838_, v___x_4780_);
v___x_4850_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 5, v___x_4850_);
lean_ctor_set(v___x_4847_, 0, v___x_4849_);
v___x_4852_ = v___x_4847_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4849_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v_nextMacroScope_4839_);
lean_ctor_set(v_reuseFailAlloc_4854_, 2, v_ngen_4840_);
lean_ctor_set(v_reuseFailAlloc_4854_, 3, v_auxDeclNGen_4841_);
lean_ctor_set(v_reuseFailAlloc_4854_, 4, v_traceState_4842_);
lean_ctor_set(v_reuseFailAlloc_4854_, 5, v___x_4850_);
lean_ctor_set(v_reuseFailAlloc_4854_, 6, v_messages_4843_);
lean_ctor_set(v_reuseFailAlloc_4854_, 7, v_infoState_4844_);
lean_ctor_set(v_reuseFailAlloc_4854_, 8, v_snapshotTasks_4845_);
v___x_4852_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
lean_object* v___x_4853_; 
v___x_4853_ = lean_st_ref_set(v___x_4754_, v___x_4852_);
lean_inc(v___x_4754_);
v___y_4782_ = v___x_4778_;
v___y_4783_ = v___x_4754_;
goto v___jp_4781_;
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
lean_dec(v_name_4721_);
lean_dec_ref(v_c_4718_);
lean_dec_ref(v_act_4717_);
lean_dec(v_modName_4713_);
lean_dec_ref(v_env_4712_);
lean_dec_ref(v_cctx_4711_);
return v_tree_4716_;
}
}
else
{
lean_dec_ref(v_c_4718_);
lean_dec_ref(v_act_4717_);
lean_dec(v_modName_4713_);
lean_dec_ref(v_env_4712_);
lean_dec_ref(v_cctx_4711_);
return v_tree_4716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4862_, lean_object* v_env_4863_, lean_object* v_modName_4864_, lean_object* v_d_4865_, lean_object* v_cacheRef_4866_, lean_object* v_tree_4867_, lean_object* v_act_4868_, lean_object* v_c_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4862_, v_env_4863_, v_modName_4864_, v_d_4865_, v_cacheRef_4866_, v_tree_4867_, v_act_4868_, v_c_4869_);
lean_dec(v_cacheRef_4866_);
lean_dec(v_d_4865_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4872_, lean_object* v_cctx_4873_, lean_object* v_env_4874_, lean_object* v_modName_4875_, lean_object* v_d_4876_, lean_object* v_cacheRef_4877_, lean_object* v_tree_4878_, lean_object* v_act_4879_, lean_object* v_c_4880_){
_start:
{
lean_object* v___x_4882_; 
v___x_4882_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4873_, v_env_4874_, v_modName_4875_, v_d_4876_, v_cacheRef_4877_, v_tree_4878_, v_act_4879_, v_c_4880_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4883_, lean_object* v_cctx_4884_, lean_object* v_env_4885_, lean_object* v_modName_4886_, lean_object* v_d_4887_, lean_object* v_cacheRef_4888_, lean_object* v_tree_4889_, lean_object* v_act_4890_, lean_object* v_c_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4883_, v_cctx_4884_, v_env_4885_, v_modName_4886_, v_d_4887_, v_cacheRef_4888_, v_tree_4889_, v_act_4890_, v_c_4891_);
lean_dec(v_cacheRef_4888_);
lean_dec(v_d_4887_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4894_, lean_object* v_as_4895_, size_t v_i_4896_, size_t v_stop_4897_, lean_object* v_b_4898_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4895_, v_i_4896_, v_stop_4897_, v_b_4898_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4900_, lean_object* v_as_4901_, lean_object* v_i_4902_, lean_object* v_stop_4903_, lean_object* v_b_4904_){
_start:
{
size_t v_i_boxed_4905_; size_t v_stop_boxed_4906_; lean_object* v_res_4907_; 
v_i_boxed_4905_ = lean_unbox_usize(v_i_4902_);
lean_dec(v_i_4902_);
v_stop_boxed_4906_ = lean_unbox_usize(v_stop_4903_);
lean_dec(v_stop_4903_);
v_res_4907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4900_, v_as_4901_, v_i_boxed_4905_, v_stop_boxed_4906_, v_b_4904_);
lean_dec_ref(v_as_4901_);
return v_res_4907_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4908_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4909_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_4910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
lean_ctor_set(v___x_4910_, 1, v___x_4908_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4911_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4913_, lean_object* v_y_4914_){
_start:
{
lean_object* v_tree_4915_; lean_object* v_errors_4916_; lean_object* v_tree_4917_; lean_object* v_errors_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4927_; 
v_tree_4915_ = lean_ctor_get(v_x_4913_, 0);
lean_inc_ref(v_tree_4915_);
v_errors_4916_ = lean_ctor_get(v_x_4913_, 1);
lean_inc_ref(v_errors_4916_);
lean_dec_ref(v_x_4913_);
v_tree_4917_ = lean_ctor_get(v_y_4914_, 0);
v_errors_4918_ = lean_ctor_get(v_y_4914_, 1);
v_isSharedCheck_4927_ = !lean_is_exclusive(v_y_4914_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4920_ = v_y_4914_;
v_isShared_4921_ = v_isSharedCheck_4927_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_errors_4918_);
lean_inc(v_tree_4917_);
lean_dec(v_y_4914_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4927_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4925_; 
v___x_4922_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4915_, v_tree_4917_);
v___x_4923_ = l_Array_append___redArg(v_errors_4916_, v_errors_4918_);
lean_dec_ref(v_errors_4918_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v___x_4923_);
lean_ctor_set(v___x_4920_, 0, v___x_4922_);
v___x_4925_ = v___x_4920_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4922_);
lean_ctor_set(v_reuseFailAlloc_4926_, 1, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4928_, lean_object* v_x_4929_, lean_object* v_y_4930_){
_start:
{
lean_object* v___x_4931_; 
v___x_4931_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4929_, v_y_4930_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4933_){
_start:
{
lean_object* v___x_4934_; 
v___x_4934_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4935_, lean_object* v_tree_4936_){
_start:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4938_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4939_ = lean_st_ref_swap(v_d_4935_, v___x_4938_);
v___x_4940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4940_, 0, v_tree_4936_);
lean_ctor_set(v___x_4940_, 1, v___x_4939_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4941_, lean_object* v_tree_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4941_, v_tree_4942_);
lean_dec(v_d_4941_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4945_, lean_object* v_d_4946_, lean_object* v_tree_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4946_, v_tree_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4950_, lean_object* v_d_4951_, lean_object* v_tree_4952_, lean_object* v_a_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4950_, v_d_4951_, v_tree_4952_);
lean_dec(v_d_4951_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4955_, lean_object* v_env_4956_, lean_object* v_act_4957_, lean_object* v_d_4958_, lean_object* v_cacheRef_4959_, lean_object* v_tree_4960_, lean_object* v_mname_4961_, lean_object* v_mdata_4962_, lean_object* v_i_4963_){
_start:
{
lean_object* v_constants_4965_; lean_object* v___x_4966_; uint8_t v___x_4967_; 
v_constants_4965_ = lean_ctor_get(v_mdata_4962_, 2);
v___x_4966_ = lean_array_get_size(v_constants_4965_);
v___x_4967_ = lean_nat_dec_lt(v_i_4963_, v___x_4966_);
if (v___x_4967_ == 0)
{
lean_dec(v_i_4963_);
lean_dec(v_mname_4961_);
lean_dec_ref(v_act_4957_);
lean_dec_ref(v_env_4956_);
lean_dec_ref(v_cctx_4955_);
return v_tree_4960_;
}
else
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4968_ = lean_array_fget_borrowed(v_constants_4965_, v_i_4963_);
lean_inc(v___x_4968_);
v___x_4969_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4968_);
lean_inc_ref(v_act_4957_);
lean_inc(v_mname_4961_);
lean_inc_ref(v_env_4956_);
lean_inc_ref(v_cctx_4955_);
v___x_4970_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4955_, v_env_4956_, v_mname_4961_, v_d_4958_, v_cacheRef_4959_, v_tree_4960_, v_act_4957_, v___x_4969_);
v___x_4971_ = lean_unsigned_to_nat(1u);
v___x_4972_ = lean_nat_add(v_i_4963_, v___x_4971_);
lean_dec(v_i_4963_);
v_tree_4960_ = v___x_4970_;
v_i_4963_ = v___x_4972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4974_, lean_object* v_env_4975_, lean_object* v_act_4976_, lean_object* v_d_4977_, lean_object* v_cacheRef_4978_, lean_object* v_tree_4979_, lean_object* v_mname_4980_, lean_object* v_mdata_4981_, lean_object* v_i_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4974_, v_env_4975_, v_act_4976_, v_d_4977_, v_cacheRef_4978_, v_tree_4979_, v_mname_4980_, v_mdata_4981_, v_i_4982_);
lean_dec_ref(v_mdata_4981_);
lean_dec(v_cacheRef_4978_);
lean_dec(v_d_4977_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4985_, lean_object* v_cctx_4986_, lean_object* v_env_4987_, lean_object* v_act_4988_, lean_object* v_d_4989_, lean_object* v_cacheRef_4990_, lean_object* v_tree_4991_, lean_object* v_mname_4992_, lean_object* v_mdata_4993_, lean_object* v_i_4994_){
_start:
{
lean_object* v___x_4996_; 
v___x_4996_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4986_, v_env_4987_, v_act_4988_, v_d_4989_, v_cacheRef_4990_, v_tree_4991_, v_mname_4992_, v_mdata_4993_, v_i_4994_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4997_, lean_object* v_cctx_4998_, lean_object* v_env_4999_, lean_object* v_act_5000_, lean_object* v_d_5001_, lean_object* v_cacheRef_5002_, lean_object* v_tree_5003_, lean_object* v_mname_5004_, lean_object* v_mdata_5005_, lean_object* v_i_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4997_, v_cctx_4998_, v_env_4999_, v_act_5000_, v_d_5001_, v_cacheRef_5002_, v_tree_5003_, v_mname_5004_, v_mdata_5005_, v_i_5006_);
lean_dec_ref(v_mdata_5005_);
lean_dec(v_cacheRef_5002_);
lean_dec(v_d_5001_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_5009_, lean_object* v_env_5010_, lean_object* v_act_5011_, lean_object* v_d_5012_, lean_object* v_cacheRef_5013_, lean_object* v_tree_5014_, lean_object* v_start_5015_, lean_object* v_stop_5016_){
_start:
{
uint8_t v___x_5018_; 
v___x_5018_ = lean_nat_dec_lt(v_start_5015_, v_stop_5016_);
if (v___x_5018_ == 0)
{
lean_object* v___x_5019_; 
lean_dec(v_start_5015_);
lean_dec_ref(v_act_5011_);
lean_dec_ref(v_env_5010_);
lean_dec_ref(v_cctx_5009_);
v___x_5019_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_5012_, v_tree_5014_);
return v___x_5019_;
}
else
{
lean_object* v___x_5020_; lean_object* v_moduleData_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v_mname_5024_; lean_object* v___x_5025_; lean_object* v_mdata_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5020_ = l_Lean_Environment_header(v_env_5010_);
v_moduleData_5021_ = lean_ctor_get(v___x_5020_, 6);
lean_inc_ref(v_moduleData_5021_);
v___x_5022_ = lean_box(0);
v___x_5023_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5020_);
v_mname_5024_ = lean_array_get(v___x_5022_, v___x_5023_, v_start_5015_);
lean_dec_ref(v___x_5023_);
v___x_5025_ = l_Lean_instInhabitedModuleData_default;
v_mdata_5026_ = lean_array_get(v___x_5025_, v_moduleData_5021_, v_start_5015_);
lean_dec_ref(v_moduleData_5021_);
v___x_5027_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_5011_);
lean_inc_ref(v_env_5010_);
lean_inc_ref(v_cctx_5009_);
v___x_5028_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_5009_, v_env_5010_, v_act_5011_, v_d_5012_, v_cacheRef_5013_, v_tree_5014_, v_mname_5024_, v_mdata_5026_, v___x_5027_);
lean_dec(v_mdata_5026_);
v___x_5029_ = lean_unsigned_to_nat(1u);
v___x_5030_ = lean_nat_add(v_start_5015_, v___x_5029_);
lean_dec(v_start_5015_);
v_tree_5014_ = v___x_5028_;
v_start_5015_ = v___x_5030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_5032_, lean_object* v_env_5033_, lean_object* v_act_5034_, lean_object* v_d_5035_, lean_object* v_cacheRef_5036_, lean_object* v_tree_5037_, lean_object* v_start_5038_, lean_object* v_stop_5039_, lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5032_, v_env_5033_, v_act_5034_, v_d_5035_, v_cacheRef_5036_, v_tree_5037_, v_start_5038_, v_stop_5039_);
lean_dec(v_stop_5039_);
lean_dec(v_cacheRef_5036_);
lean_dec(v_d_5035_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_5042_, lean_object* v_cctx_5043_, lean_object* v_env_5044_, lean_object* v_act_5045_, lean_object* v_d_5046_, lean_object* v_cacheRef_5047_, lean_object* v_tree_5048_, lean_object* v_start_5049_, lean_object* v_stop_5050_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5043_, v_env_5044_, v_act_5045_, v_d_5046_, v_cacheRef_5047_, v_tree_5048_, v_start_5049_, v_stop_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5053_, lean_object* v_cctx_5054_, lean_object* v_env_5055_, lean_object* v_act_5056_, lean_object* v_d_5057_, lean_object* v_cacheRef_5058_, lean_object* v_tree_5059_, lean_object* v_start_5060_, lean_object* v_stop_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5053_, v_cctx_5054_, v_env_5055_, v_act_5056_, v_d_5057_, v_cacheRef_5058_, v_tree_5059_, v_start_5060_, v_stop_5061_);
lean_dec(v_stop_5061_);
lean_dec(v_cacheRef_5058_);
lean_dec(v_d_5057_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5064_, lean_object* v_ngen_5065_, lean_object* v_env_5066_, lean_object* v_act_5067_, lean_object* v_start_5068_, lean_object* v_stop_5069_){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5071_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5065_);
v___x_5072_ = lean_st_mk_ref(v___x_5071_);
v___x_5073_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5074_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_5075_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5064_, v_env_5066_, v_act_5067_, v___x_5073_, v___x_5072_, v___x_5074_, v_start_5068_, v_stop_5069_);
lean_dec(v___x_5072_);
lean_dec(v___x_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5076_, lean_object* v_ngen_5077_, lean_object* v_env_5078_, lean_object* v_act_5079_, lean_object* v_start_5080_, lean_object* v_stop_5081_, lean_object* v_a_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5076_, v_ngen_5077_, v_env_5078_, v_act_5079_, v_start_5080_, v_stop_5081_);
lean_dec(v_stop_5081_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5084_, lean_object* v_cctx_5085_, lean_object* v_ngen_5086_, lean_object* v_env_5087_, lean_object* v_act_5088_, lean_object* v_start_5089_, lean_object* v_stop_5090_){
_start:
{
lean_object* v___x_5092_; 
v___x_5092_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5085_, v_ngen_5086_, v_env_5087_, v_act_5088_, v_start_5089_, v_stop_5090_);
return v___x_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5093_, lean_object* v_cctx_5094_, lean_object* v_ngen_5095_, lean_object* v_env_5096_, lean_object* v_act_5097_, lean_object* v_start_5098_, lean_object* v_stop_5099_, lean_object* v_a_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5093_, v_cctx_5094_, v_ngen_5095_, v_env_5096_, v_act_5097_, v_start_5098_, v_stop_5099_);
lean_dec(v_stop_5099_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5102_, lean_object* v_x1_5103_, lean_object* v_x2_5104_){
_start:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = lean_task_get_own(v_x2_5104_);
v___x_5106_ = lean_apply_2(v_inst_5102_, v_x1_5103_, v___x_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5107_, lean_object* v_z_5108_, lean_object* v_tasks_5109_){
_start:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; uint8_t v___x_5113_; 
v___x_5110_ = lean_unsigned_to_nat(0u);
v___x_5111_ = lean_array_get_size(v_tasks_5109_);
v___x_5112_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5113_ = lean_nat_dec_lt(v___x_5110_, v___x_5111_);
if (v___x_5113_ == 0)
{
lean_dec_ref(v_tasks_5109_);
lean_dec(v_inst_5107_);
return v_z_5108_;
}
else
{
lean_object* v___f_5114_; uint8_t v___x_5115_; 
v___f_5114_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5114_, 0, v_inst_5107_);
v___x_5115_ = lean_nat_dec_le(v___x_5111_, v___x_5111_);
if (v___x_5115_ == 0)
{
if (v___x_5113_ == 0)
{
lean_dec_ref(v___f_5114_);
lean_dec_ref(v_tasks_5109_);
return v_z_5108_;
}
else
{
size_t v___x_5116_; size_t v___x_5117_; lean_object* v___x_5118_; 
v___x_5116_ = ((size_t)0ULL);
v___x_5117_ = lean_usize_of_nat(v___x_5111_);
v___x_5118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5112_, v___f_5114_, v_tasks_5109_, v___x_5116_, v___x_5117_, v_z_5108_);
return v___x_5118_;
}
}
else
{
size_t v___x_5119_; size_t v___x_5120_; lean_object* v___x_5121_; 
v___x_5119_ = ((size_t)0ULL);
v___x_5120_ = lean_usize_of_nat(v___x_5111_);
v___x_5121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5112_, v___f_5114_, v_tasks_5109_, v___x_5119_, v___x_5120_, v_z_5108_);
return v___x_5121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5122_, lean_object* v_inst_5123_, lean_object* v_z_5124_, lean_object* v_tasks_5125_){
_start:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5123_, v_z_5124_, v_tasks_5125_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5127_, lean_object* v___x_5128_, lean_object* v_____r_5129_){
_start:
{
lean_object* v___x_5130_; 
v___x_5130_ = lean_apply_2(v_toPure_5127_, lean_box(0), v___x_5128_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5131_, lean_object* v_setNGen_5132_, lean_object* v_toBind_5133_, lean_object* v_ngen_5134_){
_start:
{
lean_object* v_namePrefix_5135_; lean_object* v_idx_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5150_; 
v_namePrefix_5135_ = lean_ctor_get(v_ngen_5134_, 0);
v_idx_5136_ = lean_ctor_get(v_ngen_5134_, 1);
v_isSharedCheck_5150_ = !lean_is_exclusive(v_ngen_5134_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5138_ = v_ngen_5134_;
v_isShared_5139_ = v_isSharedCheck_5150_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_idx_5136_);
lean_inc(v_namePrefix_5135_);
lean_dec(v_ngen_5134_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5150_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5143_; 
lean_inc(v_idx_5136_);
lean_inc(v_namePrefix_5135_);
v___x_5140_ = l_Lean_Name_num___override(v_namePrefix_5135_, v_idx_5136_);
v___x_5141_ = lean_unsigned_to_nat(1u);
if (v_isShared_5139_ == 0)
{
lean_ctor_set(v___x_5138_, 1, v___x_5141_);
lean_ctor_set(v___x_5138_, 0, v___x_5140_);
v___x_5143_ = v___x_5138_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v___x_5140_);
lean_ctor_set(v_reuseFailAlloc_5149_, 1, v___x_5141_);
v___x_5143_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
lean_object* v___f_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___f_5144_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5144_, 0, v_toPure_5131_);
lean_closure_set(v___f_5144_, 1, v___x_5143_);
v___x_5145_ = lean_nat_add(v_idx_5136_, v___x_5141_);
lean_dec(v_idx_5136_);
v___x_5146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5146_, 0, v_namePrefix_5135_);
lean_ctor_set(v___x_5146_, 1, v___x_5145_);
v___x_5147_ = lean_apply_1(v_setNGen_5132_, v___x_5146_);
v___x_5148_ = lean_apply_4(v_toBind_5133_, lean_box(0), lean_box(0), v___x_5147_, v___f_5144_);
return v___x_5148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5151_, lean_object* v_inst_5152_){
_start:
{
lean_object* v_toApplicative_5153_; lean_object* v_toBind_5154_; lean_object* v_getNGen_5155_; lean_object* v_setNGen_5156_; lean_object* v_toPure_5157_; lean_object* v___f_5158_; lean_object* v___x_5159_; 
v_toApplicative_5153_ = lean_ctor_get(v_inst_5151_, 0);
lean_inc_ref(v_toApplicative_5153_);
v_toBind_5154_ = lean_ctor_get(v_inst_5151_, 1);
lean_inc_n(v_toBind_5154_, 2);
lean_dec_ref(v_inst_5151_);
v_getNGen_5155_ = lean_ctor_get(v_inst_5152_, 0);
lean_inc(v_getNGen_5155_);
v_setNGen_5156_ = lean_ctor_get(v_inst_5152_, 1);
lean_inc(v_setNGen_5156_);
lean_dec_ref(v_inst_5152_);
v_toPure_5157_ = lean_ctor_get(v_toApplicative_5153_, 1);
lean_inc(v_toPure_5157_);
lean_dec_ref(v_toApplicative_5153_);
v___f_5158_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5158_, 0, v_toPure_5157_);
lean_closure_set(v___f_5158_, 1, v_setNGen_5156_);
lean_closure_set(v___f_5158_, 2, v_toBind_5154_);
v___x_5159_ = lean_apply_4(v_toBind_5154_, lean_box(0), lean_box(0), v_getNGen_5155_, v___f_5158_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5160_, lean_object* v_inst_5161_, lean_object* v_inst_5162_){
_start:
{
lean_object* v___x_5163_; 
v___x_5163_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5161_, v_inst_5162_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5164_, lean_object* v_env_5165_, lean_object* v_modName_5166_, lean_object* v_d_5167_, lean_object* v_val_5168_, lean_object* v_act_5169_, lean_object* v_as_5170_, size_t v_sz_5171_, size_t v_i_5172_, lean_object* v_b_5173_){
_start:
{
uint8_t v___x_5175_; 
v___x_5175_ = lean_usize_dec_lt(v_i_5172_, v_sz_5171_);
if (v___x_5175_ == 0)
{
lean_dec_ref(v_act_5169_);
lean_dec(v_modName_5166_);
lean_dec_ref(v_env_5165_);
lean_dec_ref(v_cctx_5164_);
return v_b_5173_;
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5177_; size_t v___x_5178_; size_t v___x_5179_; 
v_a_5176_ = lean_array_uget_borrowed(v_as_5170_, v_i_5172_);
lean_inc(v_a_5176_);
lean_inc_ref(v_act_5169_);
lean_inc(v_modName_5166_);
lean_inc_ref(v_env_5165_);
lean_inc_ref(v_cctx_5164_);
v___x_5177_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5164_, v_env_5165_, v_modName_5166_, v_d_5167_, v_val_5168_, v_b_5173_, v_act_5169_, v_a_5176_);
v___x_5178_ = ((size_t)1ULL);
v___x_5179_ = lean_usize_add(v_i_5172_, v___x_5178_);
v_i_5172_ = v___x_5179_;
v_b_5173_ = v___x_5177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5181_, lean_object* v_env_5182_, lean_object* v_modName_5183_, lean_object* v_d_5184_, lean_object* v_val_5185_, lean_object* v_act_5186_, lean_object* v_as_5187_, lean_object* v_sz_5188_, lean_object* v_i_5189_, lean_object* v_b_5190_, lean_object* v___y_5191_){
_start:
{
size_t v_sz_boxed_5192_; size_t v_i_boxed_5193_; lean_object* v_res_5194_; 
v_sz_boxed_5192_ = lean_unbox_usize(v_sz_5188_);
lean_dec(v_sz_5188_);
v_i_boxed_5193_ = lean_unbox_usize(v_i_5189_);
lean_dec(v_i_5189_);
v_res_5194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5181_, v_env_5182_, v_modName_5183_, v_d_5184_, v_val_5185_, v_act_5186_, v_as_5187_, v_sz_boxed_5192_, v_i_boxed_5193_, v_b_5190_);
lean_dec_ref(v_as_5187_);
lean_dec(v_val_5185_);
lean_dec(v_d_5184_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5195_, lean_object* v_ngen_5196_, lean_object* v_env_5197_, lean_object* v_d_5198_, lean_object* v_act_5199_){
_start:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; uint8_t v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v_mainModule_5206_; lean_object* v___x_5207_; size_t v_sz_5208_; size_t v___x_5209_; lean_object* v___x_5210_; 
v___x_5201_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5196_);
v___x_5202_ = lean_st_mk_ref(v___x_5201_);
v___x_5203_ = 1;
v___x_5204_ = l_Lean_Environment_getLocalConstantInfos(v_env_5197_, v___x_5203_);
v___x_5205_ = l_Lean_Environment_header(v_env_5197_);
v_mainModule_5206_ = lean_ctor_get(v___x_5205_, 0);
lean_inc(v_mainModule_5206_);
lean_dec_ref(v___x_5205_);
v___x_5207_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v_sz_5208_ = lean_array_size(v___x_5204_);
v___x_5209_ = ((size_t)0ULL);
v___x_5210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5195_, v_env_5197_, v_mainModule_5206_, v_d_5198_, v___x_5202_, v_act_5199_, v___x_5204_, v_sz_5208_, v___x_5209_, v___x_5207_);
lean_dec_ref(v___x_5204_);
lean_dec(v___x_5202_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5211_, lean_object* v_ngen_5212_, lean_object* v_env_5213_, lean_object* v_d_5214_, lean_object* v_act_5215_, lean_object* v_a_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5211_, v_ngen_5212_, v_env_5213_, v_d_5214_, v_act_5215_);
lean_dec(v_d_5214_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5218_, lean_object* v_cctx_5219_, lean_object* v_ngen_5220_, lean_object* v_env_5221_, lean_object* v_d_5222_, lean_object* v_act_5223_){
_start:
{
lean_object* v___x_5225_; 
v___x_5225_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5219_, v_ngen_5220_, v_env_5221_, v_d_5222_, v_act_5223_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5226_, lean_object* v_cctx_5227_, lean_object* v_ngen_5228_, lean_object* v_env_5229_, lean_object* v_d_5230_, lean_object* v_act_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5226_, v_cctx_5227_, v_ngen_5228_, v_env_5229_, v_d_5230_, v_act_5231_);
lean_dec(v_d_5230_);
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5234_, lean_object* v_cctx_5235_, lean_object* v_env_5236_, lean_object* v_modName_5237_, lean_object* v_d_5238_, lean_object* v_val_5239_, lean_object* v_act_5240_, lean_object* v_as_5241_, size_t v_sz_5242_, size_t v_i_5243_, lean_object* v_b_5244_){
_start:
{
lean_object* v___x_5246_; 
v___x_5246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5235_, v_env_5236_, v_modName_5237_, v_d_5238_, v_val_5239_, v_act_5240_, v_as_5241_, v_sz_5242_, v_i_5243_, v_b_5244_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5247_, lean_object* v_cctx_5248_, lean_object* v_env_5249_, lean_object* v_modName_5250_, lean_object* v_d_5251_, lean_object* v_val_5252_, lean_object* v_act_5253_, lean_object* v_as_5254_, lean_object* v_sz_5255_, lean_object* v_i_5256_, lean_object* v_b_5257_, lean_object* v___y_5258_){
_start:
{
size_t v_sz_boxed_5259_; size_t v_i_boxed_5260_; lean_object* v_res_5261_; 
v_sz_boxed_5259_ = lean_unbox_usize(v_sz_5255_);
lean_dec(v_sz_5255_);
v_i_boxed_5260_ = lean_unbox_usize(v_i_5256_);
lean_dec(v_i_5256_);
v_res_5261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5247_, v_cctx_5248_, v_env_5249_, v_modName_5250_, v_d_5251_, v_val_5252_, v_act_5253_, v_as_5254_, v_sz_boxed_5259_, v_i_boxed_5260_, v_b_5257_);
lean_dec_ref(v_as_5254_);
lean_dec(v_val_5252_);
lean_dec(v_d_5251_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5262_, lean_object* v_x_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
if (lean_obj_tag(v_x_5263_) == 0)
{
lean_object* v___x_5269_; 
v___x_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5269_, 0, v_x_5262_);
return v___x_5269_;
}
else
{
lean_object* v_head_5270_; lean_object* v_tail_5271_; lean_object* v___x_5272_; 
v_head_5270_ = lean_ctor_get(v_x_5263_, 0);
lean_inc(v_head_5270_);
v_tail_5271_ = lean_ctor_get(v_x_5263_, 1);
lean_inc(v_tail_5271_);
lean_dec_ref_known(v_x_5263_, 2);
v___x_5272_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5262_, v_head_5270_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
if (lean_obj_tag(v___x_5272_) == 0)
{
lean_object* v_a_5273_; 
v_a_5273_ = lean_ctor_get(v___x_5272_, 0);
lean_inc(v_a_5273_);
lean_dec_ref_known(v___x_5272_, 1);
v_x_5262_ = v_a_5273_;
v_x_5263_ = v_tail_5271_;
goto _start;
}
else
{
lean_dec(v_tail_5271_);
return v___x_5272_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5275_, lean_object* v_x_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5275_, v_x_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5283_, lean_object* v_keys_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5283_, v_keys_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5291_, lean_object* v_keys_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5291_, v_keys_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_);
lean_dec(v_a_5296_);
lean_dec_ref(v_a_5295_);
lean_dec(v_a_5294_);
lean_dec_ref(v_a_5293_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5299_, lean_object* v_t_5300_, lean_object* v_keys_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_){
_start:
{
lean_object* v___x_5307_; 
v___x_5307_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5300_, v_keys_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5308_, lean_object* v_t_5309_, lean_object* v_keys_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5308_, v_t_5309_, v_keys_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_);
lean_dec(v_a_5314_);
lean_dec_ref(v_a_5313_);
lean_dec(v_a_5312_);
lean_dec_ref(v_a_5311_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5317_, lean_object* v_x_5318_, lean_object* v_x_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v___x_5325_; 
v___x_5325_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5318_, v_x_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5326_, lean_object* v_x_5327_, lean_object* v_x_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
lean_object* v_res_5334_; 
v_res_5334_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5326_, v_x_5327_, v_x_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
return v_res_5334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5335_, size_t v_sz_5336_, size_t v_i_5337_, lean_object* v_b_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
uint8_t v___x_5345_; 
v___x_5345_ = lean_usize_dec_lt(v_i_5337_, v_sz_5336_);
if (v___x_5345_ == 0)
{
lean_object* v___x_5346_; 
v___x_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5346_, 0, v_b_5338_);
return v___x_5346_;
}
else
{
lean_object* v_a_5347_; lean_object* v___x_5348_; 
v_a_5347_ = lean_array_uget_borrowed(v_as_5335_, v_i_5337_);
v___x_5348_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5347_, v_b_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5361_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5351_ = v___x_5348_;
v_isShared_5352_ = v_isSharedCheck_5361_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5348_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5361_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
if (lean_obj_tag(v_a_5349_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5355_; 
v_a_5353_ = lean_ctor_get(v_a_5349_, 0);
lean_inc(v_a_5353_);
lean_dec_ref_known(v_a_5349_, 1);
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 0, v_a_5353_);
v___x_5355_ = v___x_5351_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5353_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
else
{
lean_object* v_a_5357_; size_t v___x_5358_; size_t v___x_5359_; 
lean_del_object(v___x_5351_);
v_a_5357_ = lean_ctor_get(v_a_5349_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v_a_5349_, 1);
v___x_5358_ = ((size_t)1ULL);
v___x_5359_ = lean_usize_add(v_i_5337_, v___x_5358_);
v_i_5337_ = v___x_5359_;
v_b_5338_ = v_a_5357_;
goto _start;
}
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
v_a_5362_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5348_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5348_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_){
_start:
{
lean_object* v___x_5377_; uint8_t v___x_5378_; 
v___x_5377_ = lean_unsigned_to_nat(0u);
v___x_5378_ = lean_nat_dec_eq(v_next_5370_, v___x_5377_);
if (v___x_5378_ == 0)
{
lean_object* v___x_5379_; 
v___x_5379_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v_snd_5381_; lean_object* v_fst_5382_; lean_object* v_fst_5383_; lean_object* v_snd_5384_; lean_object* v___x_5385_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
lean_inc(v_a_5380_);
lean_dec_ref_known(v___x_5379_, 1);
v_snd_5381_ = lean_ctor_get(v_a_5380_, 1);
lean_inc(v_snd_5381_);
v_fst_5382_ = lean_ctor_get(v_a_5380_, 0);
lean_inc(v_fst_5382_);
lean_dec(v_a_5380_);
v_fst_5383_ = lean_ctor_get(v_snd_5381_, 0);
lean_inc(v_fst_5383_);
v_snd_5384_ = lean_ctor_get(v_snd_5381_, 1);
lean_inc(v_snd_5384_);
lean_dec(v_snd_5381_);
v___x_5385_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5383_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_);
if (lean_obj_tag(v___x_5385_) == 0)
{
lean_object* v_a_5386_; lean_object* v_buckets_5387_; lean_object* v___x_5388_; size_t v_sz_5389_; size_t v___x_5390_; lean_object* v___x_5391_; 
v_a_5386_ = lean_ctor_get(v___x_5385_, 0);
lean_inc(v_a_5386_);
lean_dec_ref_known(v___x_5385_, 1);
v_buckets_5387_ = lean_ctor_get(v_snd_5384_, 1);
v___x_5388_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5389_ = lean_array_size(v_buckets_5387_);
v___x_5390_ = ((size_t)0ULL);
v___x_5391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5387_, v_sz_5389_, v___x_5390_, v___x_5388_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5405_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5394_ = v___x_5391_;
v_isShared_5395_ = v_isSharedCheck_5405_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_a_5392_);
lean_dec(v___x_5391_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5405_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5403_; 
v___x_5396_ = lean_st_ref_take(v_a_5371_);
v___x_5397_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5388_);
lean_ctor_set(v___x_5397_, 1, v_fst_5383_);
lean_ctor_set(v___x_5397_, 2, v_snd_5384_);
lean_ctor_set(v___x_5397_, 3, v___x_5388_);
v___x_5398_ = lean_array_set(v___x_5396_, v_next_5370_, v___x_5397_);
v___x_5399_ = lean_st_ref_set(v_a_5371_, v___x_5398_);
v___x_5400_ = l_Array_append___redArg(v_fst_5382_, v_a_5386_);
lean_dec(v_a_5386_);
v___x_5401_ = l_Array_append___redArg(v___x_5400_, v_a_5392_);
lean_dec(v_a_5392_);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 0, v___x_5401_);
v___x_5403_ = v___x_5394_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v___x_5401_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
else
{
lean_dec(v_a_5386_);
lean_dec(v_snd_5384_);
lean_dec(v_fst_5383_);
lean_dec(v_fst_5382_);
return v___x_5391_;
}
}
else
{
lean_dec(v_snd_5384_);
lean_dec(v_fst_5383_);
lean_dec(v_fst_5382_);
return v___x_5385_;
}
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5413_; 
v_a_5406_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5413_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5413_ == 0)
{
v___x_5408_ = v___x_5379_;
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_a_5406_);
lean_dec(v___x_5379_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5413_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v___x_5411_; 
if (v_isShared_5409_ == 0)
{
v___x_5411_ = v___x_5408_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5406_);
v___x_5411_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
return v___x_5411_;
}
}
}
}
else
{
lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5414_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5415_, 0, v___x_5414_);
return v___x_5415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
if (lean_obj_tag(v_a_5416_) == 0)
{
lean_object* v___x_5424_; lean_object* v___x_5425_; 
v___x_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5424_, 0, v_a_5417_);
v___x_5425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5425_, 0, v___x_5424_);
return v___x_5425_;
}
else
{
lean_object* v_value_5426_; lean_object* v_tail_5427_; lean_object* v___x_5428_; 
v_value_5426_ = lean_ctor_get(v_a_5416_, 1);
v_tail_5427_ = lean_ctor_get(v_a_5416_, 2);
v___x_5428_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5426_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5430_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5429_);
lean_dec_ref_known(v___x_5428_, 1);
v___x_5430_ = l_Array_append___redArg(v_a_5417_, v_a_5429_);
lean_dec(v_a_5429_);
v_a_5416_ = v_tail_5427_;
v_a_5417_ = v___x_5430_;
goto _start;
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
lean_dec_ref(v_a_5417_);
v_a_5432_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5428_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5428_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5440_, v_a_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec(v_a_5440_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5449_, lean_object* v_sz_5450_, lean_object* v_i_5451_, lean_object* v_b_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
size_t v_sz_boxed_5459_; size_t v_i_boxed_5460_; lean_object* v_res_5461_; 
v_sz_boxed_5459_ = lean_unbox_usize(v_sz_5450_);
lean_dec(v_sz_5450_);
v_i_boxed_5460_ = lean_unbox_usize(v_i_5451_);
lean_dec(v_i_5451_);
v_res_5461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5449_, v_sz_boxed_5459_, v_i_boxed_5460_, v_b_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5453_);
lean_dec_ref(v_as_5449_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
lean_dec(v_a_5467_);
lean_dec_ref(v_a_5466_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec(v_next_5462_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5470_, lean_object* v_next_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_){
_start:
{
lean_object* v___x_5478_; 
v___x_5478_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5479_, lean_object* v_next_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5479_, v_next_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
lean_dec(v_a_5483_);
lean_dec_ref(v_a_5482_);
lean_dec(v_a_5481_);
lean_dec(v_next_5480_);
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_){
_start:
{
lean_object* v___x_5497_; 
v___x_5497_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5489_, v_a_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_);
return v___x_5497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_){
_start:
{
lean_object* v_res_5507_; 
v_res_5507_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5498_, v_a_5499_, v_a_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
lean_dec(v___y_5505_);
lean_dec_ref(v___y_5504_);
lean_dec(v___y_5503_);
lean_dec_ref(v___y_5502_);
lean_dec(v___y_5501_);
lean_dec(v_a_5499_);
return v_res_5507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5508_, lean_object* v_as_5509_, size_t v_sz_5510_, size_t v_i_5511_, lean_object* v_b_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_){
_start:
{
lean_object* v___x_5519_; 
v___x_5519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5509_, v_sz_5510_, v_i_5511_, v_b_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_);
return v___x_5519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5520_, lean_object* v_as_5521_, lean_object* v_sz_5522_, lean_object* v_i_5523_, lean_object* v_b_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_){
_start:
{
size_t v_sz_boxed_5531_; size_t v_i_boxed_5532_; lean_object* v_res_5533_; 
v_sz_boxed_5531_ = lean_unbox_usize(v_sz_5522_);
lean_dec(v_sz_5522_);
v_i_boxed_5532_ = lean_unbox_usize(v_i_5523_);
lean_dec(v_i_5523_);
v_res_5533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5520_, v_as_5521_, v_sz_boxed_5531_, v_i_boxed_5532_, v_b_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_);
lean_dec(v___y_5529_);
lean_dec_ref(v___y_5528_);
lean_dec(v___y_5527_);
lean_dec_ref(v___y_5526_);
lean_dec(v___y_5525_);
lean_dec_ref(v_as_5521_);
return v_res_5533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5534_, lean_object* v_rest_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_){
_start:
{
lean_object* v___x_5542_; uint8_t v___x_5543_; 
v___x_5542_ = lean_unsigned_to_nat(0u);
v___x_5543_ = lean_nat_dec_eq(v_next_5534_, v___x_5542_);
if (v___x_5543_ == 0)
{
lean_object* v___x_5544_; 
v___x_5544_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5534_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_, v_a_5540_);
if (lean_obj_tag(v___x_5544_) == 0)
{
lean_object* v_a_5545_; lean_object* v_snd_5546_; 
v_a_5545_ = lean_ctor_get(v___x_5544_, 0);
lean_inc(v_a_5545_);
lean_dec_ref_known(v___x_5544_, 1);
v_snd_5546_ = lean_ctor_get(v_a_5545_, 1);
lean_inc(v_snd_5546_);
lean_dec(v_a_5545_);
if (lean_obj_tag(v_rest_5535_) == 0)
{
lean_object* v___x_5547_; 
lean_dec(v_snd_5546_);
v___x_5547_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5534_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_, v_a_5540_);
lean_dec(v_next_5534_);
return v___x_5547_;
}
else
{
lean_object* v_fst_5548_; lean_object* v_snd_5549_; lean_object* v_head_5550_; lean_object* v_tail_5551_; lean_object* v___x_5552_; uint8_t v___x_5553_; 
lean_dec(v_next_5534_);
v_fst_5548_ = lean_ctor_get(v_snd_5546_, 0);
lean_inc(v_fst_5548_);
v_snd_5549_ = lean_ctor_get(v_snd_5546_, 1);
lean_inc(v_snd_5549_);
lean_dec(v_snd_5546_);
v_head_5550_ = lean_ctor_get(v_rest_5535_, 0);
v_tail_5551_ = lean_ctor_get(v_rest_5535_, 1);
v___x_5552_ = lean_box(3);
v___x_5553_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5550_, v___x_5552_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; 
lean_dec(v_fst_5548_);
v___x_5554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5549_, v_head_5550_, v___x_5542_);
lean_dec(v_snd_5549_);
v_next_5534_ = v___x_5554_;
v_rest_5535_ = v_tail_5551_;
goto _start;
}
else
{
lean_dec(v_snd_5549_);
v_next_5534_ = v_fst_5548_;
v_rest_5535_ = v_tail_5551_;
goto _start;
}
}
}
else
{
lean_object* v_a_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5564_; 
lean_dec(v_next_5534_);
v_a_5557_ = lean_ctor_get(v___x_5544_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5559_ = v___x_5544_;
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_a_5557_);
lean_dec(v___x_5544_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5562_; 
if (v_isShared_5560_ == 0)
{
v___x_5562_ = v___x_5559_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5557_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
else
{
lean_object* v___x_5565_; lean_object* v___x_5566_; 
lean_dec(v_next_5534_);
v___x_5565_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5565_);
return v___x_5566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5567_, lean_object* v_rest_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_){
_start:
{
lean_object* v_res_5575_; 
v_res_5575_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5567_, v_rest_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_);
lean_dec(v_a_5573_);
lean_dec_ref(v_a_5572_);
lean_dec(v_a_5571_);
lean_dec_ref(v_a_5570_);
lean_dec(v_a_5569_);
lean_dec(v_rest_5568_);
return v_res_5575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5576_, lean_object* v_next_5577_, lean_object* v_rest_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_){
_start:
{
lean_object* v___x_5585_; 
v___x_5585_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5577_, v_rest_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
return v___x_5585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5586_, lean_object* v_next_5587_, lean_object* v_rest_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5586_, v_next_5587_, v_rest_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_);
lean_dec(v_a_5593_);
lean_dec_ref(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
lean_dec(v_rest_5588_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5596_, lean_object* v_path_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_){
_start:
{
if (lean_obj_tag(v_path_5597_) == 0)
{
lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5603_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
lean_ctor_set(v___x_5604_, 1, v_t_5596_);
v___x_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
return v___x_5605_;
}
else
{
lean_object* v_head_5606_; lean_object* v_tail_5607_; lean_object* v_roots_5608_; lean_object* v___x_5609_; lean_object* v_idx_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; 
v_head_5606_ = lean_ctor_get(v_path_5597_, 0);
lean_inc(v_head_5606_);
v_tail_5607_ = lean_ctor_get(v_path_5597_, 1);
lean_inc(v_tail_5607_);
lean_dec_ref_known(v_path_5597_, 2);
v_roots_5608_ = lean_ctor_get(v_t_5596_, 1);
v___x_5609_ = lean_unsigned_to_nat(0u);
v_idx_5610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5608_, v_head_5606_, v___x_5609_);
lean_dec(v_head_5606_);
v___x_5611_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5611_, 0, lean_box(0));
lean_closure_set(v___x_5611_, 1, v_idx_5610_);
lean_closure_set(v___x_5611_, 2, v_tail_5607_);
v___x_5612_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5596_, v___x_5611_, v_a_5598_, v_a_5599_, v_a_5600_, v_a_5601_);
return v___x_5612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5613_, lean_object* v_path_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_){
_start:
{
lean_object* v_res_5620_; 
v_res_5620_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5613_, v_path_5614_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_);
lean_dec(v_a_5618_);
lean_dec_ref(v_a_5617_);
lean_dec(v_a_5616_);
lean_dec_ref(v_a_5615_);
return v_res_5620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5621_, lean_object* v_t_5622_, lean_object* v_path_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_){
_start:
{
lean_object* v___x_5629_; 
v___x_5629_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5622_, v_path_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_);
return v___x_5629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5630_, lean_object* v_t_5631_, lean_object* v_path_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5630_, v_t_5631_, v_path_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_);
lean_dec(v_a_5636_);
lean_dec_ref(v_a_5635_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
return v_res_5638_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5639_, lean_object* v_b_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
if (lean_obj_tag(v_as_x27_5639_) == 0)
{
lean_object* v___x_5646_; 
v___x_5646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5646_, 0, v_b_5640_);
return v___x_5646_;
}
else
{
lean_object* v_head_5647_; lean_object* v_tail_5648_; lean_object* v_fst_5649_; lean_object* v_snd_5650_; lean_object* v___x_5651_; 
v_head_5647_ = lean_ctor_get(v_as_x27_5639_, 0);
v_tail_5648_ = lean_ctor_get(v_as_x27_5639_, 1);
v_fst_5649_ = lean_ctor_get(v_b_5640_, 0);
lean_inc(v_fst_5649_);
v_snd_5650_ = lean_ctor_get(v_b_5640_, 1);
lean_inc(v_snd_5650_);
lean_dec_ref(v_b_5640_);
lean_inc(v_head_5647_);
v___x_5651_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5650_, v_head_5647_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v_a_5652_; lean_object* v_fst_5653_; lean_object* v_snd_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5663_; 
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5652_);
lean_dec_ref_known(v___x_5651_, 1);
v_fst_5653_ = lean_ctor_get(v_a_5652_, 0);
v_snd_5654_ = lean_ctor_get(v_a_5652_, 1);
v_isSharedCheck_5663_ = !lean_is_exclusive(v_a_5652_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5656_ = v_a_5652_;
v_isShared_5657_ = v_isSharedCheck_5663_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_snd_5654_);
lean_inc(v_fst_5653_);
lean_dec(v_a_5652_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5663_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5658_; lean_object* v___x_5660_; 
v___x_5658_ = l_Array_append___redArg(v_fst_5649_, v_fst_5653_);
lean_dec(v_fst_5653_);
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 0, v___x_5658_);
v___x_5660_ = v___x_5656_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5658_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_snd_5654_);
v___x_5660_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
v_as_x27_5639_ = v_tail_5648_;
v_b_5640_ = v___x_5660_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5649_);
return v___x_5651_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5664_, lean_object* v_b_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_){
_start:
{
lean_object* v_res_5671_; 
v_res_5671_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5664_, v_b_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_);
lean_dec(v___y_5669_);
lean_dec_ref(v___y_5668_);
lean_dec(v___y_5667_);
lean_dec_ref(v___y_5666_);
lean_dec(v_as_x27_5664_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5672_, lean_object* v_keys_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_){
_start:
{
lean_object* v_allExtracted_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; 
v_allExtracted_5679_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5680_, 0, v_allExtracted_5679_);
lean_ctor_set(v___x_5680_, 1, v_t_5672_);
v___x_5681_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5673_, v___x_5680_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
if (lean_obj_tag(v___x_5681_) == 0)
{
lean_object* v_a_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5698_; 
v_a_5682_ = lean_ctor_get(v___x_5681_, 0);
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5681_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5684_ = v___x_5681_;
v_isShared_5685_ = v_isSharedCheck_5698_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_a_5682_);
lean_dec(v___x_5681_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5698_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v_fst_5686_; lean_object* v_snd_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5697_; 
v_fst_5686_ = lean_ctor_get(v_a_5682_, 0);
v_snd_5687_ = lean_ctor_get(v_a_5682_, 1);
v_isSharedCheck_5697_ = !lean_is_exclusive(v_a_5682_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5689_ = v_a_5682_;
v_isShared_5690_ = v_isSharedCheck_5697_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_snd_5687_);
lean_inc(v_fst_5686_);
lean_dec(v_a_5682_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5697_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5692_; 
if (v_isShared_5690_ == 0)
{
v___x_5692_ = v___x_5689_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_fst_5686_);
lean_ctor_set(v_reuseFailAlloc_5696_, 1, v_snd_5687_);
v___x_5692_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
lean_object* v___x_5694_; 
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 0, v___x_5692_);
v___x_5694_ = v___x_5684_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5692_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
}
else
{
return v___x_5681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5699_, lean_object* v_keys_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_){
_start:
{
lean_object* v_res_5706_; 
v_res_5706_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5699_, v_keys_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_);
lean_dec(v_a_5704_);
lean_dec_ref(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec_ref(v_a_5701_);
lean_dec(v_keys_5700_);
return v_res_5706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5707_, lean_object* v_t_5708_, lean_object* v_keys_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_){
_start:
{
lean_object* v___x_5715_; 
v___x_5715_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5708_, v_keys_5709_, v_a_5710_, v_a_5711_, v_a_5712_, v_a_5713_);
return v___x_5715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5716_, lean_object* v_t_5717_, lean_object* v_keys_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_){
_start:
{
lean_object* v_res_5724_; 
v_res_5724_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5716_, v_t_5717_, v_keys_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_);
lean_dec(v_a_5722_);
lean_dec_ref(v_a_5721_);
lean_dec(v_a_5720_);
lean_dec_ref(v_a_5719_);
lean_dec(v_keys_5718_);
return v_res_5724_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5725_, lean_object* v_as_5726_, lean_object* v_as_x27_5727_, lean_object* v_b_5728_, lean_object* v_a_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_){
_start:
{
lean_object* v___x_5735_; 
v___x_5735_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5727_, v_b_5728_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
return v___x_5735_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5736_, lean_object* v_as_5737_, lean_object* v_as_x27_5738_, lean_object* v_b_5739_, lean_object* v_a_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5736_, v_as_5737_, v_as_x27_5738_, v_b_5739_, v_a_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_);
lean_dec(v___y_5744_);
lean_dec_ref(v___y_5743_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v_as_x27_5738_);
lean_dec(v_as_5737_);
return v_res_5746_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5748_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5749_ = l_Lean_stringToMessageData(v___x_5748_);
return v___x_5749_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5751_; lean_object* v___x_5752_; 
v___x_5751_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5752_ = l_Lean_stringToMessageData(v___x_5751_);
return v___x_5752_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5754_; lean_object* v___x_5755_; 
v___x_5754_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5755_ = l_Lean_stringToMessageData(v___x_5754_);
return v___x_5755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5756_, lean_object* v_inst_5757_, lean_object* v_inst_5758_, lean_object* v_inst_5759_, lean_object* v_f_5760_){
_start:
{
lean_object* v_module_5761_; lean_object* v_const_5762_; lean_object* v_exception_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5775_; 
v_module_5761_ = lean_ctor_get(v_f_5760_, 0);
lean_inc(v_module_5761_);
v_const_5762_ = lean_ctor_get(v_f_5760_, 1);
lean_inc(v_const_5762_);
v_exception_5763_ = lean_ctor_get(v_f_5760_, 2);
lean_inc_ref(v_exception_5763_);
lean_dec_ref(v_f_5760_);
v___x_5764_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5765_ = l_Lean_MessageData_ofName(v_const_5762_);
v___x_5766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5764_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5768_, 0, v___x_5766_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = l_Lean_MessageData_ofName(v_module_5761_);
v___x_5770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5770_, 0, v___x_5768_);
lean_ctor_set(v___x_5770_, 1, v___x_5769_);
v___x_5771_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5770_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = l_Lean_Exception_toMessageData(v_exception_5763_);
v___x_5774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5774_, 0, v___x_5772_);
lean_ctor_set(v___x_5774_, 1, v___x_5773_);
v___x_5775_ = l_Lean_logError___redArg(v_inst_5756_, v_inst_5757_, v_inst_5758_, v_inst_5759_, v___x_5774_);
return v___x_5775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5776_, lean_object* v_inst_5777_, lean_object* v_inst_5778_, lean_object* v_inst_5779_, lean_object* v_inst_5780_, lean_object* v_f_5781_){
_start:
{
lean_object* v___x_5782_; 
v___x_5782_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5777_, v_inst_5778_, v_inst_5779_, v_inst_5780_, v_f_5781_);
return v___x_5782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_toApplicative_5783_, lean_object* v_tasks_5784_, lean_object* v_t_5785_){
_start:
{
lean_object* v_toPure_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; 
v_toPure_5786_ = lean_ctor_get(v_toApplicative_5783_, 1);
lean_inc(v_toPure_5786_);
lean_dec_ref(v_toApplicative_5783_);
v___x_5787_ = lean_array_push(v_tasks_5784_, v_t_5785_);
v___x_5788_ = lean_apply_2(v_toPure_5786_, lean_box(0), v___x_5787_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5789_, lean_object* v_inst_5790_, lean_object* v_cctx_5791_, lean_object* v_env_5792_, lean_object* v_act_5793_, lean_object* v_constantsPerTask_5794_, lean_object* v_n_5795_, lean_object* v_ngen_5796_, lean_object* v_tasks_5797_, lean_object* v_start_5798_, lean_object* v_cnt_5799_, lean_object* v_idx_5800_){
_start:
{
lean_object* v___x_5801_; lean_object* v_moduleData_5802_; lean_object* v___x_5803_; uint8_t v___x_5804_; 
v___x_5801_ = l_Lean_Environment_header(v_env_5792_);
v_moduleData_5802_ = lean_ctor_get(v___x_5801_, 6);
lean_inc_ref(v_moduleData_5802_);
lean_dec_ref(v___x_5801_);
v___x_5803_ = lean_array_get_size(v_moduleData_5802_);
v___x_5804_ = lean_nat_dec_lt(v_idx_5800_, v___x_5803_);
if (v___x_5804_ == 0)
{
uint8_t v___x_5805_; 
lean_dec_ref(v_moduleData_5802_);
lean_dec(v_idx_5800_);
lean_dec(v_cnt_5799_);
lean_dec(v_constantsPerTask_5794_);
v___x_5805_ = lean_nat_dec_lt(v_start_5798_, v_n_5795_);
if (v___x_5805_ == 0)
{
lean_object* v_toApplicative_5806_; lean_object* v_toPure_5807_; lean_object* v___x_5808_; 
lean_dec(v_start_5798_);
lean_dec_ref(v_ngen_5796_);
lean_dec(v_n_5795_);
lean_dec_ref(v_act_5793_);
lean_dec_ref(v_env_5792_);
lean_dec_ref(v_cctx_5791_);
lean_dec(v_inst_5790_);
v_toApplicative_5806_ = lean_ctor_get(v_inst_5789_, 0);
lean_inc_ref(v_toApplicative_5806_);
lean_dec_ref(v_inst_5789_);
v_toPure_5807_ = lean_ctor_get(v_toApplicative_5806_, 1);
lean_inc(v_toPure_5807_);
lean_dec_ref(v_toApplicative_5806_);
v___x_5808_ = lean_apply_2(v_toPure_5807_, lean_box(0), v_tasks_5797_);
return v___x_5808_;
}
else
{
lean_object* v_namePrefix_5809_; lean_object* v_idx_5810_; lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5827_; 
v_namePrefix_5809_ = lean_ctor_get(v_ngen_5796_, 0);
v_idx_5810_ = lean_ctor_get(v_ngen_5796_, 1);
v_isSharedCheck_5827_ = !lean_is_exclusive(v_ngen_5796_);
if (v_isSharedCheck_5827_ == 0)
{
v___x_5812_ = v_ngen_5796_;
v_isShared_5813_ = v_isSharedCheck_5827_;
goto v_resetjp_5811_;
}
else
{
lean_inc(v_idx_5810_);
lean_inc(v_namePrefix_5809_);
lean_dec(v_ngen_5796_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5827_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v_toApplicative_5814_; lean_object* v_toBind_5815_; lean_object* v___f_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5820_; 
v_toApplicative_5814_ = lean_ctor_get(v_inst_5789_, 0);
lean_inc_ref(v_toApplicative_5814_);
v_toBind_5815_ = lean_ctor_get(v_inst_5789_, 1);
lean_inc(v_toBind_5815_);
lean_dec_ref(v_inst_5789_);
v___f_5816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5816_, 0, v_toApplicative_5814_);
lean_closure_set(v___f_5816_, 1, v_tasks_5797_);
v___x_5817_ = l_Lean_Name_num___override(v_namePrefix_5809_, v_idx_5810_);
v___x_5818_ = lean_unsigned_to_nat(1u);
if (v_isShared_5813_ == 0)
{
lean_ctor_set(v___x_5812_, 1, v___x_5818_);
lean_ctor_set(v___x_5812_, 0, v___x_5817_);
v___x_5820_ = v___x_5812_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v___x_5817_);
lean_ctor_set(v_reuseFailAlloc_5826_, 1, v___x_5818_);
v___x_5820_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5821_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5821_, 0, lean_box(0));
lean_closure_set(v___x_5821_, 1, v_cctx_5791_);
lean_closure_set(v___x_5821_, 2, v___x_5820_);
lean_closure_set(v___x_5821_, 3, v_env_5792_);
lean_closure_set(v___x_5821_, 4, v_act_5793_);
lean_closure_set(v___x_5821_, 5, v_start_5798_);
lean_closure_set(v___x_5821_, 6, v_n_5795_);
v___x_5822_ = lean_unsigned_to_nat(0u);
v___x_5823_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5823_, 0, lean_box(0));
lean_closure_set(v___x_5823_, 1, v___x_5821_);
lean_closure_set(v___x_5823_, 2, v___x_5822_);
v___x_5824_ = lean_apply_2(v_inst_5790_, lean_box(0), v___x_5823_);
v___x_5825_ = lean_apply_4(v_toBind_5815_, lean_box(0), lean_box(0), v___x_5824_, v___f_5816_);
return v___x_5825_;
}
}
}
}
else
{
lean_object* v_mdata_5828_; lean_object* v_constants_5829_; lean_object* v___x_5830_; lean_object* v_cnt_5831_; uint8_t v___x_5832_; 
v_mdata_5828_ = lean_array_fget(v_moduleData_5802_, v_idx_5800_);
lean_dec_ref(v_moduleData_5802_);
v_constants_5829_ = lean_ctor_get(v_mdata_5828_, 2);
lean_inc_ref(v_constants_5829_);
lean_dec(v_mdata_5828_);
v___x_5830_ = lean_array_get_size(v_constants_5829_);
lean_dec_ref(v_constants_5829_);
v_cnt_5831_ = lean_nat_add(v_cnt_5799_, v___x_5830_);
lean_dec(v_cnt_5799_);
v___x_5832_ = lean_nat_dec_lt(v_constantsPerTask_5794_, v_cnt_5831_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5833_ = lean_unsigned_to_nat(1u);
v___x_5834_ = lean_nat_add(v_idx_5800_, v___x_5833_);
lean_dec(v_idx_5800_);
v_cnt_5799_ = v_cnt_5831_;
v_idx_5800_ = v___x_5834_;
goto _start;
}
else
{
lean_object* v_namePrefix_5836_; lean_object* v_idx_5837_; lean_object* v___x_5839_; uint8_t v_isShared_5840_; uint8_t v_isSharedCheck_5856_; 
lean_dec(v_cnt_5831_);
v_namePrefix_5836_ = lean_ctor_get(v_ngen_5796_, 0);
v_idx_5837_ = lean_ctor_get(v_ngen_5796_, 1);
v_isSharedCheck_5856_ = !lean_is_exclusive(v_ngen_5796_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5839_ = v_ngen_5796_;
v_isShared_5840_ = v_isSharedCheck_5856_;
goto v_resetjp_5838_;
}
else
{
lean_inc(v_idx_5837_);
lean_inc(v_namePrefix_5836_);
lean_dec(v_ngen_5796_);
v___x_5839_ = lean_box(0);
v_isShared_5840_ = v_isSharedCheck_5856_;
goto v_resetjp_5838_;
}
v_resetjp_5838_:
{
lean_object* v_toBind_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5845_; 
v_toBind_5841_ = lean_ctor_get(v_inst_5789_, 1);
lean_inc(v_toBind_5841_);
lean_inc(v_idx_5837_);
lean_inc(v_namePrefix_5836_);
v___x_5842_ = l_Lean_Name_num___override(v_namePrefix_5836_, v_idx_5837_);
v___x_5843_ = lean_unsigned_to_nat(1u);
if (v_isShared_5840_ == 0)
{
lean_ctor_set(v___x_5839_, 1, v___x_5843_);
lean_ctor_set(v___x_5839_, 0, v___x_5842_);
v___x_5845_ = v___x_5839_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5842_);
lean_ctor_set(v_reuseFailAlloc_5855_, 1, v___x_5843_);
v___x_5845_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___f_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5846_ = lean_nat_add(v_idx_5837_, v___x_5843_);
lean_dec(v_idx_5837_);
v___x_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5847_, 0, v_namePrefix_5836_);
lean_ctor_set(v___x_5847_, 1, v___x_5846_);
v___x_5848_ = lean_nat_add(v_idx_5800_, v___x_5843_);
lean_dec(v_idx_5800_);
lean_inc(v___x_5848_);
lean_inc_ref(v_act_5793_);
lean_inc_ref(v_env_5792_);
lean_inc_ref(v_cctx_5791_);
lean_inc(v_inst_5790_);
v___f_5849_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5849_, 0, v_tasks_5797_);
lean_closure_set(v___f_5849_, 1, v_inst_5789_);
lean_closure_set(v___f_5849_, 2, v_inst_5790_);
lean_closure_set(v___f_5849_, 3, v_cctx_5791_);
lean_closure_set(v___f_5849_, 4, v_env_5792_);
lean_closure_set(v___f_5849_, 5, v_act_5793_);
lean_closure_set(v___f_5849_, 6, v_constantsPerTask_5794_);
lean_closure_set(v___f_5849_, 7, v_n_5795_);
lean_closure_set(v___f_5849_, 8, v___x_5847_);
lean_closure_set(v___f_5849_, 9, v___x_5848_);
v___x_5850_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5850_, 0, lean_box(0));
lean_closure_set(v___x_5850_, 1, v_cctx_5791_);
lean_closure_set(v___x_5850_, 2, v___x_5845_);
lean_closure_set(v___x_5850_, 3, v_env_5792_);
lean_closure_set(v___x_5850_, 4, v_act_5793_);
lean_closure_set(v___x_5850_, 5, v_start_5798_);
lean_closure_set(v___x_5850_, 6, v___x_5848_);
v___x_5851_ = lean_unsigned_to_nat(0u);
v___x_5852_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5852_, 0, lean_box(0));
lean_closure_set(v___x_5852_, 1, v___x_5850_);
lean_closure_set(v___x_5852_, 2, v___x_5851_);
v___x_5853_ = lean_apply_2(v_inst_5790_, lean_box(0), v___x_5852_);
v___x_5854_ = lean_apply_4(v_toBind_5841_, lean_box(0), lean_box(0), v___x_5853_, v___f_5849_);
return v___x_5854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5857_, lean_object* v_inst_5858_, lean_object* v_inst_5859_, lean_object* v_cctx_5860_, lean_object* v_env_5861_, lean_object* v_act_5862_, lean_object* v_constantsPerTask_5863_, lean_object* v_n_5864_, lean_object* v___x_5865_, lean_object* v___x_5866_, lean_object* v_t_5867_){
_start:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5868_ = lean_array_push(v_tasks_5857_, v_t_5867_);
v___x_5869_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5866_);
v___x_5870_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5858_, v_inst_5859_, v_cctx_5860_, v_env_5861_, v_act_5862_, v_constantsPerTask_5863_, v_n_5864_, v___x_5865_, v___x_5868_, v___x_5866_, v___x_5869_, v___x_5866_);
return v___x_5870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5871_, lean_object* v_00_u03b1_5872_, lean_object* v_inst_5873_, lean_object* v_inst_5874_, lean_object* v_cctx_5875_, lean_object* v_env_5876_, lean_object* v_act_5877_, lean_object* v_constantsPerTask_5878_, lean_object* v_n_5879_, lean_object* v_ngen_5880_, lean_object* v_tasks_5881_, lean_object* v_start_5882_, lean_object* v_cnt_5883_, lean_object* v_idx_5884_){
_start:
{
lean_object* v___x_5885_; 
v___x_5885_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5873_, v_inst_5874_, v_cctx_5875_, v_env_5876_, v_act_5877_, v_constantsPerTask_5878_, v_n_5879_, v_ngen_5880_, v_tasks_5881_, v_start_5882_, v_cnt_5883_, v_idx_5884_);
return v___x_5885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5886_, lean_object* v_h__1_5887_){
_start:
{
lean_object* v_fst_5888_; lean_object* v_snd_5889_; lean_object* v___x_5890_; 
v_fst_5888_ = lean_ctor_get(v_x_5886_, 0);
lean_inc(v_fst_5888_);
v_snd_5889_ = lean_ctor_get(v_x_5886_, 1);
lean_inc(v_snd_5889_);
lean_dec_ref(v_x_5886_);
v___x_5890_ = lean_apply_2(v_h__1_5887_, v_fst_5888_, v_snd_5889_);
return v___x_5890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5891_, lean_object* v_x_5892_, lean_object* v_h__1_5893_){
_start:
{
lean_object* v_fst_5894_; lean_object* v_snd_5895_; lean_object* v___x_5896_; 
v_fst_5894_ = lean_ctor_get(v_x_5892_, 0);
lean_inc(v_fst_5894_);
v_snd_5895_ = lean_ctor_get(v_x_5892_, 1);
lean_inc(v_snd_5895_);
lean_dec_ref(v_x_5892_);
v___x_5896_ = lean_apply_2(v_h__1_5893_, v_fst_5894_, v_snd_5895_);
return v___x_5896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5897_, lean_object* v_inst_5898_, lean_object* v_inst_5899_, lean_object* v_inst_5900_, lean_object* v_x_5901_, lean_object* v___y_5902_){
_start:
{
lean_object* v___x_5903_; 
v___x_5903_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5897_, v_inst_5898_, v_inst_5899_, v_inst_5900_, v___y_5902_);
return v___x_5903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5904_, lean_object* v_toPure_5905_, lean_object* v_____r_5906_){
_start:
{
lean_object* v_tree_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; 
v_tree_5907_ = lean_ctor_get(v_r_5904_, 0);
lean_inc_ref(v_tree_5907_);
lean_dec_ref(v_r_5904_);
v___x_5908_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5907_);
v___x_5909_ = lean_apply_2(v_toPure_5905_, lean_box(0), v___x_5908_);
return v___x_5909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5910_, lean_object* v___x_5911_, lean_object* v_toPure_5912_, lean_object* v_toBind_5913_, lean_object* v_inst_5914_, lean_object* v___f_5915_, lean_object* v_tasks_5916_){
_start:
{
lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v_r_5922_; lean_object* v_errors_5923_; lean_object* v___f_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; uint8_t v___x_5927_; 
v___x_5917_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5910_);
v___x_5918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5910_);
lean_ctor_set(v___x_5918_, 1, v___x_5917_);
v___x_5919_ = lean_mk_empty_array_with_capacity(v___x_5910_);
lean_inc_ref(v___x_5919_);
v___x_5920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5918_);
lean_ctor_set(v___x_5920_, 1, v___x_5919_);
v___x_5921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5920_);
lean_ctor_set(v___x_5921_, 1, v___x_5919_);
v_r_5922_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5911_, v___x_5921_, v_tasks_5916_);
v_errors_5923_ = lean_ctor_get(v_r_5922_, 1);
lean_inc_ref(v_errors_5923_);
lean_inc(v_toPure_5912_);
v___f_5924_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5924_, 0, v_r_5922_);
lean_closure_set(v___f_5924_, 1, v_toPure_5912_);
v___x_5925_ = lean_array_get_size(v_errors_5923_);
v___x_5926_ = lean_box(0);
v___x_5927_ = lean_nat_dec_lt(v___x_5910_, v___x_5925_);
lean_dec(v___x_5910_);
if (v___x_5927_ == 0)
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
lean_dec_ref(v_errors_5923_);
lean_dec(v___f_5915_);
lean_dec_ref(v_inst_5914_);
v___x_5928_ = lean_apply_2(v_toPure_5912_, lean_box(0), v___x_5926_);
v___x_5929_ = lean_apply_4(v_toBind_5913_, lean_box(0), lean_box(0), v___x_5928_, v___f_5924_);
return v___x_5929_;
}
else
{
uint8_t v___x_5930_; 
v___x_5930_ = lean_nat_dec_le(v___x_5925_, v___x_5925_);
if (v___x_5930_ == 0)
{
if (v___x_5927_ == 0)
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
lean_dec_ref(v_errors_5923_);
lean_dec(v___f_5915_);
lean_dec_ref(v_inst_5914_);
v___x_5931_ = lean_apply_2(v_toPure_5912_, lean_box(0), v___x_5926_);
v___x_5932_ = lean_apply_4(v_toBind_5913_, lean_box(0), lean_box(0), v___x_5931_, v___f_5924_);
return v___x_5932_;
}
else
{
size_t v___x_5933_; size_t v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
lean_dec(v_toPure_5912_);
v___x_5933_ = ((size_t)0ULL);
v___x_5934_ = lean_usize_of_nat(v___x_5925_);
v___x_5935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5914_, v___f_5915_, v_errors_5923_, v___x_5933_, v___x_5934_, v___x_5926_);
v___x_5936_ = lean_apply_4(v_toBind_5913_, lean_box(0), lean_box(0), v___x_5935_, v___f_5924_);
return v___x_5936_;
}
}
else
{
size_t v___x_5937_; size_t v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
lean_dec(v_toPure_5912_);
v___x_5937_ = ((size_t)0ULL);
v___x_5938_ = lean_usize_of_nat(v___x_5925_);
v___x_5939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5914_, v___f_5915_, v_errors_5923_, v___x_5937_, v___x_5938_, v___x_5926_);
v___x_5940_ = lean_apply_4(v_toBind_5913_, lean_box(0), lean_box(0), v___x_5939_, v___f_5924_);
return v___x_5940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5943_, lean_object* v_inst_5944_, lean_object* v_inst_5945_, lean_object* v_inst_5946_, lean_object* v_inst_5947_, lean_object* v_cctx_5948_, lean_object* v_ngen_5949_, lean_object* v_env_5950_, lean_object* v_act_5951_, lean_object* v_constantsPerTask_5952_){
_start:
{
lean_object* v___x_5953_; lean_object* v_moduleData_5954_; lean_object* v_toApplicative_5955_; lean_object* v_toBind_5956_; lean_object* v_n_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v_toPure_5961_; lean_object* v___f_5962_; lean_object* v___x_5963_; lean_object* v___f_5964_; lean_object* v___x_5965_; 
v___x_5953_ = l_Lean_Environment_header(v_env_5950_);
v_moduleData_5954_ = lean_ctor_get(v___x_5953_, 6);
lean_inc_ref(v_moduleData_5954_);
lean_dec_ref(v___x_5953_);
v_toApplicative_5955_ = lean_ctor_get(v_inst_5943_, 0);
v_toBind_5956_ = lean_ctor_get(v_inst_5943_, 1);
lean_inc_n(v_toBind_5956_, 2);
v_n_5957_ = lean_array_get_size(v_moduleData_5954_);
lean_dec_ref(v_moduleData_5954_);
v___x_5958_ = lean_unsigned_to_nat(0u);
v___x_5959_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5943_, 2);
v___x_5960_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5943_, v_inst_5947_, v_cctx_5948_, v_env_5950_, v_act_5951_, v_constantsPerTask_5952_, v_n_5957_, v_ngen_5949_, v___x_5959_, v___x_5958_, v___x_5958_, v___x_5958_);
v_toPure_5961_ = lean_ctor_get(v_toApplicative_5955_, 1);
lean_inc(v_toPure_5961_);
v___f_5962_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5962_, 0, v_inst_5943_);
lean_closure_set(v___f_5962_, 1, v_inst_5944_);
lean_closure_set(v___f_5962_, 2, v_inst_5945_);
lean_closure_set(v___f_5962_, 3, v_inst_5946_);
v___x_5963_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_5964_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5964_, 0, v___x_5958_);
lean_closure_set(v___f_5964_, 1, v___x_5963_);
lean_closure_set(v___f_5964_, 2, v_toPure_5961_);
lean_closure_set(v___f_5964_, 3, v_toBind_5956_);
lean_closure_set(v___f_5964_, 4, v_inst_5943_);
lean_closure_set(v___f_5964_, 5, v___f_5962_);
v___x_5965_ = lean_apply_4(v_toBind_5956_, lean_box(0), lean_box(0), v___x_5960_, v___f_5964_);
return v___x_5965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5966_, lean_object* v_00_u03b1_5967_, lean_object* v_inst_5968_, lean_object* v_inst_5969_, lean_object* v_inst_5970_, lean_object* v_inst_5971_, lean_object* v_inst_5972_, lean_object* v_cctx_5973_, lean_object* v_ngen_5974_, lean_object* v_env_5975_, lean_object* v_act_5976_, lean_object* v_constantsPerTask_5977_){
_start:
{
lean_object* v___x_5978_; 
v___x_5978_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5968_, v_inst_5969_, v_inst_5970_, v_inst_5971_, v_inst_5972_, v_cctx_5973_, v_ngen_5974_, v_env_5975_, v_act_5976_, v_constantsPerTask_5977_);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5979_ = lean_box(0);
v___x_5980_ = lean_unsigned_to_nat(16u);
v___x_5981_ = lean_mk_array(v___x_5980_, v___x_5979_);
return v___x_5981_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; 
v___x_5982_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5983_ = lean_unsigned_to_nat(0u);
v___x_5984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
lean_ctor_set(v___x_5984_, 1, v___x_5982_);
return v___x_5984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5985_){
_start:
{
lean_object* v_fileName_5986_; lean_object* v_fileMap_5987_; lean_object* v_options_5988_; lean_object* v_maxRecDepth_5989_; lean_object* v_ref_5990_; lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_6005_; 
v_fileName_5986_ = lean_ctor_get(v_ctx_5985_, 0);
v_fileMap_5987_ = lean_ctor_get(v_ctx_5985_, 1);
v_options_5988_ = lean_ctor_get(v_ctx_5985_, 2);
v_maxRecDepth_5989_ = lean_ctor_get(v_ctx_5985_, 4);
v_ref_5990_ = lean_ctor_get(v_ctx_5985_, 5);
v_isSharedCheck_6005_ = !lean_is_exclusive(v_ctx_5985_);
if (v_isSharedCheck_6005_ == 0)
{
lean_object* v_unused_6006_; lean_object* v_unused_6007_; lean_object* v_unused_6008_; lean_object* v_unused_6009_; lean_object* v_unused_6010_; lean_object* v_unused_6011_; lean_object* v_unused_6012_; lean_object* v_unused_6013_; lean_object* v_unused_6014_; 
v_unused_6006_ = lean_ctor_get(v_ctx_5985_, 13);
lean_dec(v_unused_6006_);
v_unused_6007_ = lean_ctor_get(v_ctx_5985_, 12);
lean_dec(v_unused_6007_);
v_unused_6008_ = lean_ctor_get(v_ctx_5985_, 11);
lean_dec(v_unused_6008_);
v_unused_6009_ = lean_ctor_get(v_ctx_5985_, 10);
lean_dec(v_unused_6009_);
v_unused_6010_ = lean_ctor_get(v_ctx_5985_, 9);
lean_dec(v_unused_6010_);
v_unused_6011_ = lean_ctor_get(v_ctx_5985_, 8);
lean_dec(v_unused_6011_);
v_unused_6012_ = lean_ctor_get(v_ctx_5985_, 7);
lean_dec(v_unused_6012_);
v_unused_6013_ = lean_ctor_get(v_ctx_5985_, 6);
lean_dec(v_unused_6013_);
v_unused_6014_ = lean_ctor_get(v_ctx_5985_, 3);
lean_dec(v_unused_6014_);
v___x_5992_ = v_ctx_5985_;
v_isShared_5993_ = v_isSharedCheck_6005_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_ref_5990_);
lean_inc(v_maxRecDepth_5989_);
lean_inc(v_options_5988_);
lean_inc(v_fileMap_5987_);
lean_inc(v_fileName_5986_);
lean_dec(v_ctx_5985_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_6005_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; uint8_t v___x_5998_; lean_object* v___x_5999_; uint8_t v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6003_; 
v___x_5994_ = lean_unsigned_to_nat(0u);
v___x_5995_ = lean_box(0);
v___x_5996_ = lean_box(0);
v___x_5997_ = l_Lean_firstFrontendMacroScope;
v___x_5998_ = l_Lean_getDiag(v_options_5988_);
v___x_5999_ = lean_box(0);
v___x_6000_ = 0;
v___x_6001_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_5993_ == 0)
{
lean_ctor_set(v___x_5992_, 13, v___x_6001_);
lean_ctor_set(v___x_5992_, 12, v___x_5999_);
lean_ctor_set(v___x_5992_, 11, v___x_5997_);
lean_ctor_set(v___x_5992_, 10, v___x_5995_);
lean_ctor_set(v___x_5992_, 9, v___x_5994_);
lean_ctor_set(v___x_5992_, 8, v___x_5994_);
lean_ctor_set(v___x_5992_, 7, v___x_5996_);
lean_ctor_set(v___x_5992_, 6, v___x_5995_);
lean_ctor_set(v___x_5992_, 3, v___x_5994_);
v___x_6003_ = v___x_5992_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_fileName_5986_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v_fileMap_5987_);
lean_ctor_set(v_reuseFailAlloc_6004_, 2, v_options_5988_);
lean_ctor_set(v_reuseFailAlloc_6004_, 3, v___x_5994_);
lean_ctor_set(v_reuseFailAlloc_6004_, 4, v_maxRecDepth_5989_);
lean_ctor_set(v_reuseFailAlloc_6004_, 5, v_ref_5990_);
lean_ctor_set(v_reuseFailAlloc_6004_, 6, v___x_5995_);
lean_ctor_set(v_reuseFailAlloc_6004_, 7, v___x_5996_);
lean_ctor_set(v_reuseFailAlloc_6004_, 8, v___x_5994_);
lean_ctor_set(v_reuseFailAlloc_6004_, 9, v___x_5994_);
lean_ctor_set(v_reuseFailAlloc_6004_, 10, v___x_5995_);
lean_ctor_set(v_reuseFailAlloc_6004_, 11, v___x_5997_);
lean_ctor_set(v_reuseFailAlloc_6004_, 12, v___x_5999_);
lean_ctor_set(v_reuseFailAlloc_6004_, 13, v___x_6001_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
lean_ctor_set_uint8(v___x_6003_, sizeof(void*)*14, v___x_5998_);
lean_ctor_set_uint8(v___x_6003_, sizeof(void*)*14 + 1, v___x_6000_);
return v___x_6003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_6015_, lean_object* v_opts_6016_, lean_object* v_act_6017_, lean_object* v_decl_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; 
lean_inc(v___y_6022_);
lean_inc_ref(v___y_6021_);
lean_inc(v___y_6020_);
lean_inc_ref(v___y_6019_);
v___x_6024_ = lean_apply_4(v_act_6017_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_);
v___x_6025_ = l_Lean_profileitIOUnsafe___redArg(v_category_6015_, v_opts_6016_, v___x_6024_, v_decl_6018_);
return v___x_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6026_, lean_object* v_opts_6027_, lean_object* v_act_6028_, lean_object* v_decl_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_){
_start:
{
lean_object* v_res_6035_; 
v_res_6035_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6026_, v_opts_6027_, v_act_6028_, v_decl_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
lean_dec(v___y_6033_);
lean_dec_ref(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec_ref(v___y_6030_);
lean_dec_ref(v_opts_6027_);
lean_dec_ref(v_category_6026_);
return v_res_6035_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6036_, lean_object* v_category_6037_, lean_object* v_opts_6038_, lean_object* v_act_6039_, lean_object* v_decl_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_){
_start:
{
lean_object* v___x_6046_; 
v___x_6046_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6037_, v_opts_6038_, v_act_6039_, v_decl_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_);
return v___x_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6047_, lean_object* v_category_6048_, lean_object* v_opts_6049_, lean_object* v_act_6050_, lean_object* v_decl_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_){
_start:
{
lean_object* v_res_6057_; 
v_res_6057_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6047_, v_category_6048_, v_opts_6049_, v_act_6050_, v_decl_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
lean_dec_ref(v_opts_6049_);
lean_dec_ref(v_category_6048_);
return v_res_6057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6058_, lean_object* v_env_6059_, lean_object* v_act_6060_, lean_object* v_constantsPerTask_6061_, lean_object* v_n_6062_, lean_object* v_ngen_6063_, lean_object* v_tasks_6064_, lean_object* v_start_6065_, lean_object* v_cnt_6066_, lean_object* v_idx_6067_){
_start:
{
lean_object* v___x_6069_; lean_object* v_moduleData_6070_; lean_object* v___x_6071_; uint8_t v___x_6072_; 
v___x_6069_ = l_Lean_Environment_header(v_env_6059_);
v_moduleData_6070_ = lean_ctor_get(v___x_6069_, 6);
lean_inc_ref(v_moduleData_6070_);
lean_dec_ref(v___x_6069_);
v___x_6071_ = lean_array_get_size(v_moduleData_6070_);
v___x_6072_ = lean_nat_dec_lt(v_idx_6067_, v___x_6071_);
if (v___x_6072_ == 0)
{
uint8_t v___x_6073_; 
lean_dec_ref(v_moduleData_6070_);
lean_dec(v_idx_6067_);
lean_dec(v_cnt_6066_);
v___x_6073_ = lean_nat_dec_lt(v_start_6065_, v_n_6062_);
if (v___x_6073_ == 0)
{
lean_object* v___x_6074_; 
lean_dec(v_start_6065_);
lean_dec_ref(v_ngen_6063_);
lean_dec(v_n_6062_);
lean_dec_ref(v_act_6060_);
lean_dec_ref(v_env_6059_);
lean_dec_ref(v_cctx_6058_);
v___x_6074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6074_, 0, v_tasks_6064_);
return v___x_6074_;
}
else
{
lean_object* v_namePrefix_6075_; lean_object* v_idx_6076_; lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6090_; 
v_namePrefix_6075_ = lean_ctor_get(v_ngen_6063_, 0);
v_idx_6076_ = lean_ctor_get(v_ngen_6063_, 1);
v_isSharedCheck_6090_ = !lean_is_exclusive(v_ngen_6063_);
if (v_isSharedCheck_6090_ == 0)
{
v___x_6078_ = v_ngen_6063_;
v_isShared_6079_ = v_isSharedCheck_6090_;
goto v_resetjp_6077_;
}
else
{
lean_inc(v_idx_6076_);
lean_inc(v_namePrefix_6075_);
lean_dec(v_ngen_6063_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6090_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6083_; 
v___x_6080_ = l_Lean_Name_num___override(v_namePrefix_6075_, v_idx_6076_);
v___x_6081_ = lean_unsigned_to_nat(1u);
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 1, v___x_6081_);
lean_ctor_set(v___x_6078_, 0, v___x_6080_);
v___x_6083_ = v___x_6078_;
goto v_reusejp_6082_;
}
else
{
lean_object* v_reuseFailAlloc_6089_; 
v_reuseFailAlloc_6089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6089_, 0, v___x_6080_);
lean_ctor_set(v_reuseFailAlloc_6089_, 1, v___x_6081_);
v___x_6083_ = v_reuseFailAlloc_6089_;
goto v_reusejp_6082_;
}
v_reusejp_6082_:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; 
v___x_6084_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6084_, 0, lean_box(0));
lean_closure_set(v___x_6084_, 1, v_cctx_6058_);
lean_closure_set(v___x_6084_, 2, v___x_6083_);
lean_closure_set(v___x_6084_, 3, v_env_6059_);
lean_closure_set(v___x_6084_, 4, v_act_6060_);
lean_closure_set(v___x_6084_, 5, v_start_6065_);
lean_closure_set(v___x_6084_, 6, v_n_6062_);
v___x_6085_ = lean_unsigned_to_nat(0u);
v___x_6086_ = lean_io_as_task(v___x_6084_, v___x_6085_);
v___x_6087_ = lean_array_push(v_tasks_6064_, v___x_6086_);
v___x_6088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6087_);
return v___x_6088_;
}
}
}
}
else
{
lean_object* v_mdata_6091_; lean_object* v_constants_6092_; lean_object* v___x_6093_; lean_object* v_cnt_6094_; uint8_t v___x_6095_; 
v_mdata_6091_ = lean_array_fget(v_moduleData_6070_, v_idx_6067_);
lean_dec_ref(v_moduleData_6070_);
v_constants_6092_ = lean_ctor_get(v_mdata_6091_, 2);
lean_inc_ref(v_constants_6092_);
lean_dec(v_mdata_6091_);
v___x_6093_ = lean_array_get_size(v_constants_6092_);
lean_dec_ref(v_constants_6092_);
v_cnt_6094_ = lean_nat_add(v_cnt_6066_, v___x_6093_);
lean_dec(v_cnt_6066_);
v___x_6095_ = lean_nat_dec_lt(v_constantsPerTask_6061_, v_cnt_6094_);
if (v___x_6095_ == 0)
{
lean_object* v___x_6096_; lean_object* v___x_6097_; 
v___x_6096_ = lean_unsigned_to_nat(1u);
v___x_6097_ = lean_nat_add(v_idx_6067_, v___x_6096_);
lean_dec(v_idx_6067_);
v_cnt_6066_ = v_cnt_6094_;
v_idx_6067_ = v___x_6097_;
goto _start;
}
else
{
lean_object* v_namePrefix_6099_; lean_object* v_idx_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6117_; 
lean_dec(v_cnt_6094_);
v_namePrefix_6099_ = lean_ctor_get(v_ngen_6063_, 0);
v_idx_6100_ = lean_ctor_get(v_ngen_6063_, 1);
v_isSharedCheck_6117_ = !lean_is_exclusive(v_ngen_6063_);
if (v_isSharedCheck_6117_ == 0)
{
v___x_6102_ = v_ngen_6063_;
v_isShared_6103_ = v_isSharedCheck_6117_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_idx_6100_);
lean_inc(v_namePrefix_6099_);
lean_dec(v_ngen_6063_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6117_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6107_; 
lean_inc(v_idx_6100_);
lean_inc(v_namePrefix_6099_);
v___x_6104_ = l_Lean_Name_num___override(v_namePrefix_6099_, v_idx_6100_);
v___x_6105_ = lean_unsigned_to_nat(1u);
if (v_isShared_6103_ == 0)
{
lean_ctor_set(v___x_6102_, 1, v___x_6105_);
lean_ctor_set(v___x_6102_, 0, v___x_6104_);
v___x_6107_ = v___x_6102_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v___x_6104_);
lean_ctor_set(v_reuseFailAlloc_6116_, 1, v___x_6105_);
v___x_6107_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6108_ = lean_nat_add(v_idx_6067_, v___x_6105_);
lean_dec(v_idx_6067_);
lean_inc_n(v___x_6108_, 2);
lean_inc_ref(v_act_6060_);
lean_inc_ref(v_env_6059_);
lean_inc_ref(v_cctx_6058_);
v___x_6109_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6109_, 0, lean_box(0));
lean_closure_set(v___x_6109_, 1, v_cctx_6058_);
lean_closure_set(v___x_6109_, 2, v___x_6107_);
lean_closure_set(v___x_6109_, 3, v_env_6059_);
lean_closure_set(v___x_6109_, 4, v_act_6060_);
lean_closure_set(v___x_6109_, 5, v_start_6065_);
lean_closure_set(v___x_6109_, 6, v___x_6108_);
v___x_6110_ = lean_unsigned_to_nat(0u);
v___x_6111_ = lean_io_as_task(v___x_6109_, v___x_6110_);
v___x_6112_ = lean_nat_add(v_idx_6100_, v___x_6105_);
lean_dec(v_idx_6100_);
v___x_6113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6113_, 0, v_namePrefix_6099_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_array_push(v_tasks_6064_, v___x_6111_);
v_ngen_6063_ = v___x_6113_;
v_tasks_6064_ = v___x_6114_;
v_start_6065_ = v___x_6108_;
v_cnt_6066_ = v___x_6110_;
v_idx_6067_ = v___x_6108_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6118_, lean_object* v_env_6119_, lean_object* v_act_6120_, lean_object* v_constantsPerTask_6121_, lean_object* v_n_6122_, lean_object* v_ngen_6123_, lean_object* v_tasks_6124_, lean_object* v_start_6125_, lean_object* v_cnt_6126_, lean_object* v_idx_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v_res_6129_; 
v_res_6129_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6118_, v_env_6119_, v_act_6120_, v_constantsPerTask_6121_, v_n_6122_, v_ngen_6123_, v_tasks_6124_, v_start_6125_, v_cnt_6126_, v_idx_6127_);
lean_dec(v_constantsPerTask_6121_);
return v_res_6129_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v___y_6138_, uint8_t v_suppressElabErrors_6139_, lean_object* v_x_6140_){
_start:
{
if (lean_obj_tag(v_x_6140_) == 1)
{
lean_object* v_pre_6141_; 
v_pre_6141_ = lean_ctor_get(v_x_6140_, 0);
switch(lean_obj_tag(v_pre_6141_))
{
case 1:
{
lean_object* v_pre_6142_; 
v_pre_6142_ = lean_ctor_get(v_pre_6141_, 0);
switch(lean_obj_tag(v_pre_6142_))
{
case 0:
{
lean_object* v_str_6143_; lean_object* v_str_6144_; lean_object* v___x_6145_; uint8_t v___x_6146_; 
v_str_6143_ = lean_ctor_get(v_x_6140_, 1);
v_str_6144_ = lean_ctor_get(v_pre_6141_, 1);
v___x_6145_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6146_ = lean_string_dec_eq(v_str_6144_, v___x_6145_);
if (v___x_6146_ == 0)
{
lean_object* v___x_6147_; uint8_t v___x_6148_; 
v___x_6147_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6148_ = lean_string_dec_eq(v_str_6144_, v___x_6147_);
if (v___x_6148_ == 0)
{
return v___y_6138_;
}
else
{
lean_object* v___x_6149_; uint8_t v___x_6150_; 
v___x_6149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6150_ = lean_string_dec_eq(v_str_6143_, v___x_6149_);
if (v___x_6150_ == 0)
{
return v___y_6138_;
}
else
{
return v_suppressElabErrors_6139_;
}
}
}
else
{
lean_object* v___x_6151_; uint8_t v___x_6152_; 
v___x_6151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6152_ = lean_string_dec_eq(v_str_6143_, v___x_6151_);
if (v___x_6152_ == 0)
{
return v___y_6138_;
}
else
{
return v_suppressElabErrors_6139_;
}
}
}
case 1:
{
lean_object* v_pre_6153_; 
v_pre_6153_ = lean_ctor_get(v_pre_6142_, 0);
if (lean_obj_tag(v_pre_6153_) == 0)
{
lean_object* v_str_6154_; lean_object* v_str_6155_; lean_object* v_str_6156_; lean_object* v___x_6157_; uint8_t v___x_6158_; 
v_str_6154_ = lean_ctor_get(v_x_6140_, 1);
v_str_6155_ = lean_ctor_get(v_pre_6141_, 1);
v_str_6156_ = lean_ctor_get(v_pre_6142_, 1);
v___x_6157_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6158_ = lean_string_dec_eq(v_str_6156_, v___x_6157_);
if (v___x_6158_ == 0)
{
return v___y_6138_;
}
else
{
lean_object* v___x_6159_; uint8_t v___x_6160_; 
v___x_6159_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6160_ = lean_string_dec_eq(v_str_6155_, v___x_6159_);
if (v___x_6160_ == 0)
{
return v___y_6138_;
}
else
{
lean_object* v___x_6161_; uint8_t v___x_6162_; 
v___x_6161_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6162_ = lean_string_dec_eq(v_str_6154_, v___x_6161_);
if (v___x_6162_ == 0)
{
return v___y_6138_;
}
else
{
return v_suppressElabErrors_6139_;
}
}
}
}
else
{
return v___y_6138_;
}
}
default: 
{
return v___y_6138_;
}
}
}
case 0:
{
lean_object* v_str_6163_; lean_object* v___x_6164_; uint8_t v___x_6165_; 
v_str_6163_ = lean_ctor_get(v_x_6140_, 1);
v___x_6164_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6165_ = lean_string_dec_eq(v_str_6163_, v___x_6164_);
if (v___x_6165_ == 0)
{
return v___y_6138_;
}
else
{
return v_suppressElabErrors_6139_;
}
}
default: 
{
return v___y_6138_;
}
}
}
else
{
return v___y_6138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v___y_6166_, lean_object* v_suppressElabErrors_6167_, lean_object* v_x_6168_){
_start:
{
uint8_t v___y_7861__boxed_6169_; uint8_t v_suppressElabErrors_boxed_6170_; uint8_t v_res_6171_; lean_object* v_r_6172_; 
v___y_7861__boxed_6169_ = lean_unbox(v___y_6166_);
v_suppressElabErrors_boxed_6170_ = lean_unbox(v_suppressElabErrors_6167_);
v_res_6171_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v___y_7861__boxed_6169_, v_suppressElabErrors_boxed_6170_, v_x_6168_);
lean_dec(v_x_6168_);
v_r_6172_ = lean_box(v_res_6171_);
return v_r_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6174_, lean_object* v_msgData_6175_, uint8_t v_severity_6176_, uint8_t v_isSilent_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_){
_start:
{
lean_object* v___y_6184_; uint8_t v___y_6185_; lean_object* v___y_6186_; lean_object* v___y_6187_; lean_object* v___y_6188_; uint8_t v___y_6189_; lean_object* v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6192_; lean_object* v___y_6220_; uint8_t v___y_6221_; lean_object* v___y_6222_; lean_object* v___y_6223_; uint8_t v___y_6224_; uint8_t v___y_6225_; lean_object* v___y_6226_; lean_object* v___y_6227_; lean_object* v___y_6245_; uint8_t v___y_6246_; lean_object* v___y_6247_; uint8_t v___y_6248_; uint8_t v___y_6249_; lean_object* v___y_6250_; lean_object* v___y_6251_; lean_object* v___y_6252_; lean_object* v___y_6256_; lean_object* v___y_6257_; uint8_t v___y_6258_; uint8_t v___y_6259_; lean_object* v___y_6260_; lean_object* v___y_6261_; uint8_t v___y_6262_; uint8_t v___x_6267_; lean_object* v___y_6269_; lean_object* v___y_6270_; lean_object* v___y_6271_; uint8_t v___y_6272_; lean_object* v___y_6273_; uint8_t v___y_6274_; uint8_t v___y_6275_; uint8_t v___y_6277_; uint8_t v___x_6292_; 
v___x_6267_ = 2;
v___x_6292_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6176_, v___x_6267_);
if (v___x_6292_ == 0)
{
v___y_6277_ = v___x_6292_;
goto v___jp_6276_;
}
else
{
uint8_t v___x_6293_; 
lean_inc_ref(v_msgData_6175_);
v___x_6293_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6175_);
v___y_6277_ = v___x_6293_;
goto v___jp_6276_;
}
v___jp_6183_:
{
lean_object* v___x_6193_; lean_object* v_currNamespace_6194_; lean_object* v_openDecls_6195_; lean_object* v_env_6196_; lean_object* v_nextMacroScope_6197_; lean_object* v_ngen_6198_; lean_object* v_auxDeclNGen_6199_; lean_object* v_traceState_6200_; lean_object* v_cache_6201_; lean_object* v_messages_6202_; lean_object* v_infoState_6203_; lean_object* v_snapshotTasks_6204_; lean_object* v___x_6206_; uint8_t v_isShared_6207_; uint8_t v_isSharedCheck_6218_; 
v___x_6193_ = lean_st_ref_take(v___y_6192_);
v_currNamespace_6194_ = lean_ctor_get(v___y_6191_, 6);
v_openDecls_6195_ = lean_ctor_get(v___y_6191_, 7);
v_env_6196_ = lean_ctor_get(v___x_6193_, 0);
v_nextMacroScope_6197_ = lean_ctor_get(v___x_6193_, 1);
v_ngen_6198_ = lean_ctor_get(v___x_6193_, 2);
v_auxDeclNGen_6199_ = lean_ctor_get(v___x_6193_, 3);
v_traceState_6200_ = lean_ctor_get(v___x_6193_, 4);
v_cache_6201_ = lean_ctor_get(v___x_6193_, 5);
v_messages_6202_ = lean_ctor_get(v___x_6193_, 6);
v_infoState_6203_ = lean_ctor_get(v___x_6193_, 7);
v_snapshotTasks_6204_ = lean_ctor_get(v___x_6193_, 8);
v_isSharedCheck_6218_ = !lean_is_exclusive(v___x_6193_);
if (v_isSharedCheck_6218_ == 0)
{
v___x_6206_ = v___x_6193_;
v_isShared_6207_ = v_isSharedCheck_6218_;
goto v_resetjp_6205_;
}
else
{
lean_inc(v_snapshotTasks_6204_);
lean_inc(v_infoState_6203_);
lean_inc(v_messages_6202_);
lean_inc(v_cache_6201_);
lean_inc(v_traceState_6200_);
lean_inc(v_auxDeclNGen_6199_);
lean_inc(v_ngen_6198_);
lean_inc(v_nextMacroScope_6197_);
lean_inc(v_env_6196_);
lean_dec(v___x_6193_);
v___x_6206_ = lean_box(0);
v_isShared_6207_ = v_isSharedCheck_6218_;
goto v_resetjp_6205_;
}
v_resetjp_6205_:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6213_; 
lean_inc(v_openDecls_6195_);
lean_inc(v_currNamespace_6194_);
v___x_6208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6208_, 0, v_currNamespace_6194_);
lean_ctor_set(v___x_6208_, 1, v_openDecls_6195_);
v___x_6209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6209_, 0, v___x_6208_);
lean_ctor_set(v___x_6209_, 1, v___y_6188_);
lean_inc_ref(v___y_6186_);
lean_inc_ref(v___y_6190_);
v___x_6210_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6210_, 0, v___y_6190_);
lean_ctor_set(v___x_6210_, 1, v___y_6184_);
lean_ctor_set(v___x_6210_, 2, v___y_6187_);
lean_ctor_set(v___x_6210_, 3, v___y_6186_);
lean_ctor_set(v___x_6210_, 4, v___x_6209_);
lean_ctor_set_uint8(v___x_6210_, sizeof(void*)*5, v___y_6189_);
lean_ctor_set_uint8(v___x_6210_, sizeof(void*)*5 + 1, v___y_6185_);
lean_ctor_set_uint8(v___x_6210_, sizeof(void*)*5 + 2, v_isSilent_6177_);
v___x_6211_ = l_Lean_MessageLog_add(v___x_6210_, v_messages_6202_);
if (v_isShared_6207_ == 0)
{
lean_ctor_set(v___x_6206_, 6, v___x_6211_);
v___x_6213_ = v___x_6206_;
goto v_reusejp_6212_;
}
else
{
lean_object* v_reuseFailAlloc_6217_; 
v_reuseFailAlloc_6217_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_env_6196_);
lean_ctor_set(v_reuseFailAlloc_6217_, 1, v_nextMacroScope_6197_);
lean_ctor_set(v_reuseFailAlloc_6217_, 2, v_ngen_6198_);
lean_ctor_set(v_reuseFailAlloc_6217_, 3, v_auxDeclNGen_6199_);
lean_ctor_set(v_reuseFailAlloc_6217_, 4, v_traceState_6200_);
lean_ctor_set(v_reuseFailAlloc_6217_, 5, v_cache_6201_);
lean_ctor_set(v_reuseFailAlloc_6217_, 6, v___x_6211_);
lean_ctor_set(v_reuseFailAlloc_6217_, 7, v_infoState_6203_);
lean_ctor_set(v_reuseFailAlloc_6217_, 8, v_snapshotTasks_6204_);
v___x_6213_ = v_reuseFailAlloc_6217_;
goto v_reusejp_6212_;
}
v_reusejp_6212_:
{
lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; 
v___x_6214_ = lean_st_ref_set(v___y_6192_, v___x_6213_);
v___x_6215_ = lean_box(0);
v___x_6216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6216_, 0, v___x_6215_);
return v___x_6216_;
}
}
}
v___jp_6219_:
{
lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v_a_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6243_; 
v___x_6228_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6175_);
v___x_6229_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6228_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_);
v_a_6230_ = lean_ctor_get(v___x_6229_, 0);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6229_);
if (v_isSharedCheck_6243_ == 0)
{
v___x_6232_ = v___x_6229_;
v_isShared_6233_ = v_isSharedCheck_6243_;
goto v_resetjp_6231_;
}
else
{
lean_inc(v_a_6230_);
lean_dec(v___x_6229_);
v___x_6232_ = lean_box(0);
v_isShared_6233_ = v_isSharedCheck_6243_;
goto v_resetjp_6231_;
}
v_resetjp_6231_:
{
lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; 
lean_inc_ref_n(v___y_6222_, 2);
v___x_6234_ = l_Lean_FileMap_toPosition(v___y_6222_, v___y_6223_);
lean_dec(v___y_6223_);
v___x_6235_ = l_Lean_FileMap_toPosition(v___y_6222_, v___y_6227_);
lean_dec(v___y_6227_);
v___x_6236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6236_, 0, v___x_6235_);
v___x_6237_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6224_ == 0)
{
lean_del_object(v___x_6232_);
lean_dec_ref(v___y_6220_);
v___y_6184_ = v___x_6234_;
v___y_6185_ = v___y_6221_;
v___y_6186_ = v___x_6237_;
v___y_6187_ = v___x_6236_;
v___y_6188_ = v_a_6230_;
v___y_6189_ = v___y_6225_;
v___y_6190_ = v___y_6226_;
v___y_6191_ = v___y_6180_;
v___y_6192_ = v___y_6181_;
goto v___jp_6183_;
}
else
{
uint8_t v___x_6238_; 
lean_inc(v_a_6230_);
v___x_6238_ = l_Lean_MessageData_hasTag(v___y_6220_, v_a_6230_);
if (v___x_6238_ == 0)
{
lean_object* v___x_6239_; lean_object* v___x_6241_; 
lean_dec_ref_known(v___x_6236_, 1);
lean_dec_ref(v___x_6234_);
lean_dec(v_a_6230_);
v___x_6239_ = lean_box(0);
if (v_isShared_6233_ == 0)
{
lean_ctor_set(v___x_6232_, 0, v___x_6239_);
v___x_6241_ = v___x_6232_;
goto v_reusejp_6240_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v___x_6239_);
v___x_6241_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6240_;
}
v_reusejp_6240_:
{
return v___x_6241_;
}
}
else
{
lean_del_object(v___x_6232_);
v___y_6184_ = v___x_6234_;
v___y_6185_ = v___y_6221_;
v___y_6186_ = v___x_6237_;
v___y_6187_ = v___x_6236_;
v___y_6188_ = v_a_6230_;
v___y_6189_ = v___y_6225_;
v___y_6190_ = v___y_6226_;
v___y_6191_ = v___y_6180_;
v___y_6192_ = v___y_6181_;
goto v___jp_6183_;
}
}
}
}
v___jp_6244_:
{
lean_object* v___x_6253_; 
v___x_6253_ = l_Lean_Syntax_getTailPos_x3f(v___y_6250_, v___y_6248_);
lean_dec(v___y_6250_);
if (lean_obj_tag(v___x_6253_) == 0)
{
lean_inc(v___y_6252_);
v___y_6220_ = v___y_6245_;
v___y_6221_ = v___y_6246_;
v___y_6222_ = v___y_6247_;
v___y_6223_ = v___y_6252_;
v___y_6224_ = v___y_6249_;
v___y_6225_ = v___y_6248_;
v___y_6226_ = v___y_6251_;
v___y_6227_ = v___y_6252_;
goto v___jp_6219_;
}
else
{
lean_object* v_val_6254_; 
v_val_6254_ = lean_ctor_get(v___x_6253_, 0);
lean_inc(v_val_6254_);
lean_dec_ref_known(v___x_6253_, 1);
v___y_6220_ = v___y_6245_;
v___y_6221_ = v___y_6246_;
v___y_6222_ = v___y_6247_;
v___y_6223_ = v___y_6252_;
v___y_6224_ = v___y_6249_;
v___y_6225_ = v___y_6248_;
v___y_6226_ = v___y_6251_;
v___y_6227_ = v_val_6254_;
goto v___jp_6219_;
}
}
v___jp_6255_:
{
lean_object* v_ref_6263_; lean_object* v___x_6264_; 
v_ref_6263_ = l_Lean_replaceRef(v_ref_6174_, v___y_6260_);
v___x_6264_ = l_Lean_Syntax_getPos_x3f(v_ref_6263_, v___y_6259_);
if (lean_obj_tag(v___x_6264_) == 0)
{
lean_object* v___x_6265_; 
v___x_6265_ = lean_unsigned_to_nat(0u);
v___y_6245_ = v___y_6256_;
v___y_6246_ = v___y_6262_;
v___y_6247_ = v___y_6257_;
v___y_6248_ = v___y_6259_;
v___y_6249_ = v___y_6258_;
v___y_6250_ = v_ref_6263_;
v___y_6251_ = v___y_6261_;
v___y_6252_ = v___x_6265_;
goto v___jp_6244_;
}
else
{
lean_object* v_val_6266_; 
v_val_6266_ = lean_ctor_get(v___x_6264_, 0);
lean_inc(v_val_6266_);
lean_dec_ref_known(v___x_6264_, 1);
v___y_6245_ = v___y_6256_;
v___y_6246_ = v___y_6262_;
v___y_6247_ = v___y_6257_;
v___y_6248_ = v___y_6259_;
v___y_6249_ = v___y_6258_;
v___y_6250_ = v_ref_6263_;
v___y_6251_ = v___y_6261_;
v___y_6252_ = v_val_6266_;
goto v___jp_6244_;
}
}
v___jp_6268_:
{
if (v___y_6275_ == 0)
{
v___y_6256_ = v___y_6270_;
v___y_6257_ = v___y_6269_;
v___y_6258_ = v___y_6272_;
v___y_6259_ = v___y_6274_;
v___y_6260_ = v___y_6271_;
v___y_6261_ = v___y_6273_;
v___y_6262_ = v_severity_6176_;
goto v___jp_6255_;
}
else
{
v___y_6256_ = v___y_6270_;
v___y_6257_ = v___y_6269_;
v___y_6258_ = v___y_6272_;
v___y_6259_ = v___y_6274_;
v___y_6260_ = v___y_6271_;
v___y_6261_ = v___y_6273_;
v___y_6262_ = v___x_6267_;
goto v___jp_6255_;
}
}
v___jp_6276_:
{
if (v___y_6277_ == 0)
{
lean_object* v_fileName_6278_; lean_object* v_fileMap_6279_; lean_object* v_options_6280_; lean_object* v_ref_6281_; uint8_t v_suppressElabErrors_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___f_6285_; uint8_t v___x_6286_; uint8_t v___x_6287_; 
v_fileName_6278_ = lean_ctor_get(v___y_6180_, 0);
v_fileMap_6279_ = lean_ctor_get(v___y_6180_, 1);
v_options_6280_ = lean_ctor_get(v___y_6180_, 2);
v_ref_6281_ = lean_ctor_get(v___y_6180_, 5);
v_suppressElabErrors_6282_ = lean_ctor_get_uint8(v___y_6180_, sizeof(void*)*14 + 1);
v___x_6283_ = lean_box(v___y_6277_);
v___x_6284_ = lean_box(v_suppressElabErrors_6282_);
v___f_6285_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6285_, 0, v___x_6283_);
lean_closure_set(v___f_6285_, 1, v___x_6284_);
v___x_6286_ = 1;
v___x_6287_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6176_, v___x_6286_);
if (v___x_6287_ == 0)
{
v___y_6269_ = v_fileMap_6279_;
v___y_6270_ = v___f_6285_;
v___y_6271_ = v_ref_6281_;
v___y_6272_ = v_suppressElabErrors_6282_;
v___y_6273_ = v_fileName_6278_;
v___y_6274_ = v___y_6277_;
v___y_6275_ = v___x_6287_;
goto v___jp_6268_;
}
else
{
lean_object* v___x_6288_; uint8_t v___x_6289_; 
v___x_6288_ = l_Lean_warningAsError;
v___x_6289_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6280_, v___x_6288_);
v___y_6269_ = v_fileMap_6279_;
v___y_6270_ = v___f_6285_;
v___y_6271_ = v_ref_6281_;
v___y_6272_ = v_suppressElabErrors_6282_;
v___y_6273_ = v_fileName_6278_;
v___y_6274_ = v___y_6277_;
v___y_6275_ = v___x_6289_;
goto v___jp_6268_;
}
}
else
{
lean_object* v___x_6290_; lean_object* v___x_6291_; 
lean_dec_ref(v_msgData_6175_);
v___x_6290_ = lean_box(0);
v___x_6291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6291_, 0, v___x_6290_);
return v___x_6291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6294_, lean_object* v_msgData_6295_, lean_object* v_severity_6296_, lean_object* v_isSilent_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_){
_start:
{
uint8_t v_severity_boxed_6303_; uint8_t v_isSilent_boxed_6304_; lean_object* v_res_6305_; 
v_severity_boxed_6303_ = lean_unbox(v_severity_6296_);
v_isSilent_boxed_6304_ = lean_unbox(v_isSilent_6297_);
v_res_6305_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6294_, v_msgData_6295_, v_severity_boxed_6303_, v_isSilent_boxed_6304_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_);
lean_dec(v___y_6301_);
lean_dec_ref(v___y_6300_);
lean_dec(v___y_6299_);
lean_dec_ref(v___y_6298_);
lean_dec(v_ref_6294_);
return v_res_6305_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6306_, uint8_t v_severity_6307_, uint8_t v_isSilent_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_){
_start:
{
lean_object* v_ref_6314_; lean_object* v___x_6315_; 
v_ref_6314_ = lean_ctor_get(v___y_6311_, 5);
v___x_6315_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6314_, v_msgData_6306_, v_severity_6307_, v_isSilent_6308_, v___y_6309_, v___y_6310_, v___y_6311_, v___y_6312_);
return v___x_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6316_, lean_object* v_severity_6317_, lean_object* v_isSilent_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_){
_start:
{
uint8_t v_severity_boxed_6324_; uint8_t v_isSilent_boxed_6325_; lean_object* v_res_6326_; 
v_severity_boxed_6324_ = lean_unbox(v_severity_6317_);
v_isSilent_boxed_6325_ = lean_unbox(v_isSilent_6318_);
v_res_6326_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6316_, v_severity_boxed_6324_, v_isSilent_boxed_6325_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_);
lean_dec(v___y_6322_);
lean_dec_ref(v___y_6321_);
lean_dec(v___y_6320_);
lean_dec_ref(v___y_6319_);
return v_res_6326_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_){
_start:
{
uint8_t v___x_6333_; uint8_t v___x_6334_; lean_object* v___x_6335_; 
v___x_6333_ = 2;
v___x_6334_ = 0;
v___x_6335_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6327_, v___x_6333_, v___x_6334_, v___y_6328_, v___y_6329_, v___y_6330_, v___y_6331_);
return v___x_6335_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_){
_start:
{
lean_object* v_res_6342_; 
v_res_6342_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
lean_dec(v___y_6340_);
lean_dec_ref(v___y_6339_);
lean_dec(v___y_6338_);
lean_dec_ref(v___y_6337_);
return v_res_6342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_){
_start:
{
lean_object* v_module_6349_; lean_object* v_const_6350_; lean_object* v_exception_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; 
v_module_6349_ = lean_ctor_get(v_f_6343_, 0);
lean_inc(v_module_6349_);
v_const_6350_ = lean_ctor_get(v_f_6343_, 1);
lean_inc(v_const_6350_);
v_exception_6351_ = lean_ctor_get(v_f_6343_, 2);
lean_inc_ref(v_exception_6351_);
lean_dec_ref(v_f_6343_);
v___x_6352_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6353_ = l_Lean_MessageData_ofName(v_const_6350_);
v___x_6354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6354_, 0, v___x_6352_);
lean_ctor_set(v___x_6354_, 1, v___x_6353_);
v___x_6355_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6356_, 0, v___x_6354_);
lean_ctor_set(v___x_6356_, 1, v___x_6355_);
v___x_6357_ = l_Lean_MessageData_ofName(v_module_6349_);
v___x_6358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6358_, 0, v___x_6356_);
lean_ctor_set(v___x_6358_, 1, v___x_6357_);
v___x_6359_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6360_, 0, v___x_6358_);
lean_ctor_set(v___x_6360_, 1, v___x_6359_);
v___x_6361_ = l_Lean_Exception_toMessageData(v_exception_6351_);
v___x_6362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6362_, 0, v___x_6360_);
lean_ctor_set(v___x_6362_, 1, v___x_6361_);
v___x_6363_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6362_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_);
return v___x_6363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_){
_start:
{
lean_object* v_res_6370_; 
v_res_6370_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6364_, v___y_6365_, v___y_6366_, v___y_6367_, v___y_6368_);
lean_dec(v___y_6368_);
lean_dec_ref(v___y_6367_);
lean_dec(v___y_6366_);
lean_dec_ref(v___y_6365_);
return v_res_6370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6371_, size_t v_i_6372_, size_t v_stop_6373_, lean_object* v_b_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_){
_start:
{
uint8_t v___x_6380_; 
v___x_6380_ = lean_usize_dec_eq(v_i_6372_, v_stop_6373_);
if (v___x_6380_ == 0)
{
lean_object* v___x_6381_; lean_object* v___x_6382_; 
v___x_6381_ = lean_array_uget_borrowed(v_as_6371_, v_i_6372_);
lean_inc(v___x_6381_);
v___x_6382_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6381_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_);
if (lean_obj_tag(v___x_6382_) == 0)
{
lean_object* v_a_6383_; size_t v___x_6384_; size_t v___x_6385_; 
v_a_6383_ = lean_ctor_get(v___x_6382_, 0);
lean_inc(v_a_6383_);
lean_dec_ref_known(v___x_6382_, 1);
v___x_6384_ = ((size_t)1ULL);
v___x_6385_ = lean_usize_add(v_i_6372_, v___x_6384_);
v_i_6372_ = v___x_6385_;
v_b_6374_ = v_a_6383_;
goto _start;
}
else
{
return v___x_6382_;
}
}
else
{
lean_object* v___x_6387_; 
v___x_6387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6387_, 0, v_b_6374_);
return v___x_6387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6388_, lean_object* v_i_6389_, lean_object* v_stop_6390_, lean_object* v_b_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_){
_start:
{
size_t v_i_boxed_6397_; size_t v_stop_boxed_6398_; lean_object* v_res_6399_; 
v_i_boxed_6397_ = lean_unbox_usize(v_i_6389_);
lean_dec(v_i_6389_);
v_stop_boxed_6398_ = lean_unbox_usize(v_stop_6390_);
lean_dec(v_stop_6390_);
v_res_6399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6388_, v_i_boxed_6397_, v_stop_boxed_6398_, v_b_6391_, v___y_6392_, v___y_6393_, v___y_6394_, v___y_6395_);
lean_dec(v___y_6395_);
lean_dec_ref(v___y_6394_);
lean_dec(v___y_6393_);
lean_dec_ref(v___y_6392_);
lean_dec_ref(v_as_6388_);
return v_res_6399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6400_, size_t v_i_6401_, size_t v_stop_6402_, lean_object* v_b_6403_){
_start:
{
uint8_t v___x_6404_; 
v___x_6404_ = lean_usize_dec_eq(v_i_6401_, v_stop_6402_);
if (v___x_6404_ == 0)
{
lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6407_; size_t v___x_6408_; size_t v___x_6409_; 
v___x_6405_ = lean_array_uget_borrowed(v_as_6400_, v_i_6401_);
lean_inc(v___x_6405_);
v___x_6406_ = lean_task_get_own(v___x_6405_);
v___x_6407_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6403_, v___x_6406_);
v___x_6408_ = ((size_t)1ULL);
v___x_6409_ = lean_usize_add(v_i_6401_, v___x_6408_);
v_i_6401_ = v___x_6409_;
v_b_6403_ = v___x_6407_;
goto _start;
}
else
{
return v_b_6403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6411_, lean_object* v_i_6412_, lean_object* v_stop_6413_, lean_object* v_b_6414_){
_start:
{
size_t v_i_boxed_6415_; size_t v_stop_boxed_6416_; lean_object* v_res_6417_; 
v_i_boxed_6415_ = lean_unbox_usize(v_i_6412_);
lean_dec(v_i_6412_);
v_stop_boxed_6416_ = lean_unbox_usize(v_stop_6413_);
lean_dec(v_stop_6413_);
v_res_6417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6411_, v_i_boxed_6415_, v_stop_boxed_6416_, v_b_6414_);
lean_dec_ref(v_as_6411_);
return v_res_6417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6418_, lean_object* v_tasks_6419_){
_start:
{
lean_object* v___x_6420_; lean_object* v___x_6421_; uint8_t v___x_6422_; 
v___x_6420_ = lean_unsigned_to_nat(0u);
v___x_6421_ = lean_array_get_size(v_tasks_6419_);
v___x_6422_ = lean_nat_dec_lt(v___x_6420_, v___x_6421_);
if (v___x_6422_ == 0)
{
return v_z_6418_;
}
else
{
uint8_t v___x_6423_; 
v___x_6423_ = lean_nat_dec_le(v___x_6421_, v___x_6421_);
if (v___x_6423_ == 0)
{
if (v___x_6422_ == 0)
{
return v_z_6418_;
}
else
{
size_t v___x_6424_; size_t v___x_6425_; lean_object* v___x_6426_; 
v___x_6424_ = ((size_t)0ULL);
v___x_6425_ = lean_usize_of_nat(v___x_6421_);
v___x_6426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6419_, v___x_6424_, v___x_6425_, v_z_6418_);
return v___x_6426_;
}
}
else
{
size_t v___x_6427_; size_t v___x_6428_; lean_object* v___x_6429_; 
v___x_6427_ = ((size_t)0ULL);
v___x_6428_ = lean_usize_of_nat(v___x_6421_);
v___x_6429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6419_, v___x_6427_, v___x_6428_, v_z_6418_);
return v___x_6429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6430_, lean_object* v_tasks_6431_){
_start:
{
lean_object* v_res_6432_; 
v_res_6432_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6430_, v_tasks_6431_);
lean_dec_ref(v_tasks_6431_);
return v_res_6432_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; 
v___x_6433_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6434_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6435_, 0, v___x_6434_);
lean_ctor_set(v___x_6435_, 1, v___x_6433_);
return v___x_6435_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; 
v___x_6436_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6437_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6438_, 0, v___x_6437_);
lean_ctor_set(v___x_6438_, 1, v___x_6436_);
return v___x_6438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6439_, lean_object* v_ngen_6440_, lean_object* v_env_6441_, lean_object* v_act_6442_, lean_object* v_constantsPerTask_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_){
_start:
{
lean_object* v___x_6449_; lean_object* v_moduleData_6450_; lean_object* v_n_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v_a_6455_; lean_object* v___x_6457_; uint8_t v_isShared_6458_; uint8_t v_isSharedCheck_6497_; 
v___x_6449_ = l_Lean_Environment_header(v_env_6441_);
v_moduleData_6450_ = lean_ctor_get(v___x_6449_, 6);
lean_inc_ref(v_moduleData_6450_);
lean_dec_ref(v___x_6449_);
v_n_6451_ = lean_array_get_size(v_moduleData_6450_);
lean_dec_ref(v_moduleData_6450_);
v___x_6452_ = lean_unsigned_to_nat(0u);
v___x_6453_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6454_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6439_, v_env_6441_, v_act_6442_, v_constantsPerTask_6443_, v_n_6451_, v_ngen_6440_, v___x_6453_, v___x_6452_, v___x_6452_, v___x_6452_);
v_a_6455_ = lean_ctor_get(v___x_6454_, 0);
v_isSharedCheck_6497_ = !lean_is_exclusive(v___x_6454_);
if (v_isSharedCheck_6497_ == 0)
{
v___x_6457_ = v___x_6454_;
v_isShared_6458_ = v_isSharedCheck_6497_;
goto v_resetjp_6456_;
}
else
{
lean_inc(v_a_6455_);
lean_dec(v___x_6454_);
v___x_6457_ = lean_box(0);
v_isShared_6458_ = v_isSharedCheck_6497_;
goto v_resetjp_6456_;
}
v_resetjp_6456_:
{
lean_object* v___x_6459_; lean_object* v_r_6460_; lean_object* v_tree_6467_; lean_object* v_errors_6468_; lean_object* v___x_6469_; uint8_t v___x_6470_; 
v___x_6459_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6460_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6459_, v_a_6455_);
lean_dec(v_a_6455_);
v_tree_6467_ = lean_ctor_get(v_r_6460_, 0);
lean_inc_ref(v_tree_6467_);
v_errors_6468_ = lean_ctor_get(v_r_6460_, 1);
lean_inc_ref(v_errors_6468_);
v___x_6469_ = lean_array_get_size(v_errors_6468_);
v___x_6470_ = lean_nat_dec_lt(v___x_6452_, v___x_6469_);
if (v___x_6470_ == 0)
{
lean_object* v___x_6471_; lean_object* v___x_6472_; 
lean_dec_ref(v_errors_6468_);
lean_dec_ref(v_r_6460_);
lean_del_object(v___x_6457_);
v___x_6471_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6467_);
v___x_6472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6472_, 0, v___x_6471_);
return v___x_6472_;
}
else
{
lean_object* v___x_6473_; uint8_t v___x_6474_; 
lean_dec_ref(v_tree_6467_);
v___x_6473_ = lean_box(0);
v___x_6474_ = lean_nat_dec_le(v___x_6469_, v___x_6469_);
if (v___x_6474_ == 0)
{
if (v___x_6470_ == 0)
{
lean_dec_ref(v_errors_6468_);
goto v___jp_6461_;
}
else
{
size_t v___x_6475_; size_t v___x_6476_; lean_object* v___x_6477_; 
v___x_6475_ = ((size_t)0ULL);
v___x_6476_ = lean_usize_of_nat(v___x_6469_);
v___x_6477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6468_, v___x_6475_, v___x_6476_, v___x_6473_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
lean_dec_ref(v_errors_6468_);
if (lean_obj_tag(v___x_6477_) == 0)
{
lean_dec_ref_known(v___x_6477_, 1);
goto v___jp_6461_;
}
else
{
lean_object* v_a_6478_; lean_object* v___x_6480_; uint8_t v_isShared_6481_; uint8_t v_isSharedCheck_6485_; 
lean_dec_ref(v_r_6460_);
lean_del_object(v___x_6457_);
v_a_6478_ = lean_ctor_get(v___x_6477_, 0);
v_isSharedCheck_6485_ = !lean_is_exclusive(v___x_6477_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6480_ = v___x_6477_;
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
else
{
lean_inc(v_a_6478_);
lean_dec(v___x_6477_);
v___x_6480_ = lean_box(0);
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
v_resetjp_6479_:
{
lean_object* v___x_6483_; 
if (v_isShared_6481_ == 0)
{
v___x_6483_ = v___x_6480_;
goto v_reusejp_6482_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v_a_6478_);
v___x_6483_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6482_;
}
v_reusejp_6482_:
{
return v___x_6483_;
}
}
}
}
}
else
{
size_t v___x_6486_; size_t v___x_6487_; lean_object* v___x_6488_; 
v___x_6486_ = ((size_t)0ULL);
v___x_6487_ = lean_usize_of_nat(v___x_6469_);
v___x_6488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6468_, v___x_6486_, v___x_6487_, v___x_6473_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_);
lean_dec_ref(v_errors_6468_);
if (lean_obj_tag(v___x_6488_) == 0)
{
lean_dec_ref_known(v___x_6488_, 1);
goto v___jp_6461_;
}
else
{
lean_object* v_a_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6496_; 
lean_dec_ref(v_r_6460_);
lean_del_object(v___x_6457_);
v_a_6489_ = lean_ctor_get(v___x_6488_, 0);
v_isSharedCheck_6496_ = !lean_is_exclusive(v___x_6488_);
if (v_isSharedCheck_6496_ == 0)
{
v___x_6491_ = v___x_6488_;
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_a_6489_);
lean_dec(v___x_6488_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v___x_6494_; 
if (v_isShared_6492_ == 0)
{
v___x_6494_ = v___x_6491_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6495_; 
v_reuseFailAlloc_6495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_a_6489_);
v___x_6494_ = v_reuseFailAlloc_6495_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
return v___x_6494_;
}
}
}
}
}
v___jp_6461_:
{
lean_object* v_tree_6462_; lean_object* v___x_6463_; lean_object* v___x_6465_; 
v_tree_6462_ = lean_ctor_get(v_r_6460_, 0);
lean_inc_ref(v_tree_6462_);
lean_dec_ref(v_r_6460_);
v___x_6463_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6462_);
if (v_isShared_6458_ == 0)
{
lean_ctor_set(v___x_6457_, 0, v___x_6463_);
v___x_6465_ = v___x_6457_;
goto v_reusejp_6464_;
}
else
{
lean_object* v_reuseFailAlloc_6466_; 
v_reuseFailAlloc_6466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6466_, 0, v___x_6463_);
v___x_6465_ = v_reuseFailAlloc_6466_;
goto v_reusejp_6464_;
}
v_reusejp_6464_:
{
return v___x_6465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6498_, lean_object* v_ngen_6499_, lean_object* v_env_6500_, lean_object* v_act_6501_, lean_object* v_constantsPerTask_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_){
_start:
{
lean_object* v_res_6508_; 
v_res_6508_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6498_, v_ngen_6499_, v_env_6500_, v_act_6501_, v_constantsPerTask_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_);
lean_dec(v___y_6506_);
lean_dec_ref(v___y_6505_);
lean_dec(v___y_6504_);
lean_dec_ref(v___y_6503_);
lean_dec(v_constantsPerTask_6502_);
return v_res_6508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6509_, lean_object* v___x_6510_, lean_object* v_addEntry_6511_, lean_object* v_constantsPerTask_6512_, lean_object* v_droppedEntriesRef_6513_, lean_object* v_droppedKeys_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_){
_start:
{
lean_object* v___x_6520_; lean_object* v_env_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; 
v___x_6520_ = lean_st_ref_get(v___y_6518_);
v_env_6521_ = lean_ctor_get(v___x_6520_, 0);
lean_inc_ref(v_env_6521_);
lean_dec(v___x_6520_);
lean_inc_ref(v_a_6509_);
v___x_6522_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6509_);
v___x_6523_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6522_, v___x_6510_, v_env_6521_, v_addEntry_6511_, v_constantsPerTask_6512_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
if (lean_obj_tag(v___x_6523_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6513_) == 1)
{
lean_object* v_a_6524_; lean_object* v_val_6525_; lean_object* v___x_6527_; uint8_t v_isShared_6528_; uint8_t v_isSharedCheck_6558_; 
v_a_6524_ = lean_ctor_get(v___x_6523_, 0);
lean_inc(v_a_6524_);
lean_dec_ref_known(v___x_6523_, 1);
v_val_6525_ = lean_ctor_get(v_droppedEntriesRef_6513_, 0);
v_isSharedCheck_6558_ = !lean_is_exclusive(v_droppedEntriesRef_6513_);
if (v_isSharedCheck_6558_ == 0)
{
v___x_6527_ = v_droppedEntriesRef_6513_;
v_isShared_6528_ = v_isSharedCheck_6558_;
goto v_resetjp_6526_;
}
else
{
lean_inc(v_val_6525_);
lean_dec(v_droppedEntriesRef_6513_);
v___x_6527_ = lean_box(0);
v_isShared_6528_ = v_isSharedCheck_6558_;
goto v_resetjp_6526_;
}
v_resetjp_6526_:
{
lean_object* v___x_6529_; 
v___x_6529_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6524_, v_droppedKeys_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
lean_dec(v_droppedKeys_6514_);
if (lean_obj_tag(v___x_6529_) == 0)
{
lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6549_; 
v_a_6530_ = lean_ctor_get(v___x_6529_, 0);
v_isSharedCheck_6549_ = !lean_is_exclusive(v___x_6529_);
if (v_isSharedCheck_6549_ == 0)
{
v___x_6532_ = v___x_6529_;
v_isShared_6533_ = v_isSharedCheck_6549_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_dec(v___x_6529_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6549_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v_fst_6534_; lean_object* v_snd_6535_; lean_object* v___x_6536_; lean_object* v___y_6538_; 
v_fst_6534_ = lean_ctor_get(v_a_6530_, 0);
lean_inc(v_fst_6534_);
v_snd_6535_ = lean_ctor_get(v_a_6530_, 1);
lean_inc(v_snd_6535_);
lean_dec(v_a_6530_);
v___x_6536_ = lean_st_ref_get(v_val_6525_);
if (lean_obj_tag(v___x_6536_) == 0)
{
lean_object* v___x_6547_; 
v___x_6547_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6538_ = v___x_6547_;
goto v___jp_6537_;
}
else
{
lean_object* v_val_6548_; 
v_val_6548_ = lean_ctor_get(v___x_6536_, 0);
lean_inc(v_val_6548_);
lean_dec_ref_known(v___x_6536_, 1);
v___y_6538_ = v_val_6548_;
goto v___jp_6537_;
}
v___jp_6537_:
{
lean_object* v___x_6539_; lean_object* v___x_6541_; 
v___x_6539_ = l_Array_append___redArg(v___y_6538_, v_fst_6534_);
lean_dec(v_fst_6534_);
if (v_isShared_6528_ == 0)
{
lean_ctor_set(v___x_6527_, 0, v___x_6539_);
v___x_6541_ = v___x_6527_;
goto v_reusejp_6540_;
}
else
{
lean_object* v_reuseFailAlloc_6546_; 
v_reuseFailAlloc_6546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6546_, 0, v___x_6539_);
v___x_6541_ = v_reuseFailAlloc_6546_;
goto v_reusejp_6540_;
}
v_reusejp_6540_:
{
lean_object* v___x_6542_; lean_object* v___x_6544_; 
v___x_6542_ = lean_st_ref_set(v_val_6525_, v___x_6541_);
lean_dec(v_val_6525_);
if (v_isShared_6533_ == 0)
{
lean_ctor_set(v___x_6532_, 0, v_snd_6535_);
v___x_6544_ = v___x_6532_;
goto v_reusejp_6543_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v_snd_6535_);
v___x_6544_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6543_;
}
v_reusejp_6543_:
{
return v___x_6544_;
}
}
}
}
}
else
{
lean_object* v_a_6550_; lean_object* v___x_6552_; uint8_t v_isShared_6553_; uint8_t v_isSharedCheck_6557_; 
lean_del_object(v___x_6527_);
lean_dec(v_val_6525_);
v_a_6550_ = lean_ctor_get(v___x_6529_, 0);
v_isSharedCheck_6557_ = !lean_is_exclusive(v___x_6529_);
if (v_isSharedCheck_6557_ == 0)
{
v___x_6552_ = v___x_6529_;
v_isShared_6553_ = v_isSharedCheck_6557_;
goto v_resetjp_6551_;
}
else
{
lean_inc(v_a_6550_);
lean_dec(v___x_6529_);
v___x_6552_ = lean_box(0);
v_isShared_6553_ = v_isSharedCheck_6557_;
goto v_resetjp_6551_;
}
v_resetjp_6551_:
{
lean_object* v___x_6555_; 
if (v_isShared_6553_ == 0)
{
v___x_6555_ = v___x_6552_;
goto v_reusejp_6554_;
}
else
{
lean_object* v_reuseFailAlloc_6556_; 
v_reuseFailAlloc_6556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6556_, 0, v_a_6550_);
v___x_6555_ = v_reuseFailAlloc_6556_;
goto v_reusejp_6554_;
}
v_reusejp_6554_:
{
return v___x_6555_;
}
}
}
}
}
else
{
lean_object* v_a_6559_; lean_object* v___x_6560_; 
lean_dec(v_droppedEntriesRef_6513_);
v_a_6559_ = lean_ctor_get(v___x_6523_, 0);
lean_inc(v_a_6559_);
lean_dec_ref_known(v___x_6523_, 1);
v___x_6560_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6559_, v_droppedKeys_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
return v___x_6560_;
}
}
else
{
lean_dec(v_droppedKeys_6514_);
lean_dec(v_droppedEntriesRef_6513_);
return v___x_6523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6561_, lean_object* v___x_6562_, lean_object* v_addEntry_6563_, lean_object* v_constantsPerTask_6564_, lean_object* v_droppedEntriesRef_6565_, lean_object* v_droppedKeys_6566_, lean_object* v___y_6567_, lean_object* v___y_6568_, lean_object* v___y_6569_, lean_object* v___y_6570_, lean_object* v___y_6571_){
_start:
{
lean_object* v_res_6572_; 
v_res_6572_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6561_, v___x_6562_, v_addEntry_6563_, v_constantsPerTask_6564_, v_droppedEntriesRef_6565_, v_droppedKeys_6566_, v___y_6567_, v___y_6568_, v___y_6569_, v___y_6570_);
lean_dec(v___y_6570_);
lean_dec_ref(v___y_6569_);
lean_dec(v___y_6568_);
lean_dec_ref(v___y_6567_);
lean_dec(v_constantsPerTask_6564_);
lean_dec_ref(v_a_6561_);
return v_res_6572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6574_, lean_object* v_addEntry_6575_, lean_object* v_droppedKeys_6576_, lean_object* v_constantsPerTask_6577_, lean_object* v_droppedEntriesRef_6578_, lean_object* v_ty_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_){
_start:
{
lean_object* v_a_6586_; lean_object* v___x_6608_; lean_object* v_ngen_6609_; lean_object* v_namePrefix_6610_; lean_object* v_idx_6611_; lean_object* v___x_6613_; uint8_t v_isShared_6614_; uint8_t v_isSharedCheck_6656_; 
v___x_6608_ = lean_st_ref_get(v_a_6583_);
v_ngen_6609_ = lean_ctor_get(v___x_6608_, 2);
lean_inc_ref(v_ngen_6609_);
lean_dec(v___x_6608_);
v_namePrefix_6610_ = lean_ctor_get(v_ngen_6609_, 0);
v_idx_6611_ = lean_ctor_get(v_ngen_6609_, 1);
v_isSharedCheck_6656_ = !lean_is_exclusive(v_ngen_6609_);
if (v_isSharedCheck_6656_ == 0)
{
v___x_6613_ = v_ngen_6609_;
v_isShared_6614_ = v_isSharedCheck_6656_;
goto v_resetjp_6612_;
}
else
{
lean_inc(v_idx_6611_);
lean_inc(v_namePrefix_6610_);
lean_dec(v_ngen_6609_);
v___x_6613_ = lean_box(0);
v_isShared_6614_ = v_isSharedCheck_6656_;
goto v_resetjp_6612_;
}
v___jp_6585_:
{
lean_object* v___x_6587_; 
v___x_6587_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6586_, v_ty_6579_, v_a_6580_, v_a_6581_, v_a_6582_, v_a_6583_);
if (lean_obj_tag(v___x_6587_) == 0)
{
lean_object* v_a_6588_; lean_object* v___x_6590_; uint8_t v_isShared_6591_; uint8_t v_isSharedCheck_6599_; 
v_a_6588_ = lean_ctor_get(v___x_6587_, 0);
v_isSharedCheck_6599_ = !lean_is_exclusive(v___x_6587_);
if (v_isSharedCheck_6599_ == 0)
{
v___x_6590_ = v___x_6587_;
v_isShared_6591_ = v_isSharedCheck_6599_;
goto v_resetjp_6589_;
}
else
{
lean_inc(v_a_6588_);
lean_dec(v___x_6587_);
v___x_6590_ = lean_box(0);
v_isShared_6591_ = v_isSharedCheck_6599_;
goto v_resetjp_6589_;
}
v_resetjp_6589_:
{
lean_object* v_fst_6592_; lean_object* v_snd_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6597_; 
v_fst_6592_ = lean_ctor_get(v_a_6588_, 0);
lean_inc(v_fst_6592_);
v_snd_6593_ = lean_ctor_get(v_a_6588_, 1);
lean_inc(v_snd_6593_);
lean_dec(v_a_6588_);
v___x_6594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6594_, 0, v_snd_6593_);
v___x_6595_ = lean_st_ref_set(v_ref_6574_, v___x_6594_);
if (v_isShared_6591_ == 0)
{
lean_ctor_set(v___x_6590_, 0, v_fst_6592_);
v___x_6597_ = v___x_6590_;
goto v_reusejp_6596_;
}
else
{
lean_object* v_reuseFailAlloc_6598_; 
v_reuseFailAlloc_6598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6598_, 0, v_fst_6592_);
v___x_6597_ = v_reuseFailAlloc_6598_;
goto v_reusejp_6596_;
}
v_reusejp_6596_:
{
return v___x_6597_;
}
}
}
else
{
lean_object* v_a_6600_; lean_object* v___x_6602_; uint8_t v_isShared_6603_; uint8_t v_isSharedCheck_6607_; 
v_a_6600_ = lean_ctor_get(v___x_6587_, 0);
v_isSharedCheck_6607_ = !lean_is_exclusive(v___x_6587_);
if (v_isSharedCheck_6607_ == 0)
{
v___x_6602_ = v___x_6587_;
v_isShared_6603_ = v_isSharedCheck_6607_;
goto v_resetjp_6601_;
}
else
{
lean_inc(v_a_6600_);
lean_dec(v___x_6587_);
v___x_6602_ = lean_box(0);
v_isShared_6603_ = v_isSharedCheck_6607_;
goto v_resetjp_6601_;
}
v_resetjp_6601_:
{
lean_object* v___x_6605_; 
if (v_isShared_6603_ == 0)
{
v___x_6605_ = v___x_6602_;
goto v_reusejp_6604_;
}
else
{
lean_object* v_reuseFailAlloc_6606_; 
v_reuseFailAlloc_6606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6606_, 0, v_a_6600_);
v___x_6605_ = v_reuseFailAlloc_6606_;
goto v_reusejp_6604_;
}
v_reusejp_6604_:
{
return v___x_6605_;
}
}
}
}
v_resetjp_6612_:
{
lean_object* v___x_6615_; lean_object* v_env_6616_; lean_object* v_nextMacroScope_6617_; lean_object* v_auxDeclNGen_6618_; lean_object* v_traceState_6619_; lean_object* v_cache_6620_; lean_object* v_messages_6621_; lean_object* v_infoState_6622_; lean_object* v_snapshotTasks_6623_; lean_object* v___x_6625_; uint8_t v_isShared_6626_; uint8_t v_isSharedCheck_6654_; 
v___x_6615_ = lean_st_ref_take(v_a_6583_);
v_env_6616_ = lean_ctor_get(v___x_6615_, 0);
v_nextMacroScope_6617_ = lean_ctor_get(v___x_6615_, 1);
v_auxDeclNGen_6618_ = lean_ctor_get(v___x_6615_, 3);
v_traceState_6619_ = lean_ctor_get(v___x_6615_, 4);
v_cache_6620_ = lean_ctor_get(v___x_6615_, 5);
v_messages_6621_ = lean_ctor_get(v___x_6615_, 6);
v_infoState_6622_ = lean_ctor_get(v___x_6615_, 7);
v_snapshotTasks_6623_ = lean_ctor_get(v___x_6615_, 8);
v_isSharedCheck_6654_ = !lean_is_exclusive(v___x_6615_);
if (v_isSharedCheck_6654_ == 0)
{
lean_object* v_unused_6655_; 
v_unused_6655_ = lean_ctor_get(v___x_6615_, 2);
lean_dec(v_unused_6655_);
v___x_6625_ = v___x_6615_;
v_isShared_6626_ = v_isSharedCheck_6654_;
goto v_resetjp_6624_;
}
else
{
lean_inc(v_snapshotTasks_6623_);
lean_inc(v_infoState_6622_);
lean_inc(v_messages_6621_);
lean_inc(v_cache_6620_);
lean_inc(v_traceState_6619_);
lean_inc(v_auxDeclNGen_6618_);
lean_inc(v_nextMacroScope_6617_);
lean_inc(v_env_6616_);
lean_dec(v___x_6615_);
v___x_6625_ = lean_box(0);
v_isShared_6626_ = v_isSharedCheck_6654_;
goto v_resetjp_6624_;
}
v_resetjp_6624_:
{
lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6631_; 
lean_inc(v_idx_6611_);
lean_inc(v_namePrefix_6610_);
v___x_6627_ = l_Lean_Name_num___override(v_namePrefix_6610_, v_idx_6611_);
v___x_6628_ = lean_unsigned_to_nat(1u);
v___x_6629_ = lean_nat_add(v_idx_6611_, v___x_6628_);
lean_dec(v_idx_6611_);
if (v_isShared_6614_ == 0)
{
lean_ctor_set(v___x_6613_, 1, v___x_6629_);
v___x_6631_ = v___x_6613_;
goto v_reusejp_6630_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v_namePrefix_6610_);
lean_ctor_set(v_reuseFailAlloc_6653_, 1, v___x_6629_);
v___x_6631_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6630_;
}
v_reusejp_6630_:
{
lean_object* v___x_6633_; 
if (v_isShared_6626_ == 0)
{
lean_ctor_set(v___x_6625_, 2, v___x_6631_);
v___x_6633_ = v___x_6625_;
goto v_reusejp_6632_;
}
else
{
lean_object* v_reuseFailAlloc_6652_; 
v_reuseFailAlloc_6652_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6652_, 0, v_env_6616_);
lean_ctor_set(v_reuseFailAlloc_6652_, 1, v_nextMacroScope_6617_);
lean_ctor_set(v_reuseFailAlloc_6652_, 2, v___x_6631_);
lean_ctor_set(v_reuseFailAlloc_6652_, 3, v_auxDeclNGen_6618_);
lean_ctor_set(v_reuseFailAlloc_6652_, 4, v_traceState_6619_);
lean_ctor_set(v_reuseFailAlloc_6652_, 5, v_cache_6620_);
lean_ctor_set(v_reuseFailAlloc_6652_, 6, v_messages_6621_);
lean_ctor_set(v_reuseFailAlloc_6652_, 7, v_infoState_6622_);
lean_ctor_set(v_reuseFailAlloc_6652_, 8, v_snapshotTasks_6623_);
v___x_6633_ = v_reuseFailAlloc_6652_;
goto v_reusejp_6632_;
}
v_reusejp_6632_:
{
lean_object* v___x_6634_; lean_object* v___x_6635_; 
v___x_6634_ = lean_st_ref_set(v_a_6583_, v___x_6633_);
v___x_6635_ = lean_st_ref_get(v_ref_6574_);
if (lean_obj_tag(v___x_6635_) == 0)
{
lean_object* v_options_6636_; lean_object* v___x_6637_; lean_object* v___f_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
v_options_6636_ = lean_ctor_get(v_a_6582_, 2);
v___x_6637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6637_, 0, v___x_6627_);
lean_ctor_set(v___x_6637_, 1, v___x_6628_);
lean_inc_ref(v_a_6582_);
v___f_6638_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6638_, 0, v_a_6582_);
lean_closure_set(v___f_6638_, 1, v___x_6637_);
lean_closure_set(v___f_6638_, 2, v_addEntry_6575_);
lean_closure_set(v___f_6638_, 3, v_constantsPerTask_6577_);
lean_closure_set(v___f_6638_, 4, v_droppedEntriesRef_6578_);
lean_closure_set(v___f_6638_, 5, v_droppedKeys_6576_);
v___x_6639_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6640_ = lean_box(0);
v___x_6641_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6639_, v_options_6636_, v___f_6638_, v___x_6640_, v_a_6580_, v_a_6581_, v_a_6582_, v_a_6583_);
if (lean_obj_tag(v___x_6641_) == 0)
{
lean_object* v_a_6642_; 
v_a_6642_ = lean_ctor_get(v___x_6641_, 0);
lean_inc(v_a_6642_);
lean_dec_ref_known(v___x_6641_, 1);
v_a_6586_ = v_a_6642_;
goto v___jp_6585_;
}
else
{
lean_object* v_a_6643_; lean_object* v___x_6645_; uint8_t v_isShared_6646_; uint8_t v_isSharedCheck_6650_; 
lean_dec_ref(v_ty_6579_);
v_a_6643_ = lean_ctor_get(v___x_6641_, 0);
v_isSharedCheck_6650_ = !lean_is_exclusive(v___x_6641_);
if (v_isSharedCheck_6650_ == 0)
{
v___x_6645_ = v___x_6641_;
v_isShared_6646_ = v_isSharedCheck_6650_;
goto v_resetjp_6644_;
}
else
{
lean_inc(v_a_6643_);
lean_dec(v___x_6641_);
v___x_6645_ = lean_box(0);
v_isShared_6646_ = v_isSharedCheck_6650_;
goto v_resetjp_6644_;
}
v_resetjp_6644_:
{
lean_object* v___x_6648_; 
if (v_isShared_6646_ == 0)
{
v___x_6648_ = v___x_6645_;
goto v_reusejp_6647_;
}
else
{
lean_object* v_reuseFailAlloc_6649_; 
v_reuseFailAlloc_6649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6649_, 0, v_a_6643_);
v___x_6648_ = v_reuseFailAlloc_6649_;
goto v_reusejp_6647_;
}
v_reusejp_6647_:
{
return v___x_6648_;
}
}
}
}
else
{
lean_object* v_val_6651_; 
lean_dec(v___x_6627_);
lean_dec(v_droppedEntriesRef_6578_);
lean_dec(v_constantsPerTask_6577_);
lean_dec(v_droppedKeys_6576_);
lean_dec_ref(v_addEntry_6575_);
v_val_6651_ = lean_ctor_get(v___x_6635_, 0);
lean_inc(v_val_6651_);
lean_dec_ref_known(v___x_6635_, 1);
v_a_6586_ = v_val_6651_;
goto v___jp_6585_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6657_, lean_object* v_addEntry_6658_, lean_object* v_droppedKeys_6659_, lean_object* v_constantsPerTask_6660_, lean_object* v_droppedEntriesRef_6661_, lean_object* v_ty_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_, lean_object* v_a_6665_, lean_object* v_a_6666_, lean_object* v_a_6667_){
_start:
{
lean_object* v_res_6668_; 
v_res_6668_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6657_, v_addEntry_6658_, v_droppedKeys_6659_, v_constantsPerTask_6660_, v_droppedEntriesRef_6661_, v_ty_6662_, v_a_6663_, v_a_6664_, v_a_6665_, v_a_6666_);
lean_dec(v_a_6666_);
lean_dec_ref(v_a_6665_);
lean_dec(v_a_6664_);
lean_dec_ref(v_a_6663_);
lean_dec(v_ref_6657_);
return v_res_6668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6669_, lean_object* v_ref_6670_, lean_object* v_addEntry_6671_, lean_object* v_droppedKeys_6672_, lean_object* v_constantsPerTask_6673_, lean_object* v_droppedEntriesRef_6674_, lean_object* v_ty_6675_, lean_object* v_a_6676_, lean_object* v_a_6677_, lean_object* v_a_6678_, lean_object* v_a_6679_){
_start:
{
lean_object* v___x_6681_; 
v___x_6681_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6670_, v_addEntry_6671_, v_droppedKeys_6672_, v_constantsPerTask_6673_, v_droppedEntriesRef_6674_, v_ty_6675_, v_a_6676_, v_a_6677_, v_a_6678_, v_a_6679_);
return v___x_6681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6682_, lean_object* v_ref_6683_, lean_object* v_addEntry_6684_, lean_object* v_droppedKeys_6685_, lean_object* v_constantsPerTask_6686_, lean_object* v_droppedEntriesRef_6687_, lean_object* v_ty_6688_, lean_object* v_a_6689_, lean_object* v_a_6690_, lean_object* v_a_6691_, lean_object* v_a_6692_, lean_object* v_a_6693_){
_start:
{
lean_object* v_res_6694_; 
v_res_6694_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6682_, v_ref_6683_, v_addEntry_6684_, v_droppedKeys_6685_, v_constantsPerTask_6686_, v_droppedEntriesRef_6687_, v_ty_6688_, v_a_6689_, v_a_6690_, v_a_6691_, v_a_6692_);
lean_dec(v_a_6692_);
lean_dec_ref(v_a_6691_);
lean_dec(v_a_6690_);
lean_dec_ref(v_a_6689_);
lean_dec(v_ref_6683_);
return v_res_6694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6695_, lean_object* v_cctx_6696_, lean_object* v_ngen_6697_, lean_object* v_env_6698_, lean_object* v_act_6699_, lean_object* v_constantsPerTask_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_){
_start:
{
lean_object* v___x_6706_; 
v___x_6706_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6696_, v_ngen_6697_, v_env_6698_, v_act_6699_, v_constantsPerTask_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_);
return v___x_6706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6707_, lean_object* v_cctx_6708_, lean_object* v_ngen_6709_, lean_object* v_env_6710_, lean_object* v_act_6711_, lean_object* v_constantsPerTask_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_, lean_object* v___y_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_){
_start:
{
lean_object* v_res_6718_; 
v_res_6718_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6707_, v_cctx_6708_, v_ngen_6709_, v_env_6710_, v_act_6711_, v_constantsPerTask_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_);
lean_dec(v___y_6716_);
lean_dec_ref(v___y_6715_);
lean_dec(v___y_6714_);
lean_dec_ref(v___y_6713_);
lean_dec(v_constantsPerTask_6712_);
return v_res_6718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6719_, lean_object* v_cctx_6720_, lean_object* v_env_6721_, lean_object* v_act_6722_, lean_object* v_constantsPerTask_6723_, lean_object* v_n_6724_, lean_object* v_ngen_6725_, lean_object* v_tasks_6726_, lean_object* v_start_6727_, lean_object* v_cnt_6728_, lean_object* v_idx_6729_, lean_object* v___y_6730_, lean_object* v___y_6731_, lean_object* v___y_6732_, lean_object* v___y_6733_){
_start:
{
lean_object* v___x_6735_; 
v___x_6735_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6720_, v_env_6721_, v_act_6722_, v_constantsPerTask_6723_, v_n_6724_, v_ngen_6725_, v_tasks_6726_, v_start_6727_, v_cnt_6728_, v_idx_6729_);
return v___x_6735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6736_, lean_object* v_cctx_6737_, lean_object* v_env_6738_, lean_object* v_act_6739_, lean_object* v_constantsPerTask_6740_, lean_object* v_n_6741_, lean_object* v_ngen_6742_, lean_object* v_tasks_6743_, lean_object* v_start_6744_, lean_object* v_cnt_6745_, lean_object* v_idx_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_){
_start:
{
lean_object* v_res_6752_; 
v_res_6752_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6736_, v_cctx_6737_, v_env_6738_, v_act_6739_, v_constantsPerTask_6740_, v_n_6741_, v_ngen_6742_, v_tasks_6743_, v_start_6744_, v_cnt_6745_, v_idx_6746_, v___y_6747_, v___y_6748_, v___y_6749_, v___y_6750_);
lean_dec(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec(v___y_6748_);
lean_dec_ref(v___y_6747_);
lean_dec(v_constantsPerTask_6740_);
return v_res_6752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6753_, lean_object* v_z_6754_, lean_object* v_tasks_6755_){
_start:
{
lean_object* v___x_6756_; 
v___x_6756_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6754_, v_tasks_6755_);
return v___x_6756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6757_, lean_object* v_z_6758_, lean_object* v_tasks_6759_){
_start:
{
lean_object* v_res_6760_; 
v_res_6760_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6757_, v_z_6758_, v_tasks_6759_);
lean_dec_ref(v_tasks_6759_);
return v_res_6760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6761_, lean_object* v_as_6762_, size_t v_i_6763_, size_t v_stop_6764_, lean_object* v_b_6765_){
_start:
{
lean_object* v___x_6766_; 
v___x_6766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6762_, v_i_6763_, v_stop_6764_, v_b_6765_);
return v___x_6766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6767_, lean_object* v_as_6768_, lean_object* v_i_6769_, lean_object* v_stop_6770_, lean_object* v_b_6771_){
_start:
{
size_t v_i_boxed_6772_; size_t v_stop_boxed_6773_; lean_object* v_res_6774_; 
v_i_boxed_6772_ = lean_unbox_usize(v_i_6769_);
lean_dec(v_i_6769_);
v_stop_boxed_6773_ = lean_unbox_usize(v_stop_6770_);
lean_dec(v_stop_6770_);
v_res_6774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6767_, v_as_6768_, v_i_boxed_6772_, v_stop_boxed_6773_, v_b_6771_);
lean_dec_ref(v_as_6768_);
return v_res_6774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6775_){
_start:
{
lean_object* v___x_6777_; lean_object* v_ngen_6778_; lean_object* v_namePrefix_6779_; lean_object* v_idx_6780_; lean_object* v___x_6782_; uint8_t v_isShared_6783_; uint8_t v_isSharedCheck_6810_; 
v___x_6777_ = lean_st_ref_get(v___y_6775_);
v_ngen_6778_ = lean_ctor_get(v___x_6777_, 2);
lean_inc_ref(v_ngen_6778_);
lean_dec(v___x_6777_);
v_namePrefix_6779_ = lean_ctor_get(v_ngen_6778_, 0);
v_idx_6780_ = lean_ctor_get(v_ngen_6778_, 1);
v_isSharedCheck_6810_ = !lean_is_exclusive(v_ngen_6778_);
if (v_isSharedCheck_6810_ == 0)
{
v___x_6782_ = v_ngen_6778_;
v_isShared_6783_ = v_isSharedCheck_6810_;
goto v_resetjp_6781_;
}
else
{
lean_inc(v_idx_6780_);
lean_inc(v_namePrefix_6779_);
lean_dec(v_ngen_6778_);
v___x_6782_ = lean_box(0);
v_isShared_6783_ = v_isSharedCheck_6810_;
goto v_resetjp_6781_;
}
v_resetjp_6781_:
{
lean_object* v___x_6784_; lean_object* v_env_6785_; lean_object* v_nextMacroScope_6786_; lean_object* v_auxDeclNGen_6787_; lean_object* v_traceState_6788_; lean_object* v_cache_6789_; lean_object* v_messages_6790_; lean_object* v_infoState_6791_; lean_object* v_snapshotTasks_6792_; lean_object* v___x_6794_; uint8_t v_isShared_6795_; uint8_t v_isSharedCheck_6808_; 
v___x_6784_ = lean_st_ref_take(v___y_6775_);
v_env_6785_ = lean_ctor_get(v___x_6784_, 0);
v_nextMacroScope_6786_ = lean_ctor_get(v___x_6784_, 1);
v_auxDeclNGen_6787_ = lean_ctor_get(v___x_6784_, 3);
v_traceState_6788_ = lean_ctor_get(v___x_6784_, 4);
v_cache_6789_ = lean_ctor_get(v___x_6784_, 5);
v_messages_6790_ = lean_ctor_get(v___x_6784_, 6);
v_infoState_6791_ = lean_ctor_get(v___x_6784_, 7);
v_snapshotTasks_6792_ = lean_ctor_get(v___x_6784_, 8);
v_isSharedCheck_6808_ = !lean_is_exclusive(v___x_6784_);
if (v_isSharedCheck_6808_ == 0)
{
lean_object* v_unused_6809_; 
v_unused_6809_ = lean_ctor_get(v___x_6784_, 2);
lean_dec(v_unused_6809_);
v___x_6794_ = v___x_6784_;
v_isShared_6795_ = v_isSharedCheck_6808_;
goto v_resetjp_6793_;
}
else
{
lean_inc(v_snapshotTasks_6792_);
lean_inc(v_infoState_6791_);
lean_inc(v_messages_6790_);
lean_inc(v_cache_6789_);
lean_inc(v_traceState_6788_);
lean_inc(v_auxDeclNGen_6787_);
lean_inc(v_nextMacroScope_6786_);
lean_inc(v_env_6785_);
lean_dec(v___x_6784_);
v___x_6794_ = lean_box(0);
v_isShared_6795_ = v_isSharedCheck_6808_;
goto v_resetjp_6793_;
}
v_resetjp_6793_:
{
lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; lean_object* v___x_6800_; 
lean_inc(v_idx_6780_);
lean_inc(v_namePrefix_6779_);
v___x_6796_ = l_Lean_Name_num___override(v_namePrefix_6779_, v_idx_6780_);
v___x_6797_ = lean_unsigned_to_nat(1u);
v___x_6798_ = lean_nat_add(v_idx_6780_, v___x_6797_);
lean_dec(v_idx_6780_);
if (v_isShared_6783_ == 0)
{
lean_ctor_set(v___x_6782_, 1, v___x_6798_);
v___x_6800_ = v___x_6782_;
goto v_reusejp_6799_;
}
else
{
lean_object* v_reuseFailAlloc_6807_; 
v_reuseFailAlloc_6807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6807_, 0, v_namePrefix_6779_);
lean_ctor_set(v_reuseFailAlloc_6807_, 1, v___x_6798_);
v___x_6800_ = v_reuseFailAlloc_6807_;
goto v_reusejp_6799_;
}
v_reusejp_6799_:
{
lean_object* v___x_6802_; 
if (v_isShared_6795_ == 0)
{
lean_ctor_set(v___x_6794_, 2, v___x_6800_);
v___x_6802_ = v___x_6794_;
goto v_reusejp_6801_;
}
else
{
lean_object* v_reuseFailAlloc_6806_; 
v_reuseFailAlloc_6806_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6806_, 0, v_env_6785_);
lean_ctor_set(v_reuseFailAlloc_6806_, 1, v_nextMacroScope_6786_);
lean_ctor_set(v_reuseFailAlloc_6806_, 2, v___x_6800_);
lean_ctor_set(v_reuseFailAlloc_6806_, 3, v_auxDeclNGen_6787_);
lean_ctor_set(v_reuseFailAlloc_6806_, 4, v_traceState_6788_);
lean_ctor_set(v_reuseFailAlloc_6806_, 5, v_cache_6789_);
lean_ctor_set(v_reuseFailAlloc_6806_, 6, v_messages_6790_);
lean_ctor_set(v_reuseFailAlloc_6806_, 7, v_infoState_6791_);
lean_ctor_set(v_reuseFailAlloc_6806_, 8, v_snapshotTasks_6792_);
v___x_6802_ = v_reuseFailAlloc_6806_;
goto v_reusejp_6801_;
}
v_reusejp_6801_:
{
lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6805_; 
v___x_6803_ = lean_st_ref_set(v___y_6775_, v___x_6802_);
v___x_6804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6804_, 0, v___x_6796_);
lean_ctor_set(v___x_6804_, 1, v___x_6797_);
v___x_6805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6805_, 0, v___x_6804_);
return v___x_6805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6811_, lean_object* v___y_6812_){
_start:
{
lean_object* v_res_6813_; 
v_res_6813_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6811_);
lean_dec(v___y_6811_);
return v_res_6813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6814_, lean_object* v___y_6815_){
_start:
{
lean_object* v___x_6817_; 
v___x_6817_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6815_);
return v___x_6817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6818_, lean_object* v___y_6819_, lean_object* v___y_6820_){
_start:
{
lean_object* v_res_6821_; 
v_res_6821_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6818_, v___y_6819_);
lean_dec(v___y_6819_);
lean_dec_ref(v___y_6818_);
return v_res_6821_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6822_; lean_object* v___x_6823_; lean_object* v___x_6824_; 
v___x_6822_ = lean_unsigned_to_nat(32u);
v___x_6823_ = lean_mk_empty_array_with_capacity(v___x_6822_);
v___x_6824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6824_, 0, v___x_6823_);
return v___x_6824_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6825_; lean_object* v___x_6826_; lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; 
v___x_6825_ = ((size_t)5ULL);
v___x_6826_ = lean_unsigned_to_nat(0u);
v___x_6827_ = lean_unsigned_to_nat(32u);
v___x_6828_ = lean_mk_empty_array_with_capacity(v___x_6827_);
v___x_6829_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6830_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6830_, 0, v___x_6829_);
lean_ctor_set(v___x_6830_, 1, v___x_6828_);
lean_ctor_set(v___x_6830_, 2, v___x_6826_);
lean_ctor_set(v___x_6830_, 3, v___x_6826_);
lean_ctor_set_usize(v___x_6830_, 4, v___x_6825_);
return v___x_6830_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6831_; lean_object* v___x_6832_; lean_object* v___x_6833_; lean_object* v___x_6834_; 
v___x_6831_ = lean_box(1);
v___x_6832_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6833_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6834_, 0, v___x_6833_);
lean_ctor_set(v___x_6834_, 1, v___x_6832_);
lean_ctor_set(v___x_6834_, 2, v___x_6831_);
return v___x_6834_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6835_, lean_object* v___y_6836_, lean_object* v___y_6837_){
_start:
{
lean_object* v___x_6839_; lean_object* v_env_6840_; lean_object* v_options_6841_; lean_object* v___x_6842_; lean_object* v___x_6843_; lean_object* v___x_6844_; lean_object* v___x_6845_; lean_object* v___x_6846_; 
v___x_6839_ = lean_st_ref_get(v___y_6837_);
v_env_6840_ = lean_ctor_get(v___x_6839_, 0);
lean_inc_ref(v_env_6840_);
lean_dec(v___x_6839_);
v_options_6841_ = lean_ctor_get(v___y_6836_, 2);
v___x_6842_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6843_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6841_);
v___x_6844_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6844_, 0, v_env_6840_);
lean_ctor_set(v___x_6844_, 1, v___x_6842_);
lean_ctor_set(v___x_6844_, 2, v___x_6843_);
lean_ctor_set(v___x_6844_, 3, v_options_6841_);
v___x_6845_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6845_, 0, v___x_6844_);
lean_ctor_set(v___x_6845_, 1, v_msgData_6835_);
v___x_6846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6846_, 0, v___x_6845_);
return v___x_6846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_){
_start:
{
lean_object* v_res_6851_; 
v_res_6851_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6847_, v___y_6848_, v___y_6849_);
lean_dec(v___y_6849_);
lean_dec_ref(v___y_6848_);
return v_res_6851_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6852_, lean_object* v_msgData_6853_, uint8_t v_severity_6854_, uint8_t v_isSilent_6855_, lean_object* v___y_6856_, lean_object* v___y_6857_){
_start:
{
lean_object* v___y_6860_; uint8_t v___y_6861_; lean_object* v___y_6862_; lean_object* v___y_6863_; uint8_t v___y_6864_; lean_object* v___y_6865_; lean_object* v___y_6866_; lean_object* v___y_6867_; lean_object* v___y_6868_; lean_object* v___y_6896_; lean_object* v___y_6897_; uint8_t v___y_6898_; lean_object* v___y_6899_; lean_object* v___y_6900_; uint8_t v___y_6901_; uint8_t v___y_6902_; lean_object* v___y_6903_; lean_object* v___y_6921_; lean_object* v___y_6922_; uint8_t v___y_6923_; uint8_t v___y_6924_; lean_object* v___y_6925_; uint8_t v___y_6926_; lean_object* v___y_6927_; lean_object* v___y_6928_; lean_object* v___y_6932_; uint8_t v___y_6933_; lean_object* v___y_6934_; lean_object* v___y_6935_; lean_object* v___y_6936_; uint8_t v___y_6937_; uint8_t v___y_6938_; uint8_t v___x_6943_; lean_object* v___y_6945_; uint8_t v___y_6946_; lean_object* v___y_6947_; lean_object* v___y_6948_; lean_object* v___y_6949_; uint8_t v___y_6950_; uint8_t v___y_6951_; uint8_t v___y_6953_; uint8_t v___x_6968_; 
v___x_6943_ = 2;
v___x_6968_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6854_, v___x_6943_);
if (v___x_6968_ == 0)
{
v___y_6953_ = v___x_6968_;
goto v___jp_6952_;
}
else
{
uint8_t v___x_6969_; 
lean_inc_ref(v_msgData_6853_);
v___x_6969_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6853_);
v___y_6953_ = v___x_6969_;
goto v___jp_6952_;
}
v___jp_6859_:
{
lean_object* v___x_6869_; lean_object* v_currNamespace_6870_; lean_object* v_openDecls_6871_; lean_object* v_env_6872_; lean_object* v_nextMacroScope_6873_; lean_object* v_ngen_6874_; lean_object* v_auxDeclNGen_6875_; lean_object* v_traceState_6876_; lean_object* v_cache_6877_; lean_object* v_messages_6878_; lean_object* v_infoState_6879_; lean_object* v_snapshotTasks_6880_; lean_object* v___x_6882_; uint8_t v_isShared_6883_; uint8_t v_isSharedCheck_6894_; 
v___x_6869_ = lean_st_ref_take(v___y_6868_);
v_currNamespace_6870_ = lean_ctor_get(v___y_6867_, 6);
v_openDecls_6871_ = lean_ctor_get(v___y_6867_, 7);
v_env_6872_ = lean_ctor_get(v___x_6869_, 0);
v_nextMacroScope_6873_ = lean_ctor_get(v___x_6869_, 1);
v_ngen_6874_ = lean_ctor_get(v___x_6869_, 2);
v_auxDeclNGen_6875_ = lean_ctor_get(v___x_6869_, 3);
v_traceState_6876_ = lean_ctor_get(v___x_6869_, 4);
v_cache_6877_ = lean_ctor_get(v___x_6869_, 5);
v_messages_6878_ = lean_ctor_get(v___x_6869_, 6);
v_infoState_6879_ = lean_ctor_get(v___x_6869_, 7);
v_snapshotTasks_6880_ = lean_ctor_get(v___x_6869_, 8);
v_isSharedCheck_6894_ = !lean_is_exclusive(v___x_6869_);
if (v_isSharedCheck_6894_ == 0)
{
v___x_6882_ = v___x_6869_;
v_isShared_6883_ = v_isSharedCheck_6894_;
goto v_resetjp_6881_;
}
else
{
lean_inc(v_snapshotTasks_6880_);
lean_inc(v_infoState_6879_);
lean_inc(v_messages_6878_);
lean_inc(v_cache_6877_);
lean_inc(v_traceState_6876_);
lean_inc(v_auxDeclNGen_6875_);
lean_inc(v_ngen_6874_);
lean_inc(v_nextMacroScope_6873_);
lean_inc(v_env_6872_);
lean_dec(v___x_6869_);
v___x_6882_ = lean_box(0);
v_isShared_6883_ = v_isSharedCheck_6894_;
goto v_resetjp_6881_;
}
v_resetjp_6881_:
{
lean_object* v___x_6884_; lean_object* v___x_6885_; lean_object* v___x_6886_; lean_object* v___x_6887_; lean_object* v___x_6889_; 
lean_inc(v_openDecls_6871_);
lean_inc(v_currNamespace_6870_);
v___x_6884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6884_, 0, v_currNamespace_6870_);
lean_ctor_set(v___x_6884_, 1, v_openDecls_6871_);
v___x_6885_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6885_, 0, v___x_6884_);
lean_ctor_set(v___x_6885_, 1, v___y_6866_);
lean_inc_ref(v___y_6865_);
lean_inc_ref(v___y_6862_);
v___x_6886_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6886_, 0, v___y_6862_);
lean_ctor_set(v___x_6886_, 1, v___y_6863_);
lean_ctor_set(v___x_6886_, 2, v___y_6860_);
lean_ctor_set(v___x_6886_, 3, v___y_6865_);
lean_ctor_set(v___x_6886_, 4, v___x_6885_);
lean_ctor_set_uint8(v___x_6886_, sizeof(void*)*5, v___y_6864_);
lean_ctor_set_uint8(v___x_6886_, sizeof(void*)*5 + 1, v___y_6861_);
lean_ctor_set_uint8(v___x_6886_, sizeof(void*)*5 + 2, v_isSilent_6855_);
v___x_6887_ = l_Lean_MessageLog_add(v___x_6886_, v_messages_6878_);
if (v_isShared_6883_ == 0)
{
lean_ctor_set(v___x_6882_, 6, v___x_6887_);
v___x_6889_ = v___x_6882_;
goto v_reusejp_6888_;
}
else
{
lean_object* v_reuseFailAlloc_6893_; 
v_reuseFailAlloc_6893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_env_6872_);
lean_ctor_set(v_reuseFailAlloc_6893_, 1, v_nextMacroScope_6873_);
lean_ctor_set(v_reuseFailAlloc_6893_, 2, v_ngen_6874_);
lean_ctor_set(v_reuseFailAlloc_6893_, 3, v_auxDeclNGen_6875_);
lean_ctor_set(v_reuseFailAlloc_6893_, 4, v_traceState_6876_);
lean_ctor_set(v_reuseFailAlloc_6893_, 5, v_cache_6877_);
lean_ctor_set(v_reuseFailAlloc_6893_, 6, v___x_6887_);
lean_ctor_set(v_reuseFailAlloc_6893_, 7, v_infoState_6879_);
lean_ctor_set(v_reuseFailAlloc_6893_, 8, v_snapshotTasks_6880_);
v___x_6889_ = v_reuseFailAlloc_6893_;
goto v_reusejp_6888_;
}
v_reusejp_6888_:
{
lean_object* v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; 
v___x_6890_ = lean_st_ref_set(v___y_6868_, v___x_6889_);
v___x_6891_ = lean_box(0);
v___x_6892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6892_, 0, v___x_6891_);
return v___x_6892_;
}
}
}
v___jp_6895_:
{
lean_object* v___x_6904_; lean_object* v___x_6905_; lean_object* v_a_6906_; lean_object* v___x_6908_; uint8_t v_isShared_6909_; uint8_t v_isSharedCheck_6919_; 
v___x_6904_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6853_);
v___x_6905_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6904_, v___y_6856_, v___y_6857_);
v_a_6906_ = lean_ctor_get(v___x_6905_, 0);
v_isSharedCheck_6919_ = !lean_is_exclusive(v___x_6905_);
if (v_isSharedCheck_6919_ == 0)
{
v___x_6908_ = v___x_6905_;
v_isShared_6909_ = v_isSharedCheck_6919_;
goto v_resetjp_6907_;
}
else
{
lean_inc(v_a_6906_);
lean_dec(v___x_6905_);
v___x_6908_ = lean_box(0);
v_isShared_6909_ = v_isSharedCheck_6919_;
goto v_resetjp_6907_;
}
v_resetjp_6907_:
{
lean_object* v___x_6910_; lean_object* v___x_6911_; lean_object* v___x_6912_; lean_object* v___x_6913_; 
lean_inc_ref_n(v___y_6899_, 2);
v___x_6910_ = l_Lean_FileMap_toPosition(v___y_6899_, v___y_6897_);
lean_dec(v___y_6897_);
v___x_6911_ = l_Lean_FileMap_toPosition(v___y_6899_, v___y_6903_);
lean_dec(v___y_6903_);
v___x_6912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6912_, 0, v___x_6911_);
v___x_6913_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6898_ == 0)
{
lean_del_object(v___x_6908_);
lean_dec_ref(v___y_6896_);
v___y_6860_ = v___x_6912_;
v___y_6861_ = v___y_6901_;
v___y_6862_ = v___y_6900_;
v___y_6863_ = v___x_6910_;
v___y_6864_ = v___y_6902_;
v___y_6865_ = v___x_6913_;
v___y_6866_ = v_a_6906_;
v___y_6867_ = v___y_6856_;
v___y_6868_ = v___y_6857_;
goto v___jp_6859_;
}
else
{
uint8_t v___x_6914_; 
lean_inc(v_a_6906_);
v___x_6914_ = l_Lean_MessageData_hasTag(v___y_6896_, v_a_6906_);
if (v___x_6914_ == 0)
{
lean_object* v___x_6915_; lean_object* v___x_6917_; 
lean_dec_ref_known(v___x_6912_, 1);
lean_dec_ref(v___x_6910_);
lean_dec(v_a_6906_);
v___x_6915_ = lean_box(0);
if (v_isShared_6909_ == 0)
{
lean_ctor_set(v___x_6908_, 0, v___x_6915_);
v___x_6917_ = v___x_6908_;
goto v_reusejp_6916_;
}
else
{
lean_object* v_reuseFailAlloc_6918_; 
v_reuseFailAlloc_6918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6918_, 0, v___x_6915_);
v___x_6917_ = v_reuseFailAlloc_6918_;
goto v_reusejp_6916_;
}
v_reusejp_6916_:
{
return v___x_6917_;
}
}
else
{
lean_del_object(v___x_6908_);
v___y_6860_ = v___x_6912_;
v___y_6861_ = v___y_6901_;
v___y_6862_ = v___y_6900_;
v___y_6863_ = v___x_6910_;
v___y_6864_ = v___y_6902_;
v___y_6865_ = v___x_6913_;
v___y_6866_ = v_a_6906_;
v___y_6867_ = v___y_6856_;
v___y_6868_ = v___y_6857_;
goto v___jp_6859_;
}
}
}
}
v___jp_6920_:
{
lean_object* v___x_6929_; 
v___x_6929_ = l_Lean_Syntax_getTailPos_x3f(v___y_6927_, v___y_6926_);
lean_dec(v___y_6927_);
if (lean_obj_tag(v___x_6929_) == 0)
{
lean_inc(v___y_6928_);
v___y_6896_ = v___y_6921_;
v___y_6897_ = v___y_6928_;
v___y_6898_ = v___y_6923_;
v___y_6899_ = v___y_6922_;
v___y_6900_ = v___y_6925_;
v___y_6901_ = v___y_6924_;
v___y_6902_ = v___y_6926_;
v___y_6903_ = v___y_6928_;
goto v___jp_6895_;
}
else
{
lean_object* v_val_6930_; 
v_val_6930_ = lean_ctor_get(v___x_6929_, 0);
lean_inc(v_val_6930_);
lean_dec_ref_known(v___x_6929_, 1);
v___y_6896_ = v___y_6921_;
v___y_6897_ = v___y_6928_;
v___y_6898_ = v___y_6923_;
v___y_6899_ = v___y_6922_;
v___y_6900_ = v___y_6925_;
v___y_6901_ = v___y_6924_;
v___y_6902_ = v___y_6926_;
v___y_6903_ = v_val_6930_;
goto v___jp_6895_;
}
}
v___jp_6931_:
{
lean_object* v_ref_6939_; lean_object* v___x_6940_; 
v_ref_6939_ = l_Lean_replaceRef(v_ref_6852_, v___y_6936_);
v___x_6940_ = l_Lean_Syntax_getPos_x3f(v_ref_6939_, v___y_6937_);
if (lean_obj_tag(v___x_6940_) == 0)
{
lean_object* v___x_6941_; 
v___x_6941_ = lean_unsigned_to_nat(0u);
v___y_6921_ = v___y_6932_;
v___y_6922_ = v___y_6934_;
v___y_6923_ = v___y_6933_;
v___y_6924_ = v___y_6938_;
v___y_6925_ = v___y_6935_;
v___y_6926_ = v___y_6937_;
v___y_6927_ = v_ref_6939_;
v___y_6928_ = v___x_6941_;
goto v___jp_6920_;
}
else
{
lean_object* v_val_6942_; 
v_val_6942_ = lean_ctor_get(v___x_6940_, 0);
lean_inc(v_val_6942_);
lean_dec_ref_known(v___x_6940_, 1);
v___y_6921_ = v___y_6932_;
v___y_6922_ = v___y_6934_;
v___y_6923_ = v___y_6933_;
v___y_6924_ = v___y_6938_;
v___y_6925_ = v___y_6935_;
v___y_6926_ = v___y_6937_;
v___y_6927_ = v_ref_6939_;
v___y_6928_ = v_val_6942_;
goto v___jp_6920_;
}
}
v___jp_6944_:
{
if (v___y_6951_ == 0)
{
v___y_6932_ = v___y_6949_;
v___y_6933_ = v___y_6946_;
v___y_6934_ = v___y_6945_;
v___y_6935_ = v___y_6947_;
v___y_6936_ = v___y_6948_;
v___y_6937_ = v___y_6950_;
v___y_6938_ = v_severity_6854_;
goto v___jp_6931_;
}
else
{
v___y_6932_ = v___y_6949_;
v___y_6933_ = v___y_6946_;
v___y_6934_ = v___y_6945_;
v___y_6935_ = v___y_6947_;
v___y_6936_ = v___y_6948_;
v___y_6937_ = v___y_6950_;
v___y_6938_ = v___x_6943_;
goto v___jp_6931_;
}
}
v___jp_6952_:
{
if (v___y_6953_ == 0)
{
lean_object* v_fileName_6954_; lean_object* v_fileMap_6955_; lean_object* v_options_6956_; lean_object* v_ref_6957_; uint8_t v_suppressElabErrors_6958_; lean_object* v___x_6959_; lean_object* v___x_6960_; lean_object* v___f_6961_; uint8_t v___x_6962_; uint8_t v___x_6963_; 
v_fileName_6954_ = lean_ctor_get(v___y_6856_, 0);
v_fileMap_6955_ = lean_ctor_get(v___y_6856_, 1);
v_options_6956_ = lean_ctor_get(v___y_6856_, 2);
v_ref_6957_ = lean_ctor_get(v___y_6856_, 5);
v_suppressElabErrors_6958_ = lean_ctor_get_uint8(v___y_6856_, sizeof(void*)*14 + 1);
v___x_6959_ = lean_box(v___y_6953_);
v___x_6960_ = lean_box(v_suppressElabErrors_6958_);
v___f_6961_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6961_, 0, v___x_6959_);
lean_closure_set(v___f_6961_, 1, v___x_6960_);
v___x_6962_ = 1;
v___x_6963_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6854_, v___x_6962_);
if (v___x_6963_ == 0)
{
v___y_6945_ = v_fileMap_6955_;
v___y_6946_ = v_suppressElabErrors_6958_;
v___y_6947_ = v_fileName_6954_;
v___y_6948_ = v_ref_6957_;
v___y_6949_ = v___f_6961_;
v___y_6950_ = v___y_6953_;
v___y_6951_ = v___x_6963_;
goto v___jp_6944_;
}
else
{
lean_object* v___x_6964_; uint8_t v___x_6965_; 
v___x_6964_ = l_Lean_warningAsError;
v___x_6965_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6956_, v___x_6964_);
v___y_6945_ = v_fileMap_6955_;
v___y_6946_ = v_suppressElabErrors_6958_;
v___y_6947_ = v_fileName_6954_;
v___y_6948_ = v_ref_6957_;
v___y_6949_ = v___f_6961_;
v___y_6950_ = v___y_6953_;
v___y_6951_ = v___x_6965_;
goto v___jp_6944_;
}
}
else
{
lean_object* v___x_6966_; lean_object* v___x_6967_; 
lean_dec_ref(v_msgData_6853_);
v___x_6966_ = lean_box(0);
v___x_6967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6967_, 0, v___x_6966_);
return v___x_6967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6970_, lean_object* v_msgData_6971_, lean_object* v_severity_6972_, lean_object* v_isSilent_6973_, lean_object* v___y_6974_, lean_object* v___y_6975_, lean_object* v___y_6976_){
_start:
{
uint8_t v_severity_boxed_6977_; uint8_t v_isSilent_boxed_6978_; lean_object* v_res_6979_; 
v_severity_boxed_6977_ = lean_unbox(v_severity_6972_);
v_isSilent_boxed_6978_ = lean_unbox(v_isSilent_6973_);
v_res_6979_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6970_, v_msgData_6971_, v_severity_boxed_6977_, v_isSilent_boxed_6978_, v___y_6974_, v___y_6975_);
lean_dec(v___y_6975_);
lean_dec_ref(v___y_6974_);
lean_dec(v_ref_6970_);
return v_res_6979_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6980_, uint8_t v_severity_6981_, uint8_t v_isSilent_6982_, lean_object* v___y_6983_, lean_object* v___y_6984_){
_start:
{
lean_object* v_ref_6986_; lean_object* v___x_6987_; 
v_ref_6986_ = lean_ctor_get(v___y_6983_, 5);
v___x_6987_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6986_, v_msgData_6980_, v_severity_6981_, v_isSilent_6982_, v___y_6983_, v___y_6984_);
return v___x_6987_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6988_, lean_object* v_severity_6989_, lean_object* v_isSilent_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_){
_start:
{
uint8_t v_severity_boxed_6994_; uint8_t v_isSilent_boxed_6995_; lean_object* v_res_6996_; 
v_severity_boxed_6994_ = lean_unbox(v_severity_6989_);
v_isSilent_boxed_6995_ = lean_unbox(v_isSilent_6990_);
v_res_6996_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6988_, v_severity_boxed_6994_, v_isSilent_boxed_6995_, v___y_6991_, v___y_6992_);
lean_dec(v___y_6992_);
lean_dec_ref(v___y_6991_);
return v_res_6996_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_){
_start:
{
uint8_t v___x_7001_; uint8_t v___x_7002_; lean_object* v___x_7003_; 
v___x_7001_ = 2;
v___x_7002_ = 0;
v___x_7003_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6997_, v___x_7001_, v___x_7002_, v___y_6998_, v___y_6999_);
return v___x_7003_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_){
_start:
{
lean_object* v_res_7008_; 
v_res_7008_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_7004_, v___y_7005_, v___y_7006_);
lean_dec(v___y_7006_);
lean_dec_ref(v___y_7005_);
return v_res_7008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_){
_start:
{
lean_object* v_module_7013_; lean_object* v_const_7014_; lean_object* v_exception_7015_; lean_object* v___x_7016_; lean_object* v___x_7017_; lean_object* v___x_7018_; lean_object* v___x_7019_; lean_object* v___x_7020_; lean_object* v___x_7021_; lean_object* v___x_7022_; lean_object* v___x_7023_; lean_object* v___x_7024_; lean_object* v___x_7025_; lean_object* v___x_7026_; lean_object* v___x_7027_; 
v_module_7013_ = lean_ctor_get(v_f_7009_, 0);
lean_inc(v_module_7013_);
v_const_7014_ = lean_ctor_get(v_f_7009_, 1);
lean_inc(v_const_7014_);
v_exception_7015_ = lean_ctor_get(v_f_7009_, 2);
lean_inc_ref(v_exception_7015_);
lean_dec_ref(v_f_7009_);
v___x_7016_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_7017_ = l_Lean_MessageData_ofName(v_const_7014_);
v___x_7018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7018_, 0, v___x_7016_);
lean_ctor_set(v___x_7018_, 1, v___x_7017_);
v___x_7019_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_7020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7020_, 0, v___x_7018_);
lean_ctor_set(v___x_7020_, 1, v___x_7019_);
v___x_7021_ = l_Lean_MessageData_ofName(v_module_7013_);
v___x_7022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7022_, 0, v___x_7020_);
lean_ctor_set(v___x_7022_, 1, v___x_7021_);
v___x_7023_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_7024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7024_, 0, v___x_7022_);
lean_ctor_set(v___x_7024_, 1, v___x_7023_);
v___x_7025_ = l_Lean_Exception_toMessageData(v_exception_7015_);
v___x_7026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7026_, 0, v___x_7024_);
lean_ctor_set(v___x_7026_, 1, v___x_7025_);
v___x_7027_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_7026_, v___y_7010_, v___y_7011_);
return v___x_7027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_){
_start:
{
lean_object* v_res_7032_; 
v_res_7032_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_7028_, v___y_7029_, v___y_7030_);
lean_dec(v___y_7030_);
lean_dec_ref(v___y_7029_);
return v_res_7032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_7033_, size_t v_i_7034_, size_t v_stop_7035_, lean_object* v_b_7036_, lean_object* v___y_7037_, lean_object* v___y_7038_){
_start:
{
uint8_t v___x_7040_; 
v___x_7040_ = lean_usize_dec_eq(v_i_7034_, v_stop_7035_);
if (v___x_7040_ == 0)
{
lean_object* v___x_7041_; lean_object* v___x_7042_; 
v___x_7041_ = lean_array_uget_borrowed(v_as_7033_, v_i_7034_);
lean_inc(v___x_7041_);
v___x_7042_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_7041_, v___y_7037_, v___y_7038_);
if (lean_obj_tag(v___x_7042_) == 0)
{
lean_object* v_a_7043_; size_t v___x_7044_; size_t v___x_7045_; 
v_a_7043_ = lean_ctor_get(v___x_7042_, 0);
lean_inc(v_a_7043_);
lean_dec_ref_known(v___x_7042_, 1);
v___x_7044_ = ((size_t)1ULL);
v___x_7045_ = lean_usize_add(v_i_7034_, v___x_7044_);
v_i_7034_ = v___x_7045_;
v_b_7036_ = v_a_7043_;
goto _start;
}
else
{
return v___x_7042_;
}
}
else
{
lean_object* v___x_7047_; 
v___x_7047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7047_, 0, v_b_7036_);
return v___x_7047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7048_, lean_object* v_i_7049_, lean_object* v_stop_7050_, lean_object* v_b_7051_, lean_object* v___y_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_){
_start:
{
size_t v_i_boxed_7055_; size_t v_stop_boxed_7056_; lean_object* v_res_7057_; 
v_i_boxed_7055_ = lean_unbox_usize(v_i_7049_);
lean_dec(v_i_7049_);
v_stop_boxed_7056_ = lean_unbox_usize(v_stop_7050_);
lean_dec(v_stop_7050_);
v_res_7057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7048_, v_i_boxed_7055_, v_stop_boxed_7056_, v_b_7051_, v___y_7052_, v___y_7053_);
lean_dec(v___y_7053_);
lean_dec_ref(v___y_7052_);
lean_dec_ref(v_as_7048_);
return v_res_7057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7058_, lean_object* v_a_7059_, lean_object* v_a_7060_){
_start:
{
lean_object* v___x_7062_; lean_object* v___x_7063_; lean_object* v_a_7064_; lean_object* v___x_7066_; uint8_t v_isShared_7067_; uint8_t v_isSharedCheck_7098_; 
v___x_7062_ = lean_st_ref_get(v_a_7060_);
v___x_7063_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7060_);
v_a_7064_ = lean_ctor_get(v___x_7063_, 0);
v_isSharedCheck_7098_ = !lean_is_exclusive(v___x_7063_);
if (v_isSharedCheck_7098_ == 0)
{
v___x_7066_ = v___x_7063_;
v_isShared_7067_ = v_isSharedCheck_7098_;
goto v_resetjp_7065_;
}
else
{
lean_inc(v_a_7064_);
lean_dec(v___x_7063_);
v___x_7066_ = lean_box(0);
v_isShared_7067_ = v_isSharedCheck_7098_;
goto v_resetjp_7065_;
}
v_resetjp_7065_:
{
lean_object* v___x_7068_; lean_object* v_env_7069_; lean_object* v___x_7070_; lean_object* v___y_7077_; lean_object* v___x_7086_; lean_object* v___x_7087_; lean_object* v___x_7088_; uint8_t v___x_7089_; 
v___x_7068_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_7069_ = lean_ctor_get(v___x_7062_, 0);
lean_inc_ref(v_env_7069_);
lean_dec(v___x_7062_);
lean_inc_ref(v_a_7059_);
v___x_7070_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7059_, v_a_7064_, v_env_7069_, v___x_7068_, v_entriesForConst_7058_);
v___x_7086_ = lean_st_ref_get(v___x_7068_);
lean_dec(v___x_7068_);
v___x_7087_ = lean_unsigned_to_nat(0u);
v___x_7088_ = lean_array_get_size(v___x_7086_);
v___x_7089_ = lean_nat_dec_lt(v___x_7087_, v___x_7088_);
if (v___x_7089_ == 0)
{
lean_dec(v___x_7086_);
goto v___jp_7071_;
}
else
{
lean_object* v___x_7090_; uint8_t v___x_7091_; 
v___x_7090_ = lean_box(0);
v___x_7091_ = lean_nat_dec_le(v___x_7088_, v___x_7088_);
if (v___x_7091_ == 0)
{
if (v___x_7089_ == 0)
{
lean_dec(v___x_7086_);
goto v___jp_7071_;
}
else
{
size_t v___x_7092_; size_t v___x_7093_; lean_object* v___x_7094_; 
v___x_7092_ = ((size_t)0ULL);
v___x_7093_ = lean_usize_of_nat(v___x_7088_);
v___x_7094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7086_, v___x_7092_, v___x_7093_, v___x_7090_, v_a_7059_, v_a_7060_);
lean_dec(v___x_7086_);
v___y_7077_ = v___x_7094_;
goto v___jp_7076_;
}
}
else
{
size_t v___x_7095_; size_t v___x_7096_; lean_object* v___x_7097_; 
v___x_7095_ = ((size_t)0ULL);
v___x_7096_ = lean_usize_of_nat(v___x_7088_);
v___x_7097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7086_, v___x_7095_, v___x_7096_, v___x_7090_, v_a_7059_, v_a_7060_);
lean_dec(v___x_7086_);
v___y_7077_ = v___x_7097_;
goto v___jp_7076_;
}
}
v___jp_7071_:
{
lean_object* v___x_7072_; lean_object* v___x_7074_; 
v___x_7072_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7070_);
if (v_isShared_7067_ == 0)
{
lean_ctor_set(v___x_7066_, 0, v___x_7072_);
v___x_7074_ = v___x_7066_;
goto v_reusejp_7073_;
}
else
{
lean_object* v_reuseFailAlloc_7075_; 
v_reuseFailAlloc_7075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7075_, 0, v___x_7072_);
v___x_7074_ = v_reuseFailAlloc_7075_;
goto v_reusejp_7073_;
}
v_reusejp_7073_:
{
return v___x_7074_;
}
}
v___jp_7076_:
{
if (lean_obj_tag(v___y_7077_) == 0)
{
lean_dec_ref_known(v___y_7077_, 1);
goto v___jp_7071_;
}
else
{
lean_object* v_a_7078_; lean_object* v___x_7080_; uint8_t v_isShared_7081_; uint8_t v_isSharedCheck_7085_; 
lean_dec_ref(v___x_7070_);
lean_del_object(v___x_7066_);
v_a_7078_ = lean_ctor_get(v___y_7077_, 0);
v_isSharedCheck_7085_ = !lean_is_exclusive(v___y_7077_);
if (v_isSharedCheck_7085_ == 0)
{
v___x_7080_ = v___y_7077_;
v_isShared_7081_ = v_isSharedCheck_7085_;
goto v_resetjp_7079_;
}
else
{
lean_inc(v_a_7078_);
lean_dec(v___y_7077_);
v___x_7080_ = lean_box(0);
v_isShared_7081_ = v_isSharedCheck_7085_;
goto v_resetjp_7079_;
}
v_resetjp_7079_:
{
lean_object* v___x_7083_; 
if (v_isShared_7081_ == 0)
{
v___x_7083_ = v___x_7080_;
goto v_reusejp_7082_;
}
else
{
lean_object* v_reuseFailAlloc_7084_; 
v_reuseFailAlloc_7084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7084_, 0, v_a_7078_);
v___x_7083_ = v_reuseFailAlloc_7084_;
goto v_reusejp_7082_;
}
v_reusejp_7082_:
{
return v___x_7083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7099_, lean_object* v_a_7100_, lean_object* v_a_7101_, lean_object* v_a_7102_){
_start:
{
lean_object* v_res_7103_; 
v_res_7103_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7099_, v_a_7100_, v_a_7101_);
lean_dec(v_a_7101_);
lean_dec_ref(v_a_7100_);
return v_res_7103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7104_, lean_object* v_entriesForConst_7105_, lean_object* v_a_7106_, lean_object* v_a_7107_){
_start:
{
lean_object* v___x_7109_; 
v___x_7109_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7105_, v_a_7106_, v_a_7107_);
return v___x_7109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7110_, lean_object* v_entriesForConst_7111_, lean_object* v_a_7112_, lean_object* v_a_7113_, lean_object* v_a_7114_){
_start:
{
lean_object* v_res_7115_; 
v_res_7115_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7110_, v_entriesForConst_7111_, v_a_7112_, v_a_7113_);
lean_dec(v_a_7113_);
lean_dec_ref(v_a_7112_);
return v_res_7115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7116_, lean_object* v_droppedEntriesRef_7117_, lean_object* v_droppedKeys_7118_, lean_object* v___y_7119_, lean_object* v___y_7120_, lean_object* v___y_7121_, lean_object* v___y_7122_){
_start:
{
lean_object* v_t_7125_; lean_object* v___x_7128_; 
v___x_7128_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7116_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7128_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7117_) == 1)
{
lean_object* v_a_7129_; lean_object* v_val_7130_; lean_object* v___x_7132_; uint8_t v_isShared_7133_; uint8_t v_isSharedCheck_7156_; 
v_a_7129_ = lean_ctor_get(v___x_7128_, 0);
lean_inc(v_a_7129_);
lean_dec_ref_known(v___x_7128_, 1);
v_val_7130_ = lean_ctor_get(v_droppedEntriesRef_7117_, 0);
v_isSharedCheck_7156_ = !lean_is_exclusive(v_droppedEntriesRef_7117_);
if (v_isSharedCheck_7156_ == 0)
{
v___x_7132_ = v_droppedEntriesRef_7117_;
v_isShared_7133_ = v_isSharedCheck_7156_;
goto v_resetjp_7131_;
}
else
{
lean_inc(v_val_7130_);
lean_dec(v_droppedEntriesRef_7117_);
v___x_7132_ = lean_box(0);
v_isShared_7133_ = v_isSharedCheck_7156_;
goto v_resetjp_7131_;
}
v_resetjp_7131_:
{
lean_object* v___x_7134_; 
v___x_7134_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7129_, v_droppedKeys_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
lean_dec(v_droppedKeys_7118_);
if (lean_obj_tag(v___x_7134_) == 0)
{
lean_object* v_a_7135_; lean_object* v_fst_7136_; lean_object* v_snd_7137_; lean_object* v___x_7138_; lean_object* v___y_7140_; 
v_a_7135_ = lean_ctor_get(v___x_7134_, 0);
lean_inc(v_a_7135_);
lean_dec_ref_known(v___x_7134_, 1);
v_fst_7136_ = lean_ctor_get(v_a_7135_, 0);
lean_inc(v_fst_7136_);
v_snd_7137_ = lean_ctor_get(v_a_7135_, 1);
lean_inc(v_snd_7137_);
lean_dec(v_a_7135_);
v___x_7138_ = lean_st_ref_get(v_val_7130_);
if (lean_obj_tag(v___x_7138_) == 0)
{
lean_object* v___x_7146_; 
v___x_7146_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7140_ = v___x_7146_;
goto v___jp_7139_;
}
else
{
lean_object* v_val_7147_; 
v_val_7147_ = lean_ctor_get(v___x_7138_, 0);
lean_inc(v_val_7147_);
lean_dec_ref_known(v___x_7138_, 1);
v___y_7140_ = v_val_7147_;
goto v___jp_7139_;
}
v___jp_7139_:
{
lean_object* v___x_7141_; lean_object* v___x_7143_; 
v___x_7141_ = l_Array_append___redArg(v___y_7140_, v_fst_7136_);
lean_dec(v_fst_7136_);
if (v_isShared_7133_ == 0)
{
lean_ctor_set(v___x_7132_, 0, v___x_7141_);
v___x_7143_ = v___x_7132_;
goto v_reusejp_7142_;
}
else
{
lean_object* v_reuseFailAlloc_7145_; 
v_reuseFailAlloc_7145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7145_, 0, v___x_7141_);
v___x_7143_ = v_reuseFailAlloc_7145_;
goto v_reusejp_7142_;
}
v_reusejp_7142_:
{
lean_object* v___x_7144_; 
v___x_7144_ = lean_st_ref_set(v_val_7130_, v___x_7143_);
lean_dec(v_val_7130_);
v_t_7125_ = v_snd_7137_;
goto v___jp_7124_;
}
}
}
else
{
lean_object* v_a_7148_; lean_object* v___x_7150_; uint8_t v_isShared_7151_; uint8_t v_isSharedCheck_7155_; 
lean_del_object(v___x_7132_);
lean_dec(v_val_7130_);
v_a_7148_ = lean_ctor_get(v___x_7134_, 0);
v_isSharedCheck_7155_ = !lean_is_exclusive(v___x_7134_);
if (v_isSharedCheck_7155_ == 0)
{
v___x_7150_ = v___x_7134_;
v_isShared_7151_ = v_isSharedCheck_7155_;
goto v_resetjp_7149_;
}
else
{
lean_inc(v_a_7148_);
lean_dec(v___x_7134_);
v___x_7150_ = lean_box(0);
v_isShared_7151_ = v_isSharedCheck_7155_;
goto v_resetjp_7149_;
}
v_resetjp_7149_:
{
lean_object* v___x_7153_; 
if (v_isShared_7151_ == 0)
{
v___x_7153_ = v___x_7150_;
goto v_reusejp_7152_;
}
else
{
lean_object* v_reuseFailAlloc_7154_; 
v_reuseFailAlloc_7154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7154_, 0, v_a_7148_);
v___x_7153_ = v_reuseFailAlloc_7154_;
goto v_reusejp_7152_;
}
v_reusejp_7152_:
{
return v___x_7153_;
}
}
}
}
}
else
{
lean_object* v_a_7157_; lean_object* v___x_7158_; 
lean_dec(v_droppedEntriesRef_7117_);
v_a_7157_ = lean_ctor_get(v___x_7128_, 0);
lean_inc(v_a_7157_);
lean_dec_ref_known(v___x_7128_, 1);
v___x_7158_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7157_, v_droppedKeys_7118_, v___y_7119_, v___y_7120_, v___y_7121_, v___y_7122_);
if (lean_obj_tag(v___x_7158_) == 0)
{
lean_object* v_a_7159_; 
v_a_7159_ = lean_ctor_get(v___x_7158_, 0);
lean_inc(v_a_7159_);
lean_dec_ref_known(v___x_7158_, 1);
v_t_7125_ = v_a_7159_;
goto v___jp_7124_;
}
else
{
lean_object* v_a_7160_; lean_object* v___x_7162_; uint8_t v_isShared_7163_; uint8_t v_isSharedCheck_7167_; 
v_a_7160_ = lean_ctor_get(v___x_7158_, 0);
v_isSharedCheck_7167_ = !lean_is_exclusive(v___x_7158_);
if (v_isSharedCheck_7167_ == 0)
{
v___x_7162_ = v___x_7158_;
v_isShared_7163_ = v_isSharedCheck_7167_;
goto v_resetjp_7161_;
}
else
{
lean_inc(v_a_7160_);
lean_dec(v___x_7158_);
v___x_7162_ = lean_box(0);
v_isShared_7163_ = v_isSharedCheck_7167_;
goto v_resetjp_7161_;
}
v_resetjp_7161_:
{
lean_object* v___x_7165_; 
if (v_isShared_7163_ == 0)
{
v___x_7165_ = v___x_7162_;
goto v_reusejp_7164_;
}
else
{
lean_object* v_reuseFailAlloc_7166_; 
v_reuseFailAlloc_7166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7166_, 0, v_a_7160_);
v___x_7165_ = v_reuseFailAlloc_7166_;
goto v_reusejp_7164_;
}
v_reusejp_7164_:
{
return v___x_7165_;
}
}
}
}
}
else
{
lean_object* v_a_7168_; lean_object* v___x_7170_; uint8_t v_isShared_7171_; uint8_t v_isSharedCheck_7175_; 
lean_dec(v_droppedKeys_7118_);
lean_dec(v_droppedEntriesRef_7117_);
v_a_7168_ = lean_ctor_get(v___x_7128_, 0);
v_isSharedCheck_7175_ = !lean_is_exclusive(v___x_7128_);
if (v_isSharedCheck_7175_ == 0)
{
v___x_7170_ = v___x_7128_;
v_isShared_7171_ = v_isSharedCheck_7175_;
goto v_resetjp_7169_;
}
else
{
lean_inc(v_a_7168_);
lean_dec(v___x_7128_);
v___x_7170_ = lean_box(0);
v_isShared_7171_ = v_isSharedCheck_7175_;
goto v_resetjp_7169_;
}
v_resetjp_7169_:
{
lean_object* v___x_7173_; 
if (v_isShared_7171_ == 0)
{
v___x_7173_ = v___x_7170_;
goto v_reusejp_7172_;
}
else
{
lean_object* v_reuseFailAlloc_7174_; 
v_reuseFailAlloc_7174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7174_, 0, v_a_7168_);
v___x_7173_ = v_reuseFailAlloc_7174_;
goto v_reusejp_7172_;
}
v_reusejp_7172_:
{
return v___x_7173_;
}
}
}
v___jp_7124_:
{
lean_object* v___x_7126_; lean_object* v___x_7127_; 
v___x_7126_ = lean_st_mk_ref(v_t_7125_);
v___x_7127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7127_, 0, v___x_7126_);
return v___x_7127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7176_, lean_object* v_droppedEntriesRef_7177_, lean_object* v_droppedKeys_7178_, lean_object* v___y_7179_, lean_object* v___y_7180_, lean_object* v___y_7181_, lean_object* v___y_7182_, lean_object* v___y_7183_){
_start:
{
lean_object* v_res_7184_; 
v_res_7184_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7176_, v_droppedEntriesRef_7177_, v_droppedKeys_7178_, v___y_7179_, v___y_7180_, v___y_7181_, v___y_7182_);
lean_dec(v___y_7182_);
lean_dec_ref(v___y_7181_);
lean_dec(v___y_7180_);
lean_dec_ref(v___y_7179_);
return v_res_7184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7186_, lean_object* v_droppedKeys_7187_, lean_object* v_droppedEntriesRef_7188_, lean_object* v_a_7189_, lean_object* v_a_7190_, lean_object* v_a_7191_, lean_object* v_a_7192_){
_start:
{
lean_object* v_options_7194_; lean_object* v___f_7195_; lean_object* v___x_7196_; lean_object* v___x_7197_; lean_object* v___x_7198_; 
v_options_7194_ = lean_ctor_get(v_a_7191_, 2);
v___f_7195_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7195_, 0, v_entriesForConst_7186_);
lean_closure_set(v___f_7195_, 1, v_droppedEntriesRef_7188_);
lean_closure_set(v___f_7195_, 2, v_droppedKeys_7187_);
v___x_7196_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7197_ = lean_box(0);
v___x_7198_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7196_, v_options_7194_, v___f_7195_, v___x_7197_, v_a_7189_, v_a_7190_, v_a_7191_, v_a_7192_);
return v___x_7198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7199_, lean_object* v_droppedKeys_7200_, lean_object* v_droppedEntriesRef_7201_, lean_object* v_a_7202_, lean_object* v_a_7203_, lean_object* v_a_7204_, lean_object* v_a_7205_, lean_object* v_a_7206_){
_start:
{
lean_object* v_res_7207_; 
v_res_7207_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7199_, v_droppedKeys_7200_, v_droppedEntriesRef_7201_, v_a_7202_, v_a_7203_, v_a_7204_, v_a_7205_);
lean_dec(v_a_7205_);
lean_dec_ref(v_a_7204_);
lean_dec(v_a_7203_);
lean_dec_ref(v_a_7202_);
return v_res_7207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7208_, lean_object* v_entriesForConst_7209_, lean_object* v_droppedKeys_7210_, lean_object* v_droppedEntriesRef_7211_, lean_object* v_a_7212_, lean_object* v_a_7213_, lean_object* v_a_7214_, lean_object* v_a_7215_){
_start:
{
lean_object* v___x_7217_; 
v___x_7217_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7209_, v_droppedKeys_7210_, v_droppedEntriesRef_7211_, v_a_7212_, v_a_7213_, v_a_7214_, v_a_7215_);
return v___x_7217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7218_, lean_object* v_entriesForConst_7219_, lean_object* v_droppedKeys_7220_, lean_object* v_droppedEntriesRef_7221_, lean_object* v_a_7222_, lean_object* v_a_7223_, lean_object* v_a_7224_, lean_object* v_a_7225_, lean_object* v_a_7226_){
_start:
{
lean_object* v_res_7227_; 
v_res_7227_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7218_, v_entriesForConst_7219_, v_droppedKeys_7220_, v_droppedEntriesRef_7221_, v_a_7222_, v_a_7223_, v_a_7224_, v_a_7225_);
lean_dec(v_a_7225_);
lean_dec_ref(v_a_7224_);
lean_dec(v_a_7223_);
lean_dec_ref(v_a_7222_);
return v_res_7227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7228_, lean_object* v_ty_7229_, lean_object* v___y_7230_, lean_object* v___y_7231_, lean_object* v___y_7232_, lean_object* v___y_7233_){
_start:
{
lean_object* v___x_7235_; lean_object* v___x_7236_; 
v___x_7235_ = lean_st_ref_get(v_moduleRef_7228_);
v___x_7236_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7235_, v_ty_7229_, v___y_7230_, v___y_7231_, v___y_7232_, v___y_7233_);
if (lean_obj_tag(v___x_7236_) == 0)
{
lean_object* v_a_7237_; lean_object* v___x_7239_; uint8_t v_isShared_7240_; uint8_t v_isSharedCheck_7247_; 
v_a_7237_ = lean_ctor_get(v___x_7236_, 0);
v_isSharedCheck_7247_ = !lean_is_exclusive(v___x_7236_);
if (v_isSharedCheck_7247_ == 0)
{
v___x_7239_ = v___x_7236_;
v_isShared_7240_ = v_isSharedCheck_7247_;
goto v_resetjp_7238_;
}
else
{
lean_inc(v_a_7237_);
lean_dec(v___x_7236_);
v___x_7239_ = lean_box(0);
v_isShared_7240_ = v_isSharedCheck_7247_;
goto v_resetjp_7238_;
}
v_resetjp_7238_:
{
lean_object* v_fst_7241_; lean_object* v_snd_7242_; lean_object* v___x_7243_; lean_object* v___x_7245_; 
v_fst_7241_ = lean_ctor_get(v_a_7237_, 0);
lean_inc(v_fst_7241_);
v_snd_7242_ = lean_ctor_get(v_a_7237_, 1);
lean_inc(v_snd_7242_);
lean_dec(v_a_7237_);
v___x_7243_ = lean_st_ref_set(v_moduleRef_7228_, v_snd_7242_);
if (v_isShared_7240_ == 0)
{
lean_ctor_set(v___x_7239_, 0, v_fst_7241_);
v___x_7245_ = v___x_7239_;
goto v_reusejp_7244_;
}
else
{
lean_object* v_reuseFailAlloc_7246_; 
v_reuseFailAlloc_7246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7246_, 0, v_fst_7241_);
v___x_7245_ = v_reuseFailAlloc_7246_;
goto v_reusejp_7244_;
}
v_reusejp_7244_:
{
return v___x_7245_;
}
}
}
else
{
lean_object* v_a_7248_; lean_object* v___x_7250_; uint8_t v_isShared_7251_; uint8_t v_isSharedCheck_7255_; 
v_a_7248_ = lean_ctor_get(v___x_7236_, 0);
v_isSharedCheck_7255_ = !lean_is_exclusive(v___x_7236_);
if (v_isSharedCheck_7255_ == 0)
{
v___x_7250_ = v___x_7236_;
v_isShared_7251_ = v_isSharedCheck_7255_;
goto v_resetjp_7249_;
}
else
{
lean_inc(v_a_7248_);
lean_dec(v___x_7236_);
v___x_7250_ = lean_box(0);
v_isShared_7251_ = v_isSharedCheck_7255_;
goto v_resetjp_7249_;
}
v_resetjp_7249_:
{
lean_object* v___x_7253_; 
if (v_isShared_7251_ == 0)
{
v___x_7253_ = v___x_7250_;
goto v_reusejp_7252_;
}
else
{
lean_object* v_reuseFailAlloc_7254_; 
v_reuseFailAlloc_7254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7254_, 0, v_a_7248_);
v___x_7253_ = v_reuseFailAlloc_7254_;
goto v_reusejp_7252_;
}
v_reusejp_7252_:
{
return v___x_7253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7256_, lean_object* v_ty_7257_, lean_object* v___y_7258_, lean_object* v___y_7259_, lean_object* v___y_7260_, lean_object* v___y_7261_, lean_object* v___y_7262_){
_start:
{
lean_object* v_res_7263_; 
v_res_7263_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7256_, v_ty_7257_, v___y_7258_, v___y_7259_, v___y_7260_, v___y_7261_);
lean_dec(v___y_7261_);
lean_dec_ref(v___y_7260_);
lean_dec(v___y_7259_);
lean_dec_ref(v___y_7258_);
lean_dec(v_moduleRef_7256_);
return v_res_7263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7265_, lean_object* v_ty_7266_, lean_object* v_a_7267_, lean_object* v_a_7268_, lean_object* v_a_7269_, lean_object* v_a_7270_){
_start:
{
lean_object* v_options_7272_; lean_object* v___f_7273_; lean_object* v___x_7274_; lean_object* v___x_7275_; lean_object* v___x_7276_; 
v_options_7272_ = lean_ctor_get(v_a_7269_, 2);
v___f_7273_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7273_, 0, v_moduleRef_7265_);
lean_closure_set(v___f_7273_, 1, v_ty_7266_);
v___x_7274_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7275_ = lean_box(0);
v___x_7276_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7274_, v_options_7272_, v___f_7273_, v___x_7275_, v_a_7267_, v_a_7268_, v_a_7269_, v_a_7270_);
return v___x_7276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7277_, lean_object* v_ty_7278_, lean_object* v_a_7279_, lean_object* v_a_7280_, lean_object* v_a_7281_, lean_object* v_a_7282_, lean_object* v_a_7283_){
_start:
{
lean_object* v_res_7284_; 
v_res_7284_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7277_, v_ty_7278_, v_a_7279_, v_a_7280_, v_a_7281_, v_a_7282_);
lean_dec(v_a_7282_);
lean_dec_ref(v_a_7281_);
lean_dec(v_a_7280_);
lean_dec_ref(v_a_7279_);
return v_res_7284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7285_, lean_object* v_moduleRef_7286_, lean_object* v_ty_7287_, lean_object* v_a_7288_, lean_object* v_a_7289_, lean_object* v_a_7290_, lean_object* v_a_7291_){
_start:
{
lean_object* v___x_7293_; 
v___x_7293_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7286_, v_ty_7287_, v_a_7288_, v_a_7289_, v_a_7290_, v_a_7291_);
return v___x_7293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7294_, lean_object* v_moduleRef_7295_, lean_object* v_ty_7296_, lean_object* v_a_7297_, lean_object* v_a_7298_, lean_object* v_a_7299_, lean_object* v_a_7300_, lean_object* v_a_7301_){
_start:
{
lean_object* v_res_7302_; 
v_res_7302_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7294_, v_moduleRef_7295_, v_ty_7296_, v_a_7297_, v_a_7298_, v_a_7299_, v_a_7300_);
lean_dec(v_a_7300_);
lean_dec_ref(v_a_7299_);
lean_dec(v_a_7298_);
lean_dec_ref(v_a_7297_);
return v_res_7302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7303_, lean_object* v_j_7304_, size_t v_sz_7305_, size_t v_i_7306_, lean_object* v_bs_7307_){
_start:
{
uint8_t v___x_7308_; 
v___x_7308_ = lean_usize_dec_lt(v_i_7306_, v_sz_7305_);
if (v___x_7308_ == 0)
{
lean_dec(v_j_7304_);
lean_dec(v_adjustResult_7303_);
return v_bs_7307_;
}
else
{
lean_object* v_v_7309_; lean_object* v___x_7310_; lean_object* v_bs_x27_7311_; lean_object* v___x_7312_; size_t v___x_7313_; size_t v___x_7314_; lean_object* v___x_7315_; 
v_v_7309_ = lean_array_uget(v_bs_7307_, v_i_7306_);
v___x_7310_ = lean_unsigned_to_nat(0u);
v_bs_x27_7311_ = lean_array_uset(v_bs_7307_, v_i_7306_, v___x_7310_);
lean_inc(v_adjustResult_7303_);
lean_inc(v_j_7304_);
v___x_7312_ = lean_apply_2(v_adjustResult_7303_, v_j_7304_, v_v_7309_);
v___x_7313_ = ((size_t)1ULL);
v___x_7314_ = lean_usize_add(v_i_7306_, v___x_7313_);
v___x_7315_ = lean_array_uset(v_bs_x27_7311_, v_i_7306_, v___x_7312_);
v_i_7306_ = v___x_7314_;
v_bs_7307_ = v___x_7315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7317_, lean_object* v_j_7318_, lean_object* v_sz_7319_, lean_object* v_i_7320_, lean_object* v_bs_7321_){
_start:
{
size_t v_sz_boxed_7322_; size_t v_i_boxed_7323_; lean_object* v_res_7324_; 
v_sz_boxed_7322_ = lean_unbox_usize(v_sz_7319_);
lean_dec(v_sz_7319_);
v_i_boxed_7323_ = lean_unbox_usize(v_i_7320_);
lean_dec(v_i_7320_);
v_res_7324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7317_, v_j_7318_, v_sz_boxed_7322_, v_i_boxed_7323_, v_bs_7321_);
return v_res_7324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7325_, lean_object* v_j_7326_, lean_object* v_as_7327_, size_t v_i_7328_, size_t v_stop_7329_, lean_object* v_b_7330_){
_start:
{
uint8_t v___x_7331_; 
v___x_7331_ = lean_usize_dec_eq(v_i_7328_, v_stop_7329_);
if (v___x_7331_ == 0)
{
lean_object* v___x_7332_; size_t v_sz_7333_; size_t v___x_7334_; lean_object* v___x_7335_; lean_object* v___x_7336_; size_t v___x_7337_; size_t v___x_7338_; 
v___x_7332_ = lean_array_uget_borrowed(v_as_7327_, v_i_7328_);
v_sz_7333_ = lean_array_size(v___x_7332_);
v___x_7334_ = ((size_t)0ULL);
lean_inc(v___x_7332_);
lean_inc(v_j_7326_);
lean_inc(v_adjustResult_7325_);
v___x_7335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7325_, v_j_7326_, v_sz_7333_, v___x_7334_, v___x_7332_);
v___x_7336_ = l_Array_append___redArg(v_b_7330_, v___x_7335_);
lean_dec_ref(v___x_7335_);
v___x_7337_ = ((size_t)1ULL);
v___x_7338_ = lean_usize_add(v_i_7328_, v___x_7337_);
v_i_7328_ = v___x_7338_;
v_b_7330_ = v___x_7336_;
goto _start;
}
else
{
lean_dec(v_j_7326_);
lean_dec(v_adjustResult_7325_);
return v_b_7330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7340_, lean_object* v_j_7341_, lean_object* v_as_7342_, lean_object* v_i_7343_, lean_object* v_stop_7344_, lean_object* v_b_7345_){
_start:
{
size_t v_i_boxed_7346_; size_t v_stop_boxed_7347_; lean_object* v_res_7348_; 
v_i_boxed_7346_ = lean_unbox_usize(v_i_7343_);
lean_dec(v_i_7343_);
v_stop_boxed_7347_ = lean_unbox_usize(v_stop_7344_);
lean_dec(v_stop_7344_);
v_res_7348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7340_, v_j_7341_, v_as_7342_, v_i_boxed_7346_, v_stop_boxed_7347_, v_b_7345_);
lean_dec_ref(v_as_7342_);
return v_res_7348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7349_, lean_object* v_aa_7350_, lean_object* v_adjustResult_7351_, lean_object* v_n_7352_, lean_object* v_j_7353_, lean_object* v_a_7354_){
_start:
{
lean_object* v_zero_7355_; uint8_t v_isZero_7356_; 
v_zero_7355_ = lean_unsigned_to_nat(0u);
v_isZero_7356_ = lean_nat_dec_eq(v_j_7353_, v_zero_7355_);
if (v_isZero_7356_ == 1)
{
lean_dec(v_j_7353_);
lean_dec(v_adjustResult_7351_);
return v_a_7354_;
}
else
{
lean_object* v_one_7357_; lean_object* v_n_7358_; lean_object* v___x_7359_; lean_object* v___x_7360_; lean_object* v_j_7361_; lean_object* v_b_7362_; lean_object* v___x_7363_; uint8_t v___x_7364_; 
v_one_7357_ = lean_unsigned_to_nat(1u);
v_n_7358_ = lean_nat_sub(v_j_7353_, v_one_7357_);
v___x_7359_ = lean_nat_sub(v_n_7352_, v_j_7353_);
lean_dec(v_j_7353_);
v___x_7360_ = lean_nat_sub(v_n_7349_, v_one_7357_);
v_j_7361_ = lean_nat_sub(v___x_7360_, v___x_7359_);
lean_dec(v___x_7359_);
lean_dec(v___x_7360_);
v_b_7362_ = lean_array_fget_borrowed(v_aa_7350_, v_j_7361_);
v___x_7363_ = lean_array_get_size(v_b_7362_);
v___x_7364_ = lean_nat_dec_lt(v_zero_7355_, v___x_7363_);
if (v___x_7364_ == 0)
{
lean_dec(v_j_7361_);
v_j_7353_ = v_n_7358_;
goto _start;
}
else
{
uint8_t v___x_7366_; 
v___x_7366_ = lean_nat_dec_le(v___x_7363_, v___x_7363_);
if (v___x_7366_ == 0)
{
if (v___x_7364_ == 0)
{
lean_dec(v_j_7361_);
v_j_7353_ = v_n_7358_;
goto _start;
}
else
{
size_t v___x_7368_; size_t v___x_7369_; lean_object* v___x_7370_; 
v___x_7368_ = ((size_t)0ULL);
v___x_7369_ = lean_usize_of_nat(v___x_7363_);
lean_inc(v_adjustResult_7351_);
v___x_7370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7351_, v_j_7361_, v_b_7362_, v___x_7368_, v___x_7369_, v_a_7354_);
v_j_7353_ = v_n_7358_;
v_a_7354_ = v___x_7370_;
goto _start;
}
}
else
{
size_t v___x_7372_; size_t v___x_7373_; lean_object* v___x_7374_; 
v___x_7372_ = ((size_t)0ULL);
v___x_7373_ = lean_usize_of_nat(v___x_7363_);
lean_inc(v_adjustResult_7351_);
v___x_7374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7351_, v_j_7361_, v_b_7362_, v___x_7372_, v___x_7373_, v_a_7354_);
v_j_7353_ = v_n_7358_;
v_a_7354_ = v___x_7374_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7376_, lean_object* v_aa_7377_, lean_object* v_adjustResult_7378_, lean_object* v_n_7379_, lean_object* v_j_7380_, lean_object* v_a_7381_){
_start:
{
lean_object* v_res_7382_; 
v_res_7382_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7376_, v_aa_7377_, v_adjustResult_7378_, v_n_7379_, v_j_7380_, v_a_7381_);
lean_dec(v_n_7379_);
lean_dec_ref(v_aa_7377_);
lean_dec(v_n_7376_);
return v_res_7382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7383_, lean_object* v_adjustResult_7384_, lean_object* v_aa_7385_, lean_object* v_n_7386_, lean_object* v_j_7387_, lean_object* v_a_7388_){
_start:
{
lean_object* v_zero_7389_; uint8_t v_isZero_7390_; 
v_zero_7389_ = lean_unsigned_to_nat(0u);
v_isZero_7390_ = lean_nat_dec_eq(v_j_7387_, v_zero_7389_);
if (v_isZero_7390_ == 1)
{
lean_dec(v_adjustResult_7384_);
return v_a_7388_;
}
else
{
lean_object* v_one_7391_; lean_object* v_n_7392_; lean_object* v___x_7393_; lean_object* v___x_7394_; lean_object* v_j_7395_; lean_object* v_b_7396_; lean_object* v___x_7397_; uint8_t v___x_7398_; 
v_one_7391_ = lean_unsigned_to_nat(1u);
v_n_7392_ = lean_nat_sub(v_j_7387_, v_one_7391_);
v___x_7393_ = lean_nat_sub(v_n_7386_, v_j_7387_);
v___x_7394_ = lean_nat_sub(v_n_7383_, v_one_7391_);
v_j_7395_ = lean_nat_sub(v___x_7394_, v___x_7393_);
lean_dec(v___x_7393_);
lean_dec(v___x_7394_);
v_b_7396_ = lean_array_fget_borrowed(v_aa_7385_, v_j_7395_);
v___x_7397_ = lean_array_get_size(v_b_7396_);
v___x_7398_ = lean_nat_dec_lt(v_zero_7389_, v___x_7397_);
if (v___x_7398_ == 0)
{
lean_object* v___x_7399_; 
lean_dec(v_j_7395_);
v___x_7399_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7383_, v_aa_7385_, v_adjustResult_7384_, v_n_7386_, v_n_7392_, v_a_7388_);
return v___x_7399_;
}
else
{
uint8_t v___x_7400_; 
v___x_7400_ = lean_nat_dec_le(v___x_7397_, v___x_7397_);
if (v___x_7400_ == 0)
{
if (v___x_7398_ == 0)
{
lean_object* v___x_7401_; 
lean_dec(v_j_7395_);
v___x_7401_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7383_, v_aa_7385_, v_adjustResult_7384_, v_n_7386_, v_n_7392_, v_a_7388_);
return v___x_7401_;
}
else
{
size_t v___x_7402_; size_t v___x_7403_; lean_object* v___x_7404_; lean_object* v___x_7405_; 
v___x_7402_ = ((size_t)0ULL);
v___x_7403_ = lean_usize_of_nat(v___x_7397_);
lean_inc(v_adjustResult_7384_);
v___x_7404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7384_, v_j_7395_, v_b_7396_, v___x_7402_, v___x_7403_, v_a_7388_);
v___x_7405_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7383_, v_aa_7385_, v_adjustResult_7384_, v_n_7386_, v_n_7392_, v___x_7404_);
return v___x_7405_;
}
}
else
{
size_t v___x_7406_; size_t v___x_7407_; lean_object* v___x_7408_; lean_object* v___x_7409_; 
v___x_7406_ = ((size_t)0ULL);
v___x_7407_ = lean_usize_of_nat(v___x_7397_);
lean_inc(v_adjustResult_7384_);
v___x_7408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7384_, v_j_7395_, v_b_7396_, v___x_7406_, v___x_7407_, v_a_7388_);
v___x_7409_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7383_, v_aa_7385_, v_adjustResult_7384_, v_n_7386_, v_n_7392_, v___x_7408_);
return v___x_7409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7410_, lean_object* v_adjustResult_7411_, lean_object* v_aa_7412_, lean_object* v_n_7413_, lean_object* v_j_7414_, lean_object* v_a_7415_){
_start:
{
lean_object* v_res_7416_; 
v_res_7416_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7410_, v_adjustResult_7411_, v_aa_7412_, v_n_7413_, v_j_7414_, v_a_7415_);
lean_dec(v_j_7414_);
lean_dec(v_n_7413_);
lean_dec_ref(v_aa_7412_);
lean_dec(v_n_7410_);
return v_res_7416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7417_, lean_object* v_mr_7418_, lean_object* v_a_7419_){
_start:
{
lean_object* v_n_7420_; lean_object* v___x_7421_; 
v_n_7420_ = lean_array_get_size(v_mr_7418_);
v___x_7421_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7420_, v_adjustResult_7417_, v_mr_7418_, v_n_7420_, v_n_7420_, v_a_7419_);
return v___x_7421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7422_, lean_object* v_mr_7423_, lean_object* v_a_7424_){
_start:
{
lean_object* v_res_7425_; 
v_res_7425_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7422_, v_mr_7423_, v_a_7424_);
lean_dec_ref(v_mr_7423_);
return v_res_7425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7426_, lean_object* v_ref_7427_, lean_object* v_addEntry_7428_, lean_object* v_droppedKeys_7429_, lean_object* v_constantsPerTask_7430_, lean_object* v_droppedEntriesRef_7431_, lean_object* v_adjustResult_7432_, lean_object* v_ty_7433_, lean_object* v_a_7434_, lean_object* v_a_7435_, lean_object* v_a_7436_, lean_object* v_a_7437_){
_start:
{
lean_object* v___x_7439_; 
lean_inc_ref(v_ty_7433_);
v___x_7439_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7426_, v_ty_7433_, v_a_7434_, v_a_7435_, v_a_7436_, v_a_7437_);
if (lean_obj_tag(v___x_7439_) == 0)
{
lean_object* v_a_7440_; lean_object* v___x_7441_; 
v_a_7440_ = lean_ctor_get(v___x_7439_, 0);
lean_inc(v_a_7440_);
lean_dec_ref_known(v___x_7439_, 1);
v___x_7441_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7427_, v_addEntry_7428_, v_droppedKeys_7429_, v_constantsPerTask_7430_, v_droppedEntriesRef_7431_, v_ty_7433_, v_a_7434_, v_a_7435_, v_a_7436_, v_a_7437_);
if (lean_obj_tag(v___x_7441_) == 0)
{
lean_object* v_a_7442_; lean_object* v___x_7444_; uint8_t v_isShared_7445_; uint8_t v_isSharedCheck_7455_; 
v_a_7442_ = lean_ctor_get(v___x_7441_, 0);
v_isSharedCheck_7455_ = !lean_is_exclusive(v___x_7441_);
if (v_isSharedCheck_7455_ == 0)
{
v___x_7444_ = v___x_7441_;
v_isShared_7445_ = v_isSharedCheck_7455_;
goto v_resetjp_7443_;
}
else
{
lean_inc(v_a_7442_);
lean_dec(v___x_7441_);
v___x_7444_ = lean_box(0);
v_isShared_7445_ = v_isSharedCheck_7455_;
goto v_resetjp_7443_;
}
v_resetjp_7443_:
{
lean_object* v___x_7446_; lean_object* v___x_7447_; lean_object* v___x_7448_; lean_object* v___x_7449_; lean_object* v___x_7450_; lean_object* v___x_7451_; lean_object* v___x_7453_; 
v___x_7446_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7440_);
v___x_7447_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7442_);
v___x_7448_ = lean_nat_add(v___x_7446_, v___x_7447_);
lean_dec(v___x_7447_);
lean_dec(v___x_7446_);
v___x_7449_ = lean_mk_empty_array_with_capacity(v___x_7448_);
lean_dec(v___x_7448_);
lean_inc(v_adjustResult_7432_);
v___x_7450_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7432_, v_a_7440_, v___x_7449_);
lean_dec(v_a_7440_);
v___x_7451_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7432_, v_a_7442_, v___x_7450_);
lean_dec(v_a_7442_);
if (v_isShared_7445_ == 0)
{
lean_ctor_set(v___x_7444_, 0, v___x_7451_);
v___x_7453_ = v___x_7444_;
goto v_reusejp_7452_;
}
else
{
lean_object* v_reuseFailAlloc_7454_; 
v_reuseFailAlloc_7454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7454_, 0, v___x_7451_);
v___x_7453_ = v_reuseFailAlloc_7454_;
goto v_reusejp_7452_;
}
v_reusejp_7452_:
{
return v___x_7453_;
}
}
}
else
{
lean_object* v_a_7456_; lean_object* v___x_7458_; uint8_t v_isShared_7459_; uint8_t v_isSharedCheck_7463_; 
lean_dec(v_a_7440_);
lean_dec(v_adjustResult_7432_);
v_a_7456_ = lean_ctor_get(v___x_7441_, 0);
v_isSharedCheck_7463_ = !lean_is_exclusive(v___x_7441_);
if (v_isSharedCheck_7463_ == 0)
{
v___x_7458_ = v___x_7441_;
v_isShared_7459_ = v_isSharedCheck_7463_;
goto v_resetjp_7457_;
}
else
{
lean_inc(v_a_7456_);
lean_dec(v___x_7441_);
v___x_7458_ = lean_box(0);
v_isShared_7459_ = v_isSharedCheck_7463_;
goto v_resetjp_7457_;
}
v_resetjp_7457_:
{
lean_object* v___x_7461_; 
if (v_isShared_7459_ == 0)
{
v___x_7461_ = v___x_7458_;
goto v_reusejp_7460_;
}
else
{
lean_object* v_reuseFailAlloc_7462_; 
v_reuseFailAlloc_7462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7462_, 0, v_a_7456_);
v___x_7461_ = v_reuseFailAlloc_7462_;
goto v_reusejp_7460_;
}
v_reusejp_7460_:
{
return v___x_7461_;
}
}
}
}
else
{
lean_object* v_a_7464_; lean_object* v___x_7466_; uint8_t v_isShared_7467_; uint8_t v_isSharedCheck_7471_; 
lean_dec_ref(v_ty_7433_);
lean_dec(v_adjustResult_7432_);
lean_dec(v_droppedEntriesRef_7431_);
lean_dec(v_constantsPerTask_7430_);
lean_dec(v_droppedKeys_7429_);
lean_dec_ref(v_addEntry_7428_);
v_a_7464_ = lean_ctor_get(v___x_7439_, 0);
v_isSharedCheck_7471_ = !lean_is_exclusive(v___x_7439_);
if (v_isSharedCheck_7471_ == 0)
{
v___x_7466_ = v___x_7439_;
v_isShared_7467_ = v_isSharedCheck_7471_;
goto v_resetjp_7465_;
}
else
{
lean_inc(v_a_7464_);
lean_dec(v___x_7439_);
v___x_7466_ = lean_box(0);
v_isShared_7467_ = v_isSharedCheck_7471_;
goto v_resetjp_7465_;
}
v_resetjp_7465_:
{
lean_object* v___x_7469_; 
if (v_isShared_7467_ == 0)
{
v___x_7469_ = v___x_7466_;
goto v_reusejp_7468_;
}
else
{
lean_object* v_reuseFailAlloc_7470_; 
v_reuseFailAlloc_7470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7470_, 0, v_a_7464_);
v___x_7469_ = v_reuseFailAlloc_7470_;
goto v_reusejp_7468_;
}
v_reusejp_7468_:
{
return v___x_7469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7472_, lean_object* v_ref_7473_, lean_object* v_addEntry_7474_, lean_object* v_droppedKeys_7475_, lean_object* v_constantsPerTask_7476_, lean_object* v_droppedEntriesRef_7477_, lean_object* v_adjustResult_7478_, lean_object* v_ty_7479_, lean_object* v_a_7480_, lean_object* v_a_7481_, lean_object* v_a_7482_, lean_object* v_a_7483_, lean_object* v_a_7484_){
_start:
{
lean_object* v_res_7485_; 
v_res_7485_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7472_, v_ref_7473_, v_addEntry_7474_, v_droppedKeys_7475_, v_constantsPerTask_7476_, v_droppedEntriesRef_7477_, v_adjustResult_7478_, v_ty_7479_, v_a_7480_, v_a_7481_, v_a_7482_, v_a_7483_);
lean_dec(v_a_7483_);
lean_dec_ref(v_a_7482_);
lean_dec(v_a_7481_);
lean_dec_ref(v_a_7480_);
lean_dec(v_ref_7473_);
return v_res_7485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7486_, lean_object* v_00_u03b2_7487_, lean_object* v_moduleTreeRef_7488_, lean_object* v_ref_7489_, lean_object* v_addEntry_7490_, lean_object* v_droppedKeys_7491_, lean_object* v_constantsPerTask_7492_, lean_object* v_droppedEntriesRef_7493_, lean_object* v_adjustResult_7494_, lean_object* v_ty_7495_, lean_object* v_a_7496_, lean_object* v_a_7497_, lean_object* v_a_7498_, lean_object* v_a_7499_){
_start:
{
lean_object* v___x_7501_; 
v___x_7501_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7488_, v_ref_7489_, v_addEntry_7490_, v_droppedKeys_7491_, v_constantsPerTask_7492_, v_droppedEntriesRef_7493_, v_adjustResult_7494_, v_ty_7495_, v_a_7496_, v_a_7497_, v_a_7498_, v_a_7499_);
return v___x_7501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7502_, lean_object* v_00_u03b2_7503_, lean_object* v_moduleTreeRef_7504_, lean_object* v_ref_7505_, lean_object* v_addEntry_7506_, lean_object* v_droppedKeys_7507_, lean_object* v_constantsPerTask_7508_, lean_object* v_droppedEntriesRef_7509_, lean_object* v_adjustResult_7510_, lean_object* v_ty_7511_, lean_object* v_a_7512_, lean_object* v_a_7513_, lean_object* v_a_7514_, lean_object* v_a_7515_, lean_object* v_a_7516_){
_start:
{
lean_object* v_res_7517_; 
v_res_7517_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7502_, v_00_u03b2_7503_, v_moduleTreeRef_7504_, v_ref_7505_, v_addEntry_7506_, v_droppedKeys_7507_, v_constantsPerTask_7508_, v_droppedEntriesRef_7509_, v_adjustResult_7510_, v_ty_7511_, v_a_7512_, v_a_7513_, v_a_7514_, v_a_7515_);
lean_dec(v_a_7515_);
lean_dec_ref(v_a_7514_);
lean_dec(v_a_7513_);
lean_dec_ref(v_a_7512_);
lean_dec(v_ref_7505_);
return v_res_7517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7518_, lean_object* v_00_u03b2_7519_, lean_object* v_adjustResult_7520_, lean_object* v_mr_7521_, lean_object* v_a_7522_){
_start:
{
lean_object* v___x_7523_; 
v___x_7523_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7520_, v_mr_7521_, v_a_7522_);
return v___x_7523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7524_, lean_object* v_00_u03b2_7525_, lean_object* v_adjustResult_7526_, lean_object* v_mr_7527_, lean_object* v_a_7528_){
_start:
{
lean_object* v_res_7529_; 
v_res_7529_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7524_, v_00_u03b2_7525_, v_adjustResult_7526_, v_mr_7527_, v_a_7528_);
lean_dec_ref(v_mr_7527_);
return v_res_7529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7530_, lean_object* v_00_u03b2_7531_, lean_object* v_adjustResult_7532_, lean_object* v_j_7533_, size_t v_sz_7534_, size_t v_i_7535_, lean_object* v_bs_7536_){
_start:
{
lean_object* v___x_7537_; 
v___x_7537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7532_, v_j_7533_, v_sz_7534_, v_i_7535_, v_bs_7536_);
return v___x_7537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7538_, lean_object* v_00_u03b2_7539_, lean_object* v_adjustResult_7540_, lean_object* v_j_7541_, lean_object* v_sz_7542_, lean_object* v_i_7543_, lean_object* v_bs_7544_){
_start:
{
size_t v_sz_boxed_7545_; size_t v_i_boxed_7546_; lean_object* v_res_7547_; 
v_sz_boxed_7545_ = lean_unbox_usize(v_sz_7542_);
lean_dec(v_sz_7542_);
v_i_boxed_7546_ = lean_unbox_usize(v_i_7543_);
lean_dec(v_i_7543_);
v_res_7547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7538_, v_00_u03b2_7539_, v_adjustResult_7540_, v_j_7541_, v_sz_boxed_7545_, v_i_boxed_7546_, v_bs_7544_);
return v_res_7547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7548_, lean_object* v_00_u03b2_7549_, lean_object* v_adjustResult_7550_, lean_object* v_j_7551_, lean_object* v_as_7552_, size_t v_i_7553_, size_t v_stop_7554_, lean_object* v_b_7555_){
_start:
{
lean_object* v___x_7556_; 
v___x_7556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7550_, v_j_7551_, v_as_7552_, v_i_7553_, v_stop_7554_, v_b_7555_);
return v___x_7556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7557_, lean_object* v_00_u03b2_7558_, lean_object* v_adjustResult_7559_, lean_object* v_j_7560_, lean_object* v_as_7561_, lean_object* v_i_7562_, lean_object* v_stop_7563_, lean_object* v_b_7564_){
_start:
{
size_t v_i_boxed_7565_; size_t v_stop_boxed_7566_; lean_object* v_res_7567_; 
v_i_boxed_7565_ = lean_unbox_usize(v_i_7562_);
lean_dec(v_i_7562_);
v_stop_boxed_7566_ = lean_unbox_usize(v_stop_7563_);
lean_dec(v_stop_7563_);
v_res_7567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7557_, v_00_u03b2_7558_, v_adjustResult_7559_, v_j_7560_, v_as_7561_, v_i_boxed_7565_, v_stop_boxed_7566_, v_b_7564_);
lean_dec_ref(v_as_7561_);
return v_res_7567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7568_, lean_object* v_n_7569_, lean_object* v_00_u03b1_7570_, lean_object* v_adjustResult_7571_, lean_object* v_aa_7572_, lean_object* v_n_7573_, lean_object* v_j_7574_, lean_object* v_a_7575_, lean_object* v_a_7576_){
_start:
{
lean_object* v___x_7577_; 
v___x_7577_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7569_, v_adjustResult_7571_, v_aa_7572_, v_n_7573_, v_j_7574_, v_a_7576_);
return v___x_7577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7578_, lean_object* v_n_7579_, lean_object* v_00_u03b1_7580_, lean_object* v_adjustResult_7581_, lean_object* v_aa_7582_, lean_object* v_n_7583_, lean_object* v_j_7584_, lean_object* v_a_7585_, lean_object* v_a_7586_){
_start:
{
lean_object* v_res_7587_; 
v_res_7587_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7578_, v_n_7579_, v_00_u03b1_7580_, v_adjustResult_7581_, v_aa_7582_, v_n_7583_, v_j_7584_, v_a_7585_, v_a_7586_);
lean_dec(v_j_7584_);
lean_dec(v_n_7583_);
lean_dec_ref(v_aa_7582_);
lean_dec(v_n_7579_);
return v_res_7587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7588_, lean_object* v_n_7589_, lean_object* v_00_u03b1_7590_, lean_object* v_aa_7591_, lean_object* v_adjustResult_7592_, lean_object* v_n_7593_, lean_object* v_j_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_){
_start:
{
lean_object* v___x_7597_; 
v___x_7597_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7589_, v_aa_7591_, v_adjustResult_7592_, v_n_7593_, v_j_7594_, v_a_7596_);
return v___x_7597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7598_, lean_object* v_n_7599_, lean_object* v_00_u03b1_7600_, lean_object* v_aa_7601_, lean_object* v_adjustResult_7602_, lean_object* v_n_7603_, lean_object* v_j_7604_, lean_object* v_a_7605_, lean_object* v_a_7606_){
_start:
{
lean_object* v_res_7607_; 
v_res_7607_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7598_, v_n_7599_, v_00_u03b1_7600_, v_aa_7601_, v_adjustResult_7602_, v_n_7603_, v_j_7604_, v_a_7605_, v_a_7606_);
lean_dec(v_n_7603_);
lean_dec_ref(v_aa_7601_);
lean_dec(v_n_7599_);
return v_res_7607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7608_, lean_object* v_v_7609_){
_start:
{
lean_inc(v_v_7609_);
return v_v_7609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7610_, lean_object* v_v_7611_){
_start:
{
lean_object* v_res_7612_; 
v_res_7612_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7610_, v_v_7611_);
lean_dec(v_v_7611_);
lean_dec(v_x_7610_);
return v_res_7612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7614_, lean_object* v_addEntry_7615_, lean_object* v_droppedKeys_7616_, lean_object* v_constantsPerTask_7617_, lean_object* v_droppedEntriesRef_7618_, lean_object* v_ty_7619_, lean_object* v_a_7620_, lean_object* v_a_7621_, lean_object* v_a_7622_, lean_object* v_a_7623_){
_start:
{
lean_object* v___x_7625_; 
lean_inc(v_droppedEntriesRef_7618_);
lean_inc(v_droppedKeys_7616_);
lean_inc_ref(v_addEntry_7615_);
v___x_7625_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7615_, v_droppedKeys_7616_, v_droppedEntriesRef_7618_, v_a_7620_, v_a_7621_, v_a_7622_, v_a_7623_);
if (lean_obj_tag(v___x_7625_) == 0)
{
lean_object* v_a_7626_; lean_object* v___f_7627_; lean_object* v___x_7628_; 
v_a_7626_ = lean_ctor_get(v___x_7625_, 0);
lean_inc(v_a_7626_);
lean_dec_ref_known(v___x_7625_, 1);
v___f_7627_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7628_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7626_, v_ref_7614_, v_addEntry_7615_, v_droppedKeys_7616_, v_constantsPerTask_7617_, v_droppedEntriesRef_7618_, v___f_7627_, v_ty_7619_, v_a_7620_, v_a_7621_, v_a_7622_, v_a_7623_);
return v___x_7628_;
}
else
{
lean_object* v_a_7629_; lean_object* v___x_7631_; uint8_t v_isShared_7632_; uint8_t v_isSharedCheck_7636_; 
lean_dec_ref(v_ty_7619_);
lean_dec(v_droppedEntriesRef_7618_);
lean_dec(v_constantsPerTask_7617_);
lean_dec(v_droppedKeys_7616_);
lean_dec_ref(v_addEntry_7615_);
v_a_7629_ = lean_ctor_get(v___x_7625_, 0);
v_isSharedCheck_7636_ = !lean_is_exclusive(v___x_7625_);
if (v_isSharedCheck_7636_ == 0)
{
v___x_7631_ = v___x_7625_;
v_isShared_7632_ = v_isSharedCheck_7636_;
goto v_resetjp_7630_;
}
else
{
lean_inc(v_a_7629_);
lean_dec(v___x_7625_);
v___x_7631_ = lean_box(0);
v_isShared_7632_ = v_isSharedCheck_7636_;
goto v_resetjp_7630_;
}
v_resetjp_7630_:
{
lean_object* v___x_7634_; 
if (v_isShared_7632_ == 0)
{
v___x_7634_ = v___x_7631_;
goto v_reusejp_7633_;
}
else
{
lean_object* v_reuseFailAlloc_7635_; 
v_reuseFailAlloc_7635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7635_, 0, v_a_7629_);
v___x_7634_ = v_reuseFailAlloc_7635_;
goto v_reusejp_7633_;
}
v_reusejp_7633_:
{
return v___x_7634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7637_, lean_object* v_addEntry_7638_, lean_object* v_droppedKeys_7639_, lean_object* v_constantsPerTask_7640_, lean_object* v_droppedEntriesRef_7641_, lean_object* v_ty_7642_, lean_object* v_a_7643_, lean_object* v_a_7644_, lean_object* v_a_7645_, lean_object* v_a_7646_, lean_object* v_a_7647_){
_start:
{
lean_object* v_res_7648_; 
v_res_7648_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7637_, v_addEntry_7638_, v_droppedKeys_7639_, v_constantsPerTask_7640_, v_droppedEntriesRef_7641_, v_ty_7642_, v_a_7643_, v_a_7644_, v_a_7645_, v_a_7646_);
lean_dec(v_a_7646_);
lean_dec_ref(v_a_7645_);
lean_dec(v_a_7644_);
lean_dec_ref(v_a_7643_);
lean_dec(v_ref_7637_);
return v_res_7648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7649_, lean_object* v_ref_7650_, lean_object* v_addEntry_7651_, lean_object* v_droppedKeys_7652_, lean_object* v_constantsPerTask_7653_, lean_object* v_droppedEntriesRef_7654_, lean_object* v_ty_7655_, lean_object* v_a_7656_, lean_object* v_a_7657_, lean_object* v_a_7658_, lean_object* v_a_7659_){
_start:
{
lean_object* v___x_7661_; 
v___x_7661_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7650_, v_addEntry_7651_, v_droppedKeys_7652_, v_constantsPerTask_7653_, v_droppedEntriesRef_7654_, v_ty_7655_, v_a_7656_, v_a_7657_, v_a_7658_, v_a_7659_);
return v___x_7661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7662_, lean_object* v_ref_7663_, lean_object* v_addEntry_7664_, lean_object* v_droppedKeys_7665_, lean_object* v_constantsPerTask_7666_, lean_object* v_droppedEntriesRef_7667_, lean_object* v_ty_7668_, lean_object* v_a_7669_, lean_object* v_a_7670_, lean_object* v_a_7671_, lean_object* v_a_7672_, lean_object* v_a_7673_){
_start:
{
lean_object* v_res_7674_; 
v_res_7674_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7662_, v_ref_7663_, v_addEntry_7664_, v_droppedKeys_7665_, v_constantsPerTask_7666_, v_droppedEntriesRef_7667_, v_ty_7668_, v_a_7669_, v_a_7670_, v_a_7671_, v_a_7672_);
lean_dec(v_a_7672_);
lean_dec_ref(v_a_7671_);
lean_dec(v_a_7670_);
lean_dec_ref(v_a_7669_);
lean_dec(v_ref_7663_);
return v_res_7674_;
}
}
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar = _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar();
lean_mark_persistent(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar);
l_Lean_Meta_LazyDiscrTree_initCapacity = _init_l_Lean_Meta_LazyDiscrTree_initCapacity();
lean_mark_persistent(l_Lean_Meta_LazyDiscrTree_initCapacity);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LazyDiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_LazyDiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_LazyDiscrTree(builtin);
}
#ifdef __cplusplus
}
#endif
