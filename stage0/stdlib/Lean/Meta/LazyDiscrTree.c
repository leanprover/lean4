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
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternalDetail(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionType"};
static const lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2_value;
static const lean_string_object l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
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
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_array_get_size(v_infos_364_);
v___x_371_ = lean_nat_dec_lt(v_i_363_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_isProof(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_372_;
}
else
{
lean_object* v_info_373_; uint8_t v_isInstance_374_; uint8_t v___y_376_; 
v_info_373_ = lean_array_fget_borrowed(v_infos_364_, v_i_363_);
v_isInstance_374_ = lean_ctor_get_uint8(v_info_373_, sizeof(void*)*1 + 4);
if (v_isInstance_374_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_373_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_373_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_isProof(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_394_;
}
else
{
v___y_376_ = v___x_393_;
goto v___jp_375_;
}
}
else
{
v___y_376_ = v___x_371_;
goto v___jp_375_;
}
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v_a_362_);
v___x_395_ = lean_box(v___x_371_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
v___jp_375_:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_isType(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_391_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_391_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_391_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_391_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_unbox(v_a_378_);
lean_dec(v_a_378_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_box(v___y_376_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_383_);
v___x_385_ = v___x_380_;
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
else
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_box(v_isInstance_374_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_387_);
v___x_389_ = v___x_380_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg___boxed(lean_object* v_a_397_, lean_object* v_i_398_, lean_object* v_infos_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_a_397_, v_i_398_, v_infos_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec_ref(v_infos_399_);
lean_dec(v_i_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(lean_object* v_infos_406_, lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
if (lean_obj_tag(v_x_408_) == 5)
{
lean_object* v_fn_415_; lean_object* v_arg_416_; lean_object* v___x_417_; 
v_fn_415_ = lean_ctor_get(v_x_408_, 0);
lean_inc_ref(v_fn_415_);
v_arg_416_ = lean_ctor_get(v_x_408_, 1);
lean_inc_ref_n(v_arg_416_, 2);
lean_dec_ref_known(v_x_408_, 2);
v___x_417_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_arg_416_, v_x_407_, v_infos_406_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; uint8_t v___x_419_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_417_, 1);
v___x_419_ = lean_unbox(v_a_418_);
lean_dec(v_a_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_sub(v_x_407_, v___x_420_);
lean_dec(v_x_407_);
v___x_422_ = lean_array_push(v_x_409_, v_arg_416_);
v_x_407_ = v___x_421_;
v_x_408_ = v_fn_415_;
v_x_409_ = v___x_422_;
goto _start;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v_arg_416_);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_sub(v_x_407_, v___x_424_);
lean_dec(v_x_407_);
v___x_426_ = l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar;
v___x_427_ = lean_array_push(v_x_409_, v___x_426_);
v_x_407_ = v___x_425_;
v_x_408_ = v_fn_415_;
v_x_409_ = v___x_427_;
goto _start;
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_arg_416_);
lean_dec_ref(v_fn_415_);
lean_dec_ref(v_x_409_);
lean_dec(v_x_407_);
v_a_429_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_417_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_417_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v_x_408_);
lean_dec(v_x_407_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_x_409_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux___boxed(lean_object* v_infos_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_infos_438_, v_x_439_, v_x_440_, v_x_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec_ref(v_infos_438_);
return v_res_447_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(lean_object* v_e_462_){
_start:
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = l_Lean_Expr_isRawNatLit(v_e_462_);
v___x_464_ = 1;
if (v___x_463_ == 0)
{
lean_object* v_f_465_; uint8_t v___x_466_; 
v_f_465_ = l_Lean_Expr_getAppFn(v_e_462_);
v___x_466_ = l_Lean_Expr_isConst(v_f_465_);
if (v___x_466_ == 0)
{
lean_dec_ref(v_f_465_);
lean_dec_ref(v_e_462_);
return v___x_463_;
}
else
{
if (v___x_463_ == 0)
{
lean_object* v_fName_467_; uint8_t v___y_469_; uint8_t v___y_482_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_fName_467_ = l_Lean_Expr_constName_x21(v_f_465_);
lean_dec_ref(v_f_465_);
v___x_490_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_491_ = lean_name_eq(v_fName_467_, v___x_490_);
if (v___x_491_ == 0)
{
v___y_482_ = v___x_491_;
goto v___jp_481_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_dec_eq(v___x_492_, v___x_493_);
lean_dec(v___x_492_);
v___y_482_ = v___x_494_;
goto v___jp_481_;
}
v___jp_468_:
{
if (v___y_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_471_ = lean_name_eq(v_fName_467_, v___x_470_);
lean_dec(v_fName_467_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_e_462_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
return v___x_464_;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
lean_dec_ref(v_e_462_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_nat_dec_eq(v___x_472_, v___x_473_);
lean_dec(v___x_472_);
if (v___x_474_ == 0)
{
return v___x_474_;
}
else
{
return v___x_464_;
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_fName_467_);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
v___x_477_ = lean_nat_sub(v___x_476_, v___x_475_);
lean_dec(v___x_476_);
v___x_478_ = lean_nat_sub(v___x_477_, v___x_475_);
lean_dec(v___x_477_);
v___x_479_ = l_Lean_Expr_getRevArg_x21(v_e_462_, v___x_478_);
lean_dec_ref(v_e_462_);
v_e_462_ = v___x_479_;
goto _start;
}
}
v___jp_481_:
{
if (v___y_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_484_ = lean_name_eq(v_fName_467_, v___x_483_);
if (v___x_484_ == 0)
{
v___y_469_ = v___x_484_;
goto v___jp_468_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
v___x_486_ = lean_unsigned_to_nat(3u);
v___x_487_ = lean_nat_dec_eq(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
v___y_469_ = v___x_487_;
goto v___jp_468_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_fName_467_);
v___x_488_ = l_Lean_Expr_appArg_x21(v_e_462_);
lean_dec_ref(v_e_462_);
v_e_462_ = v___x_488_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_f_465_);
lean_dec_ref(v_e_462_);
return v___x_463_;
}
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___boxed(lean_object* v_e_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_495_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(lean_object* v_e_500_){
_start:
{
uint8_t v___y_502_; lean_object* v_f_505_; 
v_f_505_ = l_Lean_Expr_getAppFn(v_e_500_);
switch(lean_obj_tag(v_f_505_))
{
case 9:
{
lean_object* v_a_506_; 
lean_dec_ref(v_e_500_);
v_a_506_ = lean_ctor_get(v_f_505_, 0);
lean_inc_ref(v_a_506_);
lean_dec_ref_known(v_f_505_, 1);
if (lean_obj_tag(v_a_506_) == 0)
{
lean_object* v_val_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_val_507_ = lean_ctor_get(v_a_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v_a_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_val_507_);
lean_dec(v_a_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 1);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_val_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v___x_515_; 
lean_dec_ref(v_a_506_);
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
case 4:
{
lean_object* v_declName_516_; uint8_t v___y_518_; uint8_t v___y_531_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_declName_516_ = lean_ctor_get(v_f_505_, 0);
lean_inc(v_declName_516_);
lean_dec_ref_known(v_f_505_, 2);
v___x_549_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_550_ = lean_name_eq(v_declName_516_, v___x_549_);
if (v___x_550_ == 0)
{
v___y_531_ = v___x_550_;
goto v___jp_530_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
v___y_531_ = v___x_553_;
goto v___jp_530_;
}
v___jp_517_:
{
if (v___y_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_520_ = lean_name_eq(v_declName_516_, v___x_519_);
lean_dec(v_declName_516_);
if (v___x_520_ == 0)
{
lean_dec_ref(v_e_500_);
v___y_502_ = v___x_520_;
goto v___jp_501_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
lean_dec_ref(v_e_500_);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_dec_eq(v___x_521_, v___x_522_);
lean_dec(v___x_521_);
v___y_502_ = v___x_523_;
goto v___jp_501_;
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_declName_516_);
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
v___x_526_ = lean_nat_sub(v___x_525_, v___x_524_);
lean_dec(v___x_525_);
v___x_527_ = lean_nat_sub(v___x_526_, v___x_524_);
lean_dec(v___x_526_);
v___x_528_ = l_Lean_Expr_getRevArg_x21(v_e_500_, v___x_527_);
lean_dec_ref(v_e_500_);
v_e_500_ = v___x_528_;
goto _start;
}
}
v___jp_530_:
{
if (v___y_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_533_ = lean_name_eq(v_declName_516_, v___x_532_);
if (v___x_533_ == 0)
{
v___y_518_ = v___x_533_;
goto v___jp_517_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
v___x_535_ = lean_unsigned_to_nat(3u);
v___x_536_ = lean_nat_dec_eq(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
v___y_518_ = v___x_536_;
goto v___jp_517_;
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_declName_516_);
v___x_537_ = l_Lean_Expr_appArg_x21(v_e_500_);
lean_dec_ref(v_e_500_);
v___x_538_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v___x_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
return v___x_538_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
v_val_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_val_539_, v___x_543_);
lean_dec(v_val_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_554_; 
lean_dec_ref(v_f_505_);
lean_dec_ref(v_e_500_);
v___x_554_ = lean_box(0);
return v___x_554_;
}
}
v___jp_501_:
{
if (v___y_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_box(0);
return v___x_503_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0));
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object* v_e_555_){
_start:
{
uint8_t v___x_556_; 
lean_inc_ref(v_e_555_);
v___x_556_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
lean_dec_ref(v_e_555_);
v___x_557_ = lean_box(0);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v_e_555_);
if (lean_obj_tag(v___x_558_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_val_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_val_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v___x_558_);
v___x_568_ = lean_box(0);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_577_; 
lean_inc(v_a_575_);
lean_inc_ref(v_a_574_);
lean_inc(v_a_573_);
lean_inc_ref(v_a_572_);
v___x_577_ = lean_whnf(v_e_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_588_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_588_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_582_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0));
v___x_583_ = l_Lean_Expr_isConstOf(v_a_578_, v___x_582_);
lean_dec(v_a_578_);
v___x_584_ = lean_box(v___x_583_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_584_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_a_589_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_577_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_577_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v_e_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object* v_fName_617_, lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
uint8_t v___y_625_; uint8_t v___y_655_; uint8_t v___y_680_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6));
v___x_691_ = lean_name_eq(v_fName_617_, v___x_690_);
if (v___x_691_ == 0)
{
v___y_680_ = v___x_691_;
goto v___jp_679_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_693_ = lean_unsigned_to_nat(2u);
v___x_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
lean_dec(v___x_692_);
v___y_680_ = v___x_694_;
goto v___jp_679_;
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_627_ = lean_name_eq(v_fName_617_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_dec_eq(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_637_ = lean_nat_sub(v___x_636_, v___x_635_);
lean_dec(v___x_636_);
v___x_638_ = lean_nat_sub(v___x_637_, v___x_635_);
lean_dec(v___x_637_);
v___x_639_ = l_Lean_Expr_getRevArg_x21(v_e_618_, v___x_638_);
v___x_640_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_639_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; uint8_t v___x_642_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
v___x_642_ = lean_unbox(v_a_641_);
lean_dec(v_a_641_);
if (v___x_642_ == 0)
{
return v___x_640_;
}
else
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_652_; 
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___x_640_, 0);
lean_dec(v_unused_653_);
v___x_644_ = v___x_640_;
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
else
{
lean_dec(v___x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_646_ = l_Lean_Expr_appArg_x21(v_e_618_);
v___x_647_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_646_);
v___x_648_ = lean_box(v___x_647_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_648_);
v___x_650_ = v___x_644_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
return v___x_640_;
}
}
}
v___jp_654_:
{
if (v___y_655_ == 0)
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2));
v___x_657_ = lean_name_eq(v_fName_617_, v___x_656_);
if (v___x_657_ == 0)
{
v___y_625_ = v___x_657_;
goto v___jp_624_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_659_ = lean_unsigned_to_nat(6u);
v___x_660_ = lean_nat_dec_eq(v___x_658_, v___x_659_);
lean_dec(v___x_658_);
v___y_625_ = v___x_660_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_661_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = lean_nat_sub(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
v___x_664_ = l_Lean_Expr_getRevArg_x21(v_e_618_, v___x_663_);
v___x_665_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_664_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; uint8_t v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
v___x_667_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
if (v___x_667_ == 0)
{
return v___x_665_;
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_677_; 
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_665_, 0);
lean_dec(v_unused_678_);
v___x_669_ = v___x_665_;
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
else
{
lean_dec(v___x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_671_ = l_Lean_Expr_appArg_x21(v_e_618_);
v___x_672_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_671_);
v___x_673_ = lean_box(v___x_672_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_673_);
v___x_675_ = v___x_669_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
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
else
{
return v___x_665_;
}
}
}
v___jp_679_:
{
if (v___y_680_ == 0)
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5));
v___x_682_ = lean_name_eq(v_fName_617_, v___x_681_);
if (v___x_682_ == 0)
{
v___y_655_ = v___x_682_;
goto v___jp_654_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_684_ = lean_unsigned_to_nat(4u);
v___x_685_ = lean_nat_dec_eq(v___x_683_, v___x_684_);
lean_dec(v___x_683_);
v___y_655_ = v___x_685_;
goto v___jp_654_;
}
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = l_Lean_Expr_appArg_x21(v_e_618_);
v___x_687_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_686_);
v___x_688_ = lean_box(v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object* v_fName_695_, lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_695_, v_e_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_e_696_);
lean_dec(v_fName_695_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object* v_fName_703_, lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_703_, v_e_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object* v_fName_711_, lean_object* v_e_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(v_fName_711_, v_e_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_e_712_);
lean_dec(v_fName_711_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object* v_e_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = l_Lean_Expr_hasLooseBVars(v_e_721_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_e_721_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 0;
v___x_729_ = l_Lean_Expr_isHeadBetaTarget(v_e_721_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v_e_721_);
v___x_730_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0));
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = l_Lean_Expr_headBeta(v_e_721_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object* v_e_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(v_e_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object* v_e_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_e_740_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object* v_e_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(v_e_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_750_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_box(0);
v___x_752_ = l_Lean_interruptExceptionId;
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_758_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = l_Lean_maxRecDepthErrorMessage;
v___x_765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_767_ = l_Lean_MessageData_ofFormat(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_769_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_770_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_771_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_ref_771_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___y_785_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; uint8_t v___y_809_; lean_object* v___y_810_; lean_object* v_fileName_815_; lean_object* v_fileMap_816_; lean_object* v_options_817_; lean_object* v_currRecDepth_818_; lean_object* v_maxRecDepth_819_; lean_object* v_ref_820_; lean_object* v_currNamespace_821_; lean_object* v_openDecls_822_; lean_object* v_initHeartbeats_823_; lean_object* v_maxHeartbeats_824_; lean_object* v_quotContext_825_; lean_object* v_currMacroScope_826_; uint8_t v_diag_827_; lean_object* v_cancelTk_x3f_828_; uint8_t v_suppressElabErrors_829_; lean_object* v_inheritedTraceOptions_830_; 
v_fileName_815_ = lean_ctor_get(v___y_781_, 0);
v_fileMap_816_ = lean_ctor_get(v___y_781_, 1);
v_options_817_ = lean_ctor_get(v___y_781_, 2);
v_currRecDepth_818_ = lean_ctor_get(v___y_781_, 3);
v_maxRecDepth_819_ = lean_ctor_get(v___y_781_, 4);
v_ref_820_ = lean_ctor_get(v___y_781_, 5);
v_currNamespace_821_ = lean_ctor_get(v___y_781_, 6);
v_openDecls_822_ = lean_ctor_get(v___y_781_, 7);
v_initHeartbeats_823_ = lean_ctor_get(v___y_781_, 8);
v_maxHeartbeats_824_ = lean_ctor_get(v___y_781_, 9);
v_quotContext_825_ = lean_ctor_get(v___y_781_, 10);
v_currMacroScope_826_ = lean_ctor_get(v___y_781_, 11);
v_diag_827_ = lean_ctor_get_uint8(v___y_781_, sizeof(void*)*14);
v_cancelTk_x3f_828_ = lean_ctor_get(v___y_781_, 12);
v_suppressElabErrors_829_ = lean_ctor_get_uint8(v___y_781_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_830_ = lean_ctor_get(v___y_781_, 13);
if (lean_obj_tag(v_cancelTk_x3f_828_) == 1)
{
lean_object* v_val_836_; uint8_t v___x_837_; 
v_val_836_ = lean_ctor_get(v_cancelTk_x3f_828_, 0);
v___x_837_ = l_IO_CancelToken_isSet(v_val_836_);
if (v___x_837_ == 0)
{
goto v___jp_831_;
}
else
{
lean_object* v___x_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_x_779_);
v___x_838_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
goto v___jp_831_;
}
v___jp_784_:
{
if (lean_obj_tag(v___y_785_) == 0)
{
return v___y_785_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___y_785_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___y_785_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___y_785_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___y_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
v___jp_794_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_add(v___y_806_, v___x_811_);
lean_inc_ref(v___y_797_);
lean_inc(v___y_802_);
lean_inc(v___y_805_);
lean_inc(v___y_800_);
lean_inc(v___y_808_);
lean_inc(v___y_807_);
lean_inc(v___y_810_);
lean_inc(v___y_798_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_795_);
lean_inc_ref(v___y_803_);
lean_inc_ref(v___y_796_);
v___x_813_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_813_, 0, v___y_796_);
lean_ctor_set(v___x_813_, 1, v___y_803_);
lean_ctor_set(v___x_813_, 2, v___y_795_);
lean_ctor_set(v___x_813_, 3, v___x_812_);
lean_ctor_set(v___x_813_, 4, v___y_799_);
lean_ctor_set(v___x_813_, 5, v___y_804_);
lean_ctor_set(v___x_813_, 6, v___y_798_);
lean_ctor_set(v___x_813_, 7, v___y_810_);
lean_ctor_set(v___x_813_, 8, v___y_807_);
lean_ctor_set(v___x_813_, 9, v___y_808_);
lean_ctor_set(v___x_813_, 10, v___y_800_);
lean_ctor_set(v___x_813_, 11, v___y_805_);
lean_ctor_set(v___x_813_, 12, v___y_802_);
lean_ctor_set(v___x_813_, 13, v___y_797_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*14, v___y_809_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*14 + 1, v___y_801_);
lean_inc(v___y_782_);
lean_inc(v___y_780_);
v___x_814_ = lean_apply_4(v_x_779_, v___y_780_, v___x_813_, v___y_782_, lean_box(0));
v___y_785_ = v___x_814_;
goto v___jp_784_;
}
v___jp_831_:
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = lean_nat_dec_eq(v_maxRecDepth_819_, v___x_832_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_eq(v_currRecDepth_818_, v_maxRecDepth_819_);
if (v___x_834_ == 0)
{
lean_inc(v_ref_820_);
v___y_795_ = v_options_817_;
v___y_796_ = v_fileName_815_;
v___y_797_ = v_inheritedTraceOptions_830_;
v___y_798_ = v_currNamespace_821_;
v___y_799_ = v_maxRecDepth_819_;
v___y_800_ = v_quotContext_825_;
v___y_801_ = v_suppressElabErrors_829_;
v___y_802_ = v_cancelTk_x3f_828_;
v___y_803_ = v_fileMap_816_;
v___y_804_ = v_ref_820_;
v___y_805_ = v_currMacroScope_826_;
v___y_806_ = v_currRecDepth_818_;
v___y_807_ = v_initHeartbeats_823_;
v___y_808_ = v_maxHeartbeats_824_;
v___y_809_ = v_diag_827_;
v___y_810_ = v_openDecls_822_;
goto v___jp_794_;
}
else
{
lean_object* v___x_835_; 
lean_dec_ref(v_x_779_);
lean_inc(v_ref_820_);
v___x_835_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_820_);
v___y_785_ = v___x_835_;
goto v___jp_784_;
}
}
else
{
lean_inc(v_ref_820_);
v___y_795_ = v_options_817_;
v___y_796_ = v_fileName_815_;
v___y_797_ = v_inheritedTraceOptions_830_;
v___y_798_ = v_currNamespace_821_;
v___y_799_ = v_maxRecDepth_819_;
v___y_800_ = v_quotContext_825_;
v___y_801_ = v_suppressElabErrors_829_;
v___y_802_ = v_cancelTk_x3f_828_;
v___y_803_ = v_fileMap_816_;
v___y_804_ = v_ref_820_;
v___y_805_ = v_currMacroScope_826_;
v___y_806_ = v_currRecDepth_818_;
v___y_807_ = v_initHeartbeats_823_;
v___y_808_ = v_maxHeartbeats_824_;
v___y_809_ = v_diag_827_;
v___y_810_ = v_openDecls_822_;
goto v___jp_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
if (lean_obj_tag(v_x_854_) == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_box(0);
return v___x_855_;
}
else
{
lean_object* v_key_856_; lean_object* v_value_857_; lean_object* v_tail_858_; uint8_t v___x_859_; 
v_key_856_ = lean_ctor_get(v_x_854_, 0);
v_value_857_ = lean_ctor_get(v_x_854_, 1);
v_tail_858_ = lean_ctor_get(v_x_854_, 2);
v___x_859_ = l_Lean_ExprStructEq_beq(v_key_856_, v_a_853_);
if (v___x_859_ == 0)
{
v_x_854_ = v_tail_858_;
goto _start;
}
else
{
lean_object* v___x_861_; 
lean_inc(v_value_857_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_value_857_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec_ref(v_a_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_buckets_867_; lean_object* v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v_fold_872_; uint64_t v___x_873_; uint64_t v___x_874_; uint64_t v___x_875_; size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_buckets_867_ = lean_ctor_get(v_m_865_, 1);
v___x_868_ = lean_array_get_size(v_buckets_867_);
v___x_869_ = l_Lean_ExprStructEq_hash(v_a_866_);
v___x_870_ = 32ULL;
v___x_871_ = lean_uint64_shift_right(v___x_869_, v___x_870_);
v_fold_872_ = lean_uint64_xor(v___x_869_, v___x_871_);
v___x_873_ = 16ULL;
v___x_874_ = lean_uint64_shift_right(v_fold_872_, v___x_873_);
v___x_875_ = lean_uint64_xor(v_fold_872_, v___x_874_);
v___x_876_ = lean_uint64_to_usize(v___x_875_);
v___x_877_ = lean_usize_of_nat(v___x_868_);
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_sub(v___x_877_, v___x_878_);
v___x_880_ = lean_usize_land(v___x_876_, v___x_879_);
v___x_881_ = lean_array_uget_borrowed(v_buckets_867_, v___x_880_);
v___x_882_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_866_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_883_, v_a_884_);
lean_dec_ref(v_a_884_);
lean_dec_ref(v_m_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_886_, lean_object* v_b_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_888_) == 0)
{
lean_dec(v_b_887_);
lean_dec_ref(v_a_886_);
return v_x_888_;
}
else
{
lean_object* v_key_889_; lean_object* v_value_890_; lean_object* v_tail_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_903_; 
v_key_889_ = lean_ctor_get(v_x_888_, 0);
v_value_890_ = lean_ctor_get(v_x_888_, 1);
v_tail_891_ = lean_ctor_get(v_x_888_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_888_);
if (v_isSharedCheck_903_ == 0)
{
v___x_893_ = v_x_888_;
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_tail_891_);
lean_inc(v_value_890_);
lean_inc(v_key_889_);
lean_dec(v_x_888_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_903_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_ExprStructEq_beq(v_key_889_, v_a_886_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_886_, v_b_887_, v_tail_891_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 2, v___x_896_);
v___x_898_ = v___x_893_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_key_889_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_value_890_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v___x_901_; 
lean_dec(v_value_890_);
lean_dec(v_key_889_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v_b_887_);
lean_ctor_set(v___x_893_, 0, v_a_886_);
v___x_901_ = v___x_893_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_886_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_b_887_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_tail_891_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
return v_x_904_;
}
else
{
lean_object* v_key_906_; lean_object* v_value_907_; lean_object* v_tail_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_931_; 
v_key_906_ = lean_ctor_get(v_x_905_, 0);
v_value_907_ = lean_ctor_get(v_x_905_, 1);
v_tail_908_ = lean_ctor_get(v_x_905_, 2);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_905_);
if (v_isSharedCheck_931_ == 0)
{
v___x_910_ = v_x_905_;
v_isShared_911_ = v_isSharedCheck_931_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_tail_908_);
lean_inc(v_value_907_);
lean_inc(v_key_906_);
lean_dec(v_x_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_931_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v___x_915_; uint64_t v_fold_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_912_ = lean_array_get_size(v_x_904_);
v___x_913_ = l_Lean_ExprStructEq_hash(v_key_906_);
v___x_914_ = 32ULL;
v___x_915_ = lean_uint64_shift_right(v___x_913_, v___x_914_);
v_fold_916_ = lean_uint64_xor(v___x_913_, v___x_915_);
v___x_917_ = 16ULL;
v___x_918_ = lean_uint64_shift_right(v_fold_916_, v___x_917_);
v___x_919_ = lean_uint64_xor(v_fold_916_, v___x_918_);
v___x_920_ = lean_uint64_to_usize(v___x_919_);
v___x_921_ = lean_usize_of_nat(v___x_912_);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_sub(v___x_921_, v___x_922_);
v___x_924_ = lean_usize_land(v___x_920_, v___x_923_);
v___x_925_ = lean_array_uget_borrowed(v_x_904_, v___x_924_);
lean_inc(v___x_925_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 2, v___x_925_);
v___x_927_ = v___x_910_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_key_906_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_value_907_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v___x_925_);
v___x_927_ = v_reuseFailAlloc_930_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_array_uset(v_x_904_, v___x_924_, v___x_927_);
v_x_904_ = v___x_928_;
v_x_905_ = v_tail_908_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_932_, lean_object* v_source_933_, lean_object* v_target_934_){
_start:
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = lean_array_get_size(v_source_933_);
v___x_936_ = lean_nat_dec_lt(v_i_932_, v___x_935_);
if (v___x_936_ == 0)
{
lean_dec_ref(v_source_933_);
lean_dec(v_i_932_);
return v_target_934_;
}
else
{
lean_object* v_es_937_; lean_object* v___x_938_; lean_object* v_source_939_; lean_object* v_target_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_es_937_ = lean_array_fget(v_source_933_, v_i_932_);
v___x_938_ = lean_box(0);
v_source_939_ = lean_array_fset(v_source_933_, v_i_932_, v___x_938_);
v_target_940_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_934_, v_es_937_);
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_nat_add(v_i_932_, v___x_941_);
lean_dec(v_i_932_);
v_i_932_ = v___x_942_;
v_source_933_ = v_source_939_;
v_target_934_ = v_target_940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_944_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_nbuckets_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_945_ = lean_array_get_size(v_data_944_);
v___x_946_ = lean_unsigned_to_nat(2u);
v_nbuckets_947_ = lean_nat_mul(v___x_945_, v___x_946_);
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = lean_box(0);
v___x_950_ = lean_mk_array(v_nbuckets_947_, v___x_949_);
v___x_951_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_948_, v_data_944_, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_952_, lean_object* v_x_953_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
uint8_t v___x_954_; 
v___x_954_ = 0;
return v___x_954_;
}
else
{
lean_object* v_key_955_; lean_object* v_tail_956_; uint8_t v___x_957_; 
v_key_955_ = lean_ctor_get(v_x_953_, 0);
v_tail_956_ = lean_ctor_get(v_x_953_, 2);
v___x_957_ = l_Lean_ExprStructEq_beq(v_key_955_, v_a_952_);
if (v___x_957_ == 0)
{
v_x_953_ = v_tail_956_;
goto _start;
}
else
{
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_959_, lean_object* v_x_960_){
_start:
{
uint8_t v_res_961_; lean_object* v_r_962_; 
v_res_961_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_959_, v_x_960_);
lean_dec(v_x_960_);
lean_dec_ref(v_a_959_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_963_, lean_object* v_a_964_, lean_object* v_b_965_){
_start:
{
lean_object* v_size_966_; lean_object* v_buckets_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1010_; 
v_size_966_ = lean_ctor_get(v_m_963_, 0);
v_buckets_967_ = lean_ctor_get(v_m_963_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_m_963_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_969_ = v_m_963_;
v_isShared_970_ = v_isSharedCheck_1010_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_buckets_967_);
lean_inc(v_size_966_);
lean_dec(v_m_963_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1010_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v___x_974_; uint64_t v_fold_975_; uint64_t v___x_976_; uint64_t v___x_977_; uint64_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; size_t v___x_983_; lean_object* v_bkt_984_; uint8_t v___x_985_; 
v___x_971_ = lean_array_get_size(v_buckets_967_);
v___x_972_ = l_Lean_ExprStructEq_hash(v_a_964_);
v___x_973_ = 32ULL;
v___x_974_ = lean_uint64_shift_right(v___x_972_, v___x_973_);
v_fold_975_ = lean_uint64_xor(v___x_972_, v___x_974_);
v___x_976_ = 16ULL;
v___x_977_ = lean_uint64_shift_right(v_fold_975_, v___x_976_);
v___x_978_ = lean_uint64_xor(v_fold_975_, v___x_977_);
v___x_979_ = lean_uint64_to_usize(v___x_978_);
v___x_980_ = lean_usize_of_nat(v___x_971_);
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_sub(v___x_980_, v___x_981_);
v___x_983_ = lean_usize_land(v___x_979_, v___x_982_);
v_bkt_984_ = lean_array_uget_borrowed(v_buckets_967_, v___x_983_);
v___x_985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_964_, v_bkt_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v_size_x27_987_; lean_object* v___x_988_; lean_object* v_buckets_x27_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_986_ = lean_unsigned_to_nat(1u);
v_size_x27_987_ = lean_nat_add(v_size_966_, v___x_986_);
lean_dec(v_size_966_);
lean_inc(v_bkt_984_);
v___x_988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_988_, 0, v_a_964_);
lean_ctor_set(v___x_988_, 1, v_b_965_);
lean_ctor_set(v___x_988_, 2, v_bkt_984_);
v_buckets_x27_989_ = lean_array_uset(v_buckets_967_, v___x_983_, v___x_988_);
v___x_990_ = lean_unsigned_to_nat(4u);
v___x_991_ = lean_nat_mul(v_size_x27_987_, v___x_990_);
v___x_992_ = lean_unsigned_to_nat(3u);
v___x_993_ = lean_nat_div(v___x_991_, v___x_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_array_get_size(v_buckets_x27_989_);
v___x_995_ = lean_nat_dec_le(v___x_993_, v___x_994_);
lean_dec(v___x_993_);
if (v___x_995_ == 0)
{
lean_object* v_val_996_; lean_object* v___x_998_; 
v_val_996_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_989_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_val_996_);
lean_ctor_set(v___x_969_, 0, v_size_x27_987_);
v___x_998_ = v___x_969_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_size_x27_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_val_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
else
{
lean_object* v___x_1001_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_buckets_x27_989_);
lean_ctor_set(v___x_969_, 0, v_size_x27_987_);
v___x_1001_ = v___x_969_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_size_x27_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_buckets_x27_989_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v_buckets_x27_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_inc(v_bkt_984_);
v___x_1003_ = lean_box(0);
v_buckets_x27_1004_ = lean_array_uset(v_buckets_967_, v___x_983_, v___x_1003_);
v___x_1005_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_964_, v_b_965_, v_bkt_984_);
v___x_1006_ = lean_array_uset(v_buckets_x27_1004_, v___x_983_, v___x_1005_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_1006_);
v___x_1008_ = v___x_969_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_size_966_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_1011_, lean_object* v_e_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = lean_st_ref_take(v_a_1011_);
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_1015_, v_e_1012_, v_a_1013_);
v___x_1017_ = lean_st_ref_set(v_a_1011_, v___x_1016_);
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1019_, lean_object* v_e_1020_, lean_object* v_a_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_1019_, v_e_1020_, v_a_1021_);
lean_dec(v_a_1019_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1024_, lean_object* v_x_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_apply_1(v_x_1025_, lean_box(0));
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1031_, v_x_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1036_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1038_; lean_object* v_dummy_1039_; 
v___x_1038_ = lean_box(0);
v_dummy_1039_ = l_Lean_Expr_sort___override(v___x_1038_);
return v_dummy_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1040_, lean_object* v_post_1041_, size_t v_sz_1042_, size_t v_i_1043_, lean_object* v_bs_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_usize_dec_lt(v_i_1043_, v_sz_1042_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec_ref(v_post_1041_);
lean_dec_ref(v_pre_1040_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_bs_1044_);
return v___x_1050_;
}
else
{
lean_object* v_v_1051_; lean_object* v___x_1052_; 
v_v_1051_ = lean_array_uget_borrowed(v_bs_1044_, v_i_1043_);
lean_inc(v_v_1051_);
lean_inc_ref(v_post_1041_);
lean_inc_ref(v_pre_1040_);
v___x_1052_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1040_, v_post_1041_, v_v_1051_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v_bs_x27_1055_; size_t v___x_1056_; size_t v___x_1057_; lean_object* v___x_1058_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = lean_unsigned_to_nat(0u);
v_bs_x27_1055_ = lean_array_uset(v_bs_1044_, v_i_1043_, v___x_1054_);
v___x_1056_ = ((size_t)1ULL);
v___x_1057_ = lean_usize_add(v_i_1043_, v___x_1056_);
v___x_1058_ = lean_array_uset(v_bs_x27_1055_, v_i_1043_, v_a_1053_);
v_i_1043_ = v___x_1057_;
v_bs_1044_ = v___x_1058_;
goto _start;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v_bs_1044_);
lean_dec_ref(v_post_1041_);
lean_dec_ref(v_pre_1040_);
v_a_1060_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1052_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1052_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1068_, lean_object* v_post_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
if (lean_obj_tag(v_x_1070_) == 5)
{
lean_object* v_fn_1077_; lean_object* v_arg_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_fn_1077_ = lean_ctor_get(v_x_1070_, 0);
lean_inc_ref(v_fn_1077_);
v_arg_1078_ = lean_ctor_get(v_x_1070_, 1);
lean_inc_ref(v_arg_1078_);
lean_dec_ref_known(v_x_1070_, 2);
v___x_1079_ = lean_array_set(v_x_1071_, v_x_1072_, v_arg_1078_);
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_sub(v_x_1072_, v___x_1080_);
lean_dec(v_x_1072_);
v_x_1070_ = v_fn_1077_;
v_x_1071_ = v___x_1079_;
v_x_1072_ = v___x_1081_;
goto _start;
}
else
{
lean_object* v___x_1083_; 
lean_dec(v_x_1072_);
lean_inc_ref(v_post_1069_);
lean_inc_ref(v_pre_1068_);
v___x_1083_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1068_, v_post_1069_, v_x_1070_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v_sz_1085_ = lean_array_size(v_x_1071_);
v___x_1086_ = ((size_t)0ULL);
lean_inc_ref(v_post_1069_);
lean_inc_ref(v_pre_1068_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1068_, v_post_1069_, v_sz_1085_, v___x_1086_, v_x_1071_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_Lean_mkAppN(v_a_1084_, v_a_1088_);
lean_dec(v_a_1088_);
v___x_1090_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1068_, v_post_1069_, v___x_1089_, v___y_1073_, v___y_1074_, v___y_1075_);
return v___x_1090_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1084_);
lean_dec_ref(v_post_1069_);
lean_dec_ref(v_pre_1068_);
v_a_1091_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1087_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1087_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_dec_ref(v_x_1071_);
lean_dec_ref(v_post_1069_);
lean_dec_ref(v_pre_1068_);
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1099_, lean_object* v_pre_1100_, lean_object* v_e_1101_, lean_object* v_post_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; uint8_t v___y_1130_; lean_object* v___y_1138_; uint8_t v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; uint8_t v___y_1143_; lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Core_checkSystem(v___x_1099_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1150_, 1);
lean_inc_ref(v_pre_1100_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
lean_inc_ref(v_e_1101_);
v___x_1151_ = lean_apply_4(v_pre_1100_, v_e_1101_, v___y_1104_, v___y_1105_, lean_box(0));
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1241_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1241_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1241_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___y_1157_; 
switch(lean_obj_tag(v_a_1152_))
{
case 0:
{
lean_object* v_e_1231_; lean_object* v___x_1233_; 
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_e_1101_);
lean_dec_ref(v_pre_1100_);
v_e_1231_ = lean_ctor_get(v_a_1152_, 0);
lean_inc_ref(v_e_1231_);
lean_dec_ref_known(v_a_1152_, 1);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_e_1231_);
v___x_1233_ = v___x_1154_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_e_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
case 1:
{
lean_object* v_e_1235_; lean_object* v___x_1236_; 
lean_del_object(v___x_1154_);
lean_dec_ref(v_e_1101_);
v_e_1235_ = lean_ctor_get(v_a_1152_, 0);
lean_inc_ref(v_e_1235_);
lean_dec_ref_known(v_a_1152_, 1);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1236_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_e_1235_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v_a_1237_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1238_;
}
else
{
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1236_;
}
}
default: 
{
lean_object* v_e_x3f_1239_; 
lean_del_object(v___x_1154_);
v_e_x3f_1239_ = lean_ctor_get(v_a_1152_, 0);
lean_inc(v_e_x3f_1239_);
lean_dec_ref_known(v_a_1152_, 1);
if (lean_obj_tag(v_e_x3f_1239_) == 0)
{
v___y_1157_ = v_e_1101_;
goto v___jp_1156_;
}
else
{
lean_object* v_val_1240_; 
lean_dec_ref(v_e_1101_);
v_val_1240_ = lean_ctor_get(v_e_x3f_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v_e_x3f_1239_, 1);
v___y_1157_ = v_val_1240_;
goto v___jp_1156_;
}
}
}
v___jp_1156_:
{
switch(lean_obj_tag(v___y_1157_))
{
case 7:
{
lean_object* v_binderName_1158_; lean_object* v_binderType_1159_; lean_object* v_body_1160_; uint8_t v_binderInfo_1161_; lean_object* v___x_1162_; 
v_binderName_1158_ = lean_ctor_get(v___y_1157_, 0);
lean_inc(v_binderName_1158_);
v_binderType_1159_ = lean_ctor_get(v___y_1157_, 1);
v_body_1160_ = lean_ctor_get(v___y_1157_, 2);
v_binderInfo_1161_ = lean_ctor_get_uint8(v___y_1157_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1159_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_binderType_1159_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
lean_inc_ref(v_body_1160_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1164_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_body_1160_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; size_t v___x_1166_; size_t v___x_1167_; uint8_t v___x_1168_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1166_ = lean_ptr_addr(v_binderType_1159_);
v___x_1167_ = lean_ptr_addr(v_a_1163_);
v___x_1168_ = lean_usize_dec_eq(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
v___y_1138_ = v_binderName_1158_;
v___y_1139_ = v_binderInfo_1161_;
v___y_1140_ = v_a_1165_;
v___y_1141_ = v___y_1157_;
v___y_1142_ = v_a_1163_;
v___y_1143_ = v___x_1168_;
goto v___jp_1137_;
}
else
{
size_t v___x_1169_; size_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = lean_ptr_addr(v_body_1160_);
v___x_1170_ = lean_ptr_addr(v_a_1165_);
v___x_1171_ = lean_usize_dec_eq(v___x_1169_, v___x_1170_);
v___y_1138_ = v_binderName_1158_;
v___y_1139_ = v_binderInfo_1161_;
v___y_1140_ = v_a_1165_;
v___y_1141_ = v___y_1157_;
v___y_1142_ = v_a_1163_;
v___y_1143_ = v___x_1171_;
goto v___jp_1137_;
}
}
else
{
lean_dec(v_a_1163_);
lean_dec_ref_known(v___y_1157_, 3);
lean_dec(v_binderName_1158_);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1164_;
}
}
else
{
lean_dec_ref_known(v___y_1157_, 3);
lean_dec(v_binderName_1158_);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1162_;
}
}
case 6:
{
lean_object* v_binderName_1172_; lean_object* v_binderType_1173_; lean_object* v_body_1174_; uint8_t v_binderInfo_1175_; lean_object* v___x_1176_; 
v_binderName_1172_ = lean_ctor_get(v___y_1157_, 0);
lean_inc(v_binderName_1172_);
v_binderType_1173_ = lean_ctor_get(v___y_1157_, 1);
v_body_1174_ = lean_ctor_get(v___y_1157_, 2);
v_binderInfo_1175_ = lean_ctor_get_uint8(v___y_1157_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1173_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1176_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_binderType_1173_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
lean_inc_ref(v_body_1174_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1178_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_body_1174_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; size_t v___x_1180_; size_t v___x_1181_; uint8_t v___x_1182_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1180_ = lean_ptr_addr(v_binderType_1173_);
v___x_1181_ = lean_ptr_addr(v_a_1177_);
v___x_1182_ = lean_usize_dec_eq(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
v___y_1125_ = v_a_1179_;
v___y_1126_ = v_a_1177_;
v___y_1127_ = v_binderName_1172_;
v___y_1128_ = v___y_1157_;
v___y_1129_ = v_binderInfo_1175_;
v___y_1130_ = v___x_1182_;
goto v___jp_1124_;
}
else
{
size_t v___x_1183_; size_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1183_ = lean_ptr_addr(v_body_1174_);
v___x_1184_ = lean_ptr_addr(v_a_1179_);
v___x_1185_ = lean_usize_dec_eq(v___x_1183_, v___x_1184_);
v___y_1125_ = v_a_1179_;
v___y_1126_ = v_a_1177_;
v___y_1127_ = v_binderName_1172_;
v___y_1128_ = v___y_1157_;
v___y_1129_ = v_binderInfo_1175_;
v___y_1130_ = v___x_1185_;
goto v___jp_1124_;
}
}
else
{
lean_dec(v_a_1177_);
lean_dec_ref_known(v___y_1157_, 3);
lean_dec(v_binderName_1172_);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1178_;
}
}
else
{
lean_dec(v_binderName_1172_);
lean_dec_ref_known(v___y_1157_, 3);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1176_;
}
}
case 8:
{
lean_object* v_declName_1186_; lean_object* v_type_1187_; lean_object* v_value_1188_; lean_object* v_body_1189_; uint8_t v_nondep_1190_; lean_object* v___x_1191_; 
v_declName_1186_ = lean_ctor_get(v___y_1157_, 0);
lean_inc(v_declName_1186_);
v_type_1187_ = lean_ctor_get(v___y_1157_, 1);
v_value_1188_ = lean_ctor_get(v___y_1157_, 2);
v_body_1189_ = lean_ctor_get(v___y_1157_, 3);
lean_inc_ref(v_body_1189_);
v_nondep_1190_ = lean_ctor_get_uint8(v___y_1157_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1187_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1191_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_type_1187_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
lean_inc_ref(v_value_1188_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1193_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_value_1188_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
lean_inc_ref(v_body_1189_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1195_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_body_1189_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; size_t v___x_1197_; size_t v___x_1198_; uint8_t v___x_1199_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = lean_ptr_addr(v_type_1187_);
v___x_1198_ = lean_ptr_addr(v_a_1192_);
v___x_1199_ = lean_usize_dec_eq(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
v___y_1108_ = v_nondep_1190_;
v___y_1109_ = v_declName_1186_;
v___y_1110_ = v___y_1157_;
v___y_1111_ = v_a_1196_;
v___y_1112_ = v_a_1194_;
v___y_1113_ = v_a_1192_;
v___y_1114_ = v_body_1189_;
v___y_1115_ = v___x_1199_;
goto v___jp_1107_;
}
else
{
size_t v___x_1200_; size_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1200_ = lean_ptr_addr(v_value_1188_);
v___x_1201_ = lean_ptr_addr(v_a_1194_);
v___x_1202_ = lean_usize_dec_eq(v___x_1200_, v___x_1201_);
v___y_1108_ = v_nondep_1190_;
v___y_1109_ = v_declName_1186_;
v___y_1110_ = v___y_1157_;
v___y_1111_ = v_a_1196_;
v___y_1112_ = v_a_1194_;
v___y_1113_ = v_a_1192_;
v___y_1114_ = v_body_1189_;
v___y_1115_ = v___x_1202_;
goto v___jp_1107_;
}
}
else
{
lean_dec(v_a_1194_);
lean_dec(v_a_1192_);
lean_dec_ref(v_body_1189_);
lean_dec_ref_known(v___y_1157_, 4);
lean_dec(v_declName_1186_);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1195_;
}
}
else
{
lean_dec(v_a_1192_);
lean_dec_ref(v_body_1189_);
lean_dec_ref_known(v___y_1157_, 4);
lean_dec(v_declName_1186_);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1193_;
}
}
else
{
lean_dec_ref(v_body_1189_);
lean_dec_ref_known(v___y_1157_, 4);
lean_dec(v_declName_1186_);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1191_;
}
}
case 5:
{
lean_object* v_dummy_1203_; lean_object* v_nargs_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_dummy_1203_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1204_ = l_Lean_Expr_getAppNumArgs(v___y_1157_);
lean_inc(v_nargs_1204_);
v___x_1205_ = lean_mk_array(v_nargs_1204_, v_dummy_1203_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_sub(v_nargs_1204_, v___x_1206_);
lean_dec(v_nargs_1204_);
v___x_1208_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1100_, v_post_1102_, v___y_1157_, v___x_1205_, v___x_1207_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1208_;
}
case 10:
{
lean_object* v_data_1209_; lean_object* v_expr_1210_; lean_object* v___x_1211_; 
v_data_1209_ = lean_ctor_get(v___y_1157_, 0);
v_expr_1210_ = lean_ctor_get(v___y_1157_, 1);
lean_inc_ref(v_expr_1210_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1211_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_expr_1210_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1213_ = lean_ptr_addr(v_expr_1210_);
v___x_1214_ = lean_ptr_addr(v_a_1212_);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_inc(v_data_1209_);
lean_dec_ref_known(v___y_1157_, 2);
v___x_1216_ = l_Lean_Expr_mdata___override(v_data_1209_, v_a_1212_);
v___x_1217_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1216_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; 
lean_dec(v_a_1212_);
v___x_1218_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___y_1157_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1218_;
}
}
else
{
lean_dec_ref_known(v___y_1157_, 2);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1211_;
}
}
case 11:
{
lean_object* v_typeName_1219_; lean_object* v_idx_1220_; lean_object* v_struct_1221_; lean_object* v___x_1222_; 
v_typeName_1219_ = lean_ctor_get(v___y_1157_, 0);
v_idx_1220_ = lean_ctor_get(v___y_1157_, 1);
v_struct_1221_ = lean_ctor_get(v___y_1157_, 2);
lean_inc_ref(v_struct_1221_);
lean_inc_ref(v_post_1102_);
lean_inc_ref(v_pre_1100_);
v___x_1222_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1100_, v_post_1102_, v_struct_1221_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; size_t v___x_1224_; size_t v___x_1225_; uint8_t v___x_1226_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___x_1224_ = lean_ptr_addr(v_struct_1221_);
v___x_1225_ = lean_ptr_addr(v_a_1223_);
v___x_1226_ = lean_usize_dec_eq(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_inc(v_idx_1220_);
lean_inc(v_typeName_1219_);
lean_dec_ref_known(v___y_1157_, 3);
v___x_1227_ = l_Lean_Expr_proj___override(v_typeName_1219_, v_idx_1220_, v_a_1223_);
v___x_1228_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1227_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; 
lean_dec(v_a_1223_);
v___x_1229_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___y_1157_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1229_;
}
}
else
{
lean_dec_ref_known(v___y_1157_, 3);
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_pre_1100_);
return v___x_1222_;
}
}
default: 
{
lean_object* v___x_1230_; 
v___x_1230_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___y_1157_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1230_;
}
}
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_e_1101_);
lean_dec_ref(v_pre_1100_);
v_a_1242_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1151_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1151_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_post_1102_);
lean_dec_ref(v_e_1101_);
lean_dec_ref(v_pre_1100_);
v_a_1250_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1150_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1150_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
v___jp_1107_:
{
if (v___y_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v___y_1114_);
lean_dec_ref(v___y_1110_);
v___x_1116_ = l_Lean_Expr_letE___override(v___y_1109_, v___y_1113_, v___y_1112_, v___y_1111_, v___y_1108_);
v___x_1117_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1116_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1117_;
}
else
{
size_t v___x_1118_; size_t v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_ptr_addr(v___y_1114_);
lean_dec_ref(v___y_1114_);
v___x_1119_ = lean_ptr_addr(v___y_1111_);
v___x_1120_ = lean_usize_dec_eq(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref(v___y_1110_);
v___x_1121_ = l_Lean_Expr_letE___override(v___y_1109_, v___y_1113_, v___y_1112_, v___y_1111_, v___y_1108_);
v___x_1122_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1121_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1109_);
v___x_1123_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___y_1110_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1123_;
}
}
}
v___jp_1124_:
{
if (v___y_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref(v___y_1128_);
v___x_1131_ = l_Lean_Expr_lam___override(v___y_1127_, v___y_1126_, v___y_1125_, v___y_1129_);
v___x_1132_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1131_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1132_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Lean_instBEqBinderInfo_beq(v___y_1129_, v___y_1129_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref(v___y_1128_);
v___x_1134_ = l_Lean_Expr_lam___override(v___y_1127_, v___y_1126_, v___y_1125_, v___y_1129_);
v___x_1135_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1134_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v___y_1125_);
v___x_1136_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___y_1128_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1136_;
}
}
}
v___jp_1137_:
{
if (v___y_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v___y_1141_);
v___x_1144_ = l_Lean_Expr_forallE___override(v___y_1138_, v___y_1142_, v___y_1140_, v___y_1139_);
v___x_1145_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1144_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1145_;
}
else
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Lean_instBEqBinderInfo_beq(v___y_1139_, v___y_1139_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v___y_1141_);
v___x_1147_ = l_Lean_Expr_forallE___override(v___y_1138_, v___y_1142_, v___y_1140_, v___y_1139_);
v___x_1148_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___x_1147_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v___y_1142_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1138_);
v___x_1149_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1100_, v_post_1102_, v___y_1141_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1258_, lean_object* v_pre_1259_, lean_object* v_e_1260_, lean_object* v_post_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1258_, v_pre_1259_, v_e_1260_, v_post_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1267_, lean_object* v_post_1268_, lean_object* v_e_1269_, lean_object* v_a_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc(v_a_1270_);
v___x_1274_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1274_, 0, lean_box(0));
lean_closure_set(v___x_1274_, 1, lean_box(0));
lean_closure_set(v___x_1274_, 2, v_a_1270_);
v___x_1275_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1274_, v___y_1271_, v___y_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1307_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1307_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1307_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1276_, v_e_1269_);
lean_dec(v_a_1276_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; 
lean_del_object(v___x_1278_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1269_);
v___f_1282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1282_, 0, v___x_1281_);
lean_closure_set(v___f_1282_, 1, v_pre_1267_);
lean_closure_set(v___f_1282_, 2, v_e_1269_);
lean_closure_set(v___f_1282_, 3, v_post_1268_);
v___x_1283_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1282_, v_a_1270_, v___y_1271_, v___y_1272_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_n(v_a_1284_, 2);
lean_dec_ref_known(v___x_1283_, 1);
lean_inc(v_a_1270_);
v___f_1285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1285_, 0, v_a_1270_);
lean_closure_set(v___f_1285_, 1, v_e_1269_);
lean_closure_set(v___f_1285_, 2, v_a_1284_);
v___x_1286_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1285_, v___y_1271_, v___y_1272_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1286_, 0);
lean_dec(v_unused_1294_);
v___x_1288_ = v___x_1286_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_dec(v___x_1286_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v_a_1284_);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1284_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_a_1284_);
v_a_1295_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1286_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1286_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_dec_ref(v_e_1269_);
return v___x_1283_;
}
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1305_; 
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_post_1268_);
lean_dec_ref(v_pre_1267_);
v_val_1303_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___x_1280_, 1);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v_val_1303_);
v___x_1305_ = v___x_1278_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_val_1303_);
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
lean_dec_ref(v_e_1269_);
lean_dec_ref(v_post_1268_);
lean_dec_ref(v_pre_1267_);
v_a_1308_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1275_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1275_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1316_, lean_object* v_post_1317_, lean_object* v_e_1318_, lean_object* v_a_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
lean_inc_ref(v_post_1317_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc_ref(v_e_1318_);
v___x_1323_ = lean_apply_4(v_post_1317_, v_e_1318_, v___y_1320_, v___y_1321_, lean_box(0));
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1342_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1342_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1342_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
switch(lean_obj_tag(v_a_1324_))
{
case 0:
{
lean_object* v_e_1328_; lean_object* v___x_1330_; 
lean_dec_ref(v_e_1318_);
lean_dec_ref(v_post_1317_);
lean_dec_ref(v_pre_1316_);
v_e_1328_ = lean_ctor_get(v_a_1324_, 0);
lean_inc_ref(v_e_1328_);
lean_dec_ref_known(v_a_1324_, 1);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_e_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_e_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
case 1:
{
lean_object* v_e_1332_; lean_object* v___x_1333_; 
lean_del_object(v___x_1326_);
lean_dec_ref(v_e_1318_);
v_e_1332_ = lean_ctor_get(v_a_1324_, 0);
lean_inc_ref(v_e_1332_);
lean_dec_ref_known(v_a_1324_, 1);
v___x_1333_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1316_, v_post_1317_, v_e_1332_, v_a_1319_, v___y_1320_, v___y_1321_);
return v___x_1333_;
}
default: 
{
lean_object* v_e_x3f_1334_; 
lean_dec_ref(v_post_1317_);
lean_dec_ref(v_pre_1316_);
v_e_x3f_1334_ = lean_ctor_get(v_a_1324_, 0);
lean_inc(v_e_x3f_1334_);
lean_dec_ref_known(v_a_1324_, 1);
if (lean_obj_tag(v_e_x3f_1334_) == 0)
{
lean_object* v___x_1336_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_e_1318_);
v___x_1336_ = v___x_1326_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_e_1318_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
else
{
lean_object* v_val_1338_; lean_object* v___x_1340_; 
lean_dec_ref(v_e_1318_);
v_val_1338_ = lean_ctor_get(v_e_x3f_1334_, 0);
lean_inc(v_val_1338_);
lean_dec_ref_known(v_e_x3f_1334_, 1);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_val_1338_);
v___x_1340_ = v___x_1326_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_val_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_e_1318_);
lean_dec_ref(v_post_1317_);
lean_dec_ref(v_pre_1316_);
v_a_1343_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1323_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1323_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1351_, lean_object* v_post_1352_, lean_object* v_e_1353_, lean_object* v_a_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1351_, v_post_1352_, v_e_1353_, v_a_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v_a_1354_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1359_, lean_object* v_post_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_bs_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
size_t v_sz_boxed_1368_; size_t v_i_boxed_1369_; lean_object* v_res_1370_; 
v_sz_boxed_1368_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1369_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1359_, v_post_1360_, v_sz_boxed_1368_, v_i_boxed_1369_, v_bs_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1371_, lean_object* v_post_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1371_, v_post_1372_, v_x_1373_, v_x_1374_, v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1381_, lean_object* v_post_1382_, lean_object* v_e_1383_, lean_object* v_a_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1381_, v_post_1382_, v_e_1383_, v_a_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v_a_1384_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1389_, lean_object* v_x_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_apply_1(v_x_1390_, lean_box(0));
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1396_, v_x_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
return v_res_1401_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_unsigned_to_nat(16u);
v___x_1404_ = lean_mk_array(v___x_1403_, v___x_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___x_1405_);
return v___x_1407_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1409_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1409_, 0, lean_box(0));
lean_closure_set(v___x_1409_, 1, lean_box(0));
lean_closure_set(v___x_1409_, 2, v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1410_, lean_object* v_pre_1411_, lean_object* v_post_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_a_1418_; lean_object* v___x_1419_; 
v___x_1416_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1417_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1416_, v___y_1413_, v___y_1414_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1411_, v_post_1412_, v_input_1410_, v_a_1418_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1421_, 0, lean_box(0));
lean_closure_set(v___x_1421_, 1, lean_box(0));
lean_closure_set(v___x_1421_, 2, v_a_1418_);
v___x_1422_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1421_, v___y_1413_, v___y_1414_);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1422_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v___x_1422_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_a_1420_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1420_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_dec(v_a_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1431_, lean_object* v_pre_1432_, lean_object* v_post_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1431_, v_pre_1432_, v_post_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; 
v___f_1444_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1445_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1446_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1440_, v___f_1444_, v___f_1445_, v_a_1441_, v_a_1442_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1452_, lean_object* v_m_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1453_, v_a_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1456_, lean_object* v_m_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1456_, v_m_1457_, v_a_1458_);
lean_dec_ref(v_a_1458_);
lean_dec_ref(v_m_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1460_, lean_object* v_ref_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1461_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1466_, lean_object* v_ref_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1466_, v_ref_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1482_, lean_object* v_x_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1489_, lean_object* v_x_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1489_, v_x_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1496_, lean_object* v_m_1497_, lean_object* v_a_1498_, lean_object* v_b_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1497_, v_a_1498_, v_b_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1501_, lean_object* v_a_1502_, lean_object* v_x_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1502_, v_x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1505_, lean_object* v_a_1506_, lean_object* v_x_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1505_, v_a_1506_, v_x_1507_);
lean_dec(v_x_1507_);
lean_dec_ref(v_a_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1509_, lean_object* v_a_1510_, lean_object* v_x_1511_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1510_, v_x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1513_, lean_object* v_a_1514_, lean_object* v_x_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1513_, v_a_1514_, v_x_1515_);
lean_dec(v_x_1515_);
lean_dec_ref(v_a_1514_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1518_, lean_object* v_data_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1521_, lean_object* v_a_1522_, lean_object* v_b_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1522_, v_b_1523_, v_x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1526_, lean_object* v_i_1527_, lean_object* v_source_1528_, lean_object* v_target_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1527_, v_source_1528_, v_target_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1532_, v_x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v_env_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1538_ = lean_st_ref_get(v___y_1536_);
v_env_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc_ref(v_env_1539_);
lean_dec(v___x_1538_);
v___x_1540_ = l_Lean_isRecCore(v_env_1539_, v_declName_1535_);
v___x_1541_ = lean_box(v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1543_, v___y_1544_);
lean_dec(v___y_1544_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1547_, v___y_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v_env_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1564_ = lean_st_ref_get(v___y_1562_);
v_env_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1564_);
v___x_1566_ = l_Lean_getReducibilityStatusCore(v_env_1565_, v_declName_1561_);
v___x_1567_ = lean_box(v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1569_, v___y_1570_);
lean_dec(v___y_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1595_; 
v___x_1579_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1573_, v___y_1577_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1595_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1595_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
if (v___x_1584_ == 0)
{
uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1585_ = 1;
v___x_1586_ = lean_box(v___x_1585_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1586_);
v___x_1588_ = v___x_1582_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
else
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = 0;
v___x_1591_ = lean_box(v___x_1590_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1591_);
v___x_1593_ = v___x_1582_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1603_, lean_object* v_b_1604_){
_start:
{
lean_object* v_array_1606_; lean_object* v_start_1607_; lean_object* v_stop_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1625_; 
v_array_1606_ = lean_ctor_get(v_a_1603_, 0);
v_start_1607_ = lean_ctor_get(v_a_1603_, 1);
v_stop_1608_ = lean_ctor_get(v_a_1603_, 2);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_a_1603_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1610_ = v_a_1603_;
v_isShared_1611_ = v_isSharedCheck_1625_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_stop_1608_);
lean_inc(v_start_1607_);
lean_inc(v_array_1606_);
lean_dec(v_a_1603_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1625_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_nat_dec_lt(v_start_1607_, v_stop_1608_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_del_object(v___x_1610_);
lean_dec(v_stop_1608_);
lean_dec(v_start_1607_);
lean_dec_ref(v_array_1606_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_b_1604_);
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_add(v_start_1607_, v___x_1615_);
lean_inc_ref(v_array_1606_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 1, v___x_1616_);
v___x_1618_ = v___x_1610_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_array_1606_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_stop_1608_);
v___x_1618_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = lean_array_fget(v_array_1606_, v_start_1607_);
lean_dec(v_start_1607_);
lean_dec_ref(v_array_1606_);
v___x_1620_ = l_Lean_Expr_hasExprMVar(v___x_1619_);
lean_dec(v___x_1619_);
if (v___x_1620_ == 0)
{
v_a_1603_ = v___x_1618_;
v_b_1604_ = v___x_1614_;
goto _start;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_dec_ref_known(v___x_1622_, 1);
v_a_1603_ = v___x_1618_;
v_b_1604_ = v___x_1614_;
goto _start;
}
else
{
lean_dec_ref(v___x_1618_);
return v___x_1622_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1626_, lean_object* v_b_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1626_, v_b_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1638_, uint8_t v_isMatch_1639_, uint8_t v_root_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v___y_1647_; lean_object* v_b_1648_; lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1638_, v_root_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1822_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1822_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1822_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___y_1665_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; 
if (v_root_1640_ == 0)
{
lean_object* v___x_1810_; 
lean_inc(v_a_1660_);
v___x_1810_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1660_);
if (lean_obj_tag(v___x_1810_) == 1)
{
lean_object* v_val_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1821_; 
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v_val_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_val_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set_tag(v___x_1813_, 2);
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_val_1811_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
}
}
else
{
lean_dec(v___x_1810_);
v___y_1675_ = v_a_1641_;
v___y_1676_ = v_a_1642_;
v___y_1677_ = v_a_1643_;
v___y_1678_ = v_a_1644_;
goto v___jp_1674_;
}
}
else
{
v___y_1675_ = v_a_1641_;
v___y_1676_ = v_a_1642_;
v___y_1677_ = v_a_1643_;
v___y_1678_ = v_a_1644_;
goto v___jp_1674_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1666_ = l_Lean_Expr_getAppNumArgs(v_a_1660_);
lean_inc(v___x_1666_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_mk_empty_array_with_capacity(v___x_1666_);
lean_dec(v___x_1666_);
v___x_1669_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1660_, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1667_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1670_);
v___x_1672_ = v___x_1662_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
v___jp_1674_:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Expr_getAppFn(v_a_1660_);
switch(lean_obj_tag(v___x_1679_))
{
case 1:
{
lean_object* v_fvarId_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_del_object(v___x_1662_);
v_fvarId_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_fvarId_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = l_Lean_Expr_getAppNumArgs(v_a_1660_);
lean_inc(v___x_1681_);
v___x_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_fvarId_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_mk_empty_array_with_capacity(v___x_1681_);
lean_dec(v___x_1681_);
v___x_1684_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1660_, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1682_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
case 2:
{
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
if (v_isMatch_1639_ == 0)
{
lean_object* v_mvarId_1687_; lean_object* v___x_1688_; uint8_t v_isDefEqStuckEx_1689_; 
v_mvarId_1687_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_mvarId_1687_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1688_ = l_Lean_Meta_Context_config(v___y_1675_);
v_isDefEqStuckEx_1689_ = lean_ctor_get_uint8(v___x_1688_, 4);
lean_dec_ref(v___x_1688_);
if (v_isDefEqStuckEx_1689_ == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1687_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1704_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_unbox(v_a_1691_);
lean_dec(v_a_1691_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1696_);
v___x_1698_ = v___x_1693_;
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
else
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1700_);
v___x_1702_ = v___x_1693_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
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
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_a_1705_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1690_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1690_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec(v_mvarId_1687_);
v___x_1713_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
return v___x_1714_;
}
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1679_, 1);
v___x_1715_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
case 4:
{
lean_object* v_declName_1717_; lean_object* v___x_1718_; uint8_t v_isDefEqStuckEx_1719_; 
v_declName_1717_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_declName_1717_);
lean_dec_ref_known(v___x_1679_, 2);
v___x_1718_ = l_Lean_Meta_Context_config(v___y_1675_);
v_isDefEqStuckEx_1719_ = lean_ctor_get_uint8(v___x_1718_, 4);
lean_dec_ref(v___x_1718_);
if (v_isDefEqStuckEx_1719_ == 0)
{
v___y_1665_ = v_declName_1717_;
goto v___jp_1664_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = l_Lean_Expr_hasExprMVar(v_a_1660_);
if (v___x_1720_ == 0)
{
v___y_1665_ = v_declName_1717_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1721_; 
lean_inc(v_declName_1717_);
v___x_1721_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1717_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; uint8_t v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = lean_unbox(v_a_1722_);
lean_dec(v_a_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v_env_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_st_ref_get(v___y_1678_);
v_env_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_ref(v_env_1725_);
lean_dec(v___x_1724_);
v___x_1726_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1725_, v_a_1660_);
if (lean_obj_tag(v___x_1726_) == 1)
{
lean_object* v_val_1727_; lean_object* v_numDiscrs_1728_; lean_object* v_nargs_1729_; lean_object* v_dummy_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_val_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v_numDiscrs_1728_ = lean_ctor_get(v_val_1727_, 1);
lean_inc(v_numDiscrs_1728_);
v_nargs_1729_ = l_Lean_Expr_getAppNumArgs(v_a_1660_);
v_dummy_1730_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1729_);
v___x_1731_ = lean_mk_array(v_nargs_1729_, v_dummy_1730_);
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_sub(v_nargs_1729_, v___x_1732_);
lean_dec(v_nargs_1729_);
lean_inc(v_a_1660_);
v___x_1734_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1660_, v___x_1731_, v___x_1733_);
v___x_1735_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1727_);
lean_dec(v_val_1727_);
v___x_1736_ = lean_nat_add(v___x_1735_, v_numDiscrs_1728_);
lean_dec(v_numDiscrs_1728_);
v___x_1737_ = l_Array_toSubarray___redArg(v___x_1734_, v___x_1735_, v___x_1736_);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1737_, v___x_1738_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_dec_ref_known(v___x_1739_, 1);
v___y_1665_ = v_declName_1717_;
goto v___jp_1664_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_declName_1717_);
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v___x_1748_; lean_object* v_a_1749_; uint8_t v___x_1750_; 
lean_dec(v___x_1726_);
lean_inc(v_declName_1717_);
v___x_1748_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1717_, v___y_1678_);
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___x_1748_);
v___x_1750_ = lean_unbox(v_a_1749_);
lean_dec(v_a_1749_);
if (v___x_1750_ == 0)
{
v___y_1665_ = v_declName_1717_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec_ref_known(v___x_1751_, 1);
v___y_1665_ = v_declName_1717_;
goto v___jp_1664_;
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_declName_1717_);
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_dec_ref_known(v___x_1760_, 1);
v___y_1665_ = v_declName_1717_;
goto v___jp_1664_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_declName_1717_);
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
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
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_declName_1717_);
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v_a_1769_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1721_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1721_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1777_; lean_object* v_body_1778_; uint8_t v___x_1779_; 
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v_binderType_1777_ = lean_ctor_get(v___x_1679_, 1);
lean_inc_ref(v_binderType_1777_);
v_body_1778_ = lean_ctor_get(v___x_1679_, 2);
lean_inc_ref(v_body_1778_);
lean_dec_ref_known(v___x_1679_, 3);
v___x_1779_ = l_Lean_Expr_hasLooseBVars(v_body_1778_);
if (v___x_1779_ == 0)
{
v___y_1647_ = v_binderType_1777_;
v_b_1648_ = v_body_1778_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1778_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___y_1647_ = v_binderType_1777_;
v_b_1648_ = v_a_1781_;
goto v___jp_1646_;
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_binderType_1777_);
v_a_1782_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1780_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v_a_1790_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_ref(v_a_1790_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1791_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_a_1790_);
v___x_1792_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
case 11:
{
lean_object* v_typeName_1795_; lean_object* v_idx_1796_; lean_object* v_struct_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_del_object(v___x_1662_);
v_typeName_1795_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_typeName_1795_);
v_idx_1796_ = lean_ctor_get(v___x_1679_, 1);
lean_inc(v_idx_1796_);
v_struct_1797_ = lean_ctor_get(v___x_1679_, 2);
lean_inc_ref(v_struct_1797_);
lean_dec_ref_known(v___x_1679_, 3);
v___x_1798_ = l_Lean_Expr_getAppNumArgs(v_a_1660_);
lean_inc(v___x_1798_);
v___x_1799_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1799_, 0, v_typeName_1795_);
lean_ctor_set(v___x_1799_, 1, v_idx_1796_);
lean_ctor_set(v___x_1799_, 2, v___x_1798_);
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = lean_mk_empty_array_with_capacity(v___x_1800_);
v___x_1802_ = lean_array_push(v___x_1801_, v_struct_1797_);
v___x_1803_ = lean_mk_empty_array_with_capacity(v___x_1798_);
lean_dec(v___x_1798_);
v___x_1804_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1660_, v___x_1803_);
v___x_1805_ = l_Array_append___redArg(v___x_1802_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1799_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
default: 
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec_ref(v___x_1679_);
lean_del_object(v___x_1662_);
lean_dec(v_a_1660_);
v___x_1808_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1659_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1659_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
v___jp_1646_:
{
uint8_t v___x_1649_; 
v___x_1649_ = l_Lean_Expr_hasLooseBVars(v_b_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1650_ = lean_box(5);
v___x_1651_ = lean_unsigned_to_nat(2u);
v___x_1652_ = lean_mk_empty_array_with_capacity(v___x_1651_);
v___x_1653_ = lean_array_push(v___x_1652_, v___y_1647_);
v___x_1654_ = lean_array_push(v___x_1653_, v_b_1648_);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1650_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec_ref(v_b_1648_);
lean_dec_ref(v___y_1647_);
v___x_1657_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1831_, lean_object* v_isMatch_1832_, lean_object* v_root_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
uint8_t v_isMatch_boxed_1839_; uint8_t v_root_boxed_1840_; lean_object* v_res_1841_; 
v_isMatch_boxed_1839_ = lean_unbox(v_isMatch_1832_);
v_root_boxed_1840_ = lean_unbox(v_root_1833_);
v_res_1841_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1831_, v_isMatch_boxed_1839_, v_root_boxed_1840_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1842_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1856_, lean_object* v_R_1857_, lean_object* v_a_1858_, lean_object* v_b_1859_, lean_object* v_c_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1858_, v_b_1859_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1867_, lean_object* v_R_1868_, lean_object* v_a_1869_, lean_object* v_b_1870_, lean_object* v_c_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1867_, v_R_1868_, v_a_1869_, v_b_1870_, v_c_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1878_, uint8_t v_root_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
uint8_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = 1;
v___x_1886_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1878_, v___x_1885_, v_root_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1887_, lean_object* v_root_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
uint8_t v_root_boxed_1894_; lean_object* v_res_1895_; 
v_root_boxed_1894_ = lean_unbox(v_root_1888_);
v_res_1895_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1887_, v_root_boxed_1894_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1895_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_unsigned_to_nat(16u);
v___x_1900_ = lean_mk_array(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1901_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1906_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_1907_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___x_1908_);
lean_ctor_set(v___x_1910_, 2, v___x_1907_);
lean_ctor_set(v___x_1910_, 3, v___x_1906_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4);
return v___x_1912_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1918_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v___x_1919_);
lean_ctor_set(v___x_1921_, 2, v___x_1918_);
lean_ctor_set(v___x_1921_, 3, v___x_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v_values_1926_; lean_object* v_star_1927_; lean_object* v_children_1928_; lean_object* v_pending_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1937_; 
v_values_1926_ = lean_ctor_get(v_x_1924_, 0);
v_star_1927_ = lean_ctor_get(v_x_1924_, 1);
v_children_1928_ = lean_ctor_get(v_x_1924_, 2);
v_pending_1929_ = lean_ctor_get(v_x_1924_, 3);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_x_1924_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1931_ = v_x_1924_;
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_pending_1929_);
lean_inc(v_children_1928_);
lean_inc(v_star_1927_);
lean_inc(v_values_1926_);
lean_dec(v_x_1924_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = lean_array_push(v_pending_1929_, v_x_1925_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 3, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_values_1926_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_star_1927_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_children_1928_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v___x_1933_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1939_, v_x_1940_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1942_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = lean_mk_empty_array_with_capacity(v___x_1943_);
v___x_1945_ = lean_array_push(v___x_1944_, v___x_1942_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1947_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v_env_1958_; lean_object* v___x_1959_; lean_object* v_mctx_1960_; lean_object* v_lctx_1961_; lean_object* v_options_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1957_ = lean_st_ref_get(v___y_1955_);
v_env_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc_ref(v_env_1958_);
lean_dec(v___x_1957_);
v___x_1959_ = lean_st_ref_get(v___y_1953_);
v_mctx_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_ref(v_mctx_1960_);
lean_dec(v___x_1959_);
v_lctx_1961_ = lean_ctor_get(v___y_1952_, 2);
v_options_1962_ = lean_ctor_get(v___y_1954_, 2);
lean_inc_ref(v_options_1962_);
lean_inc_ref(v_lctx_1961_);
v___x_1963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1963_, 0, v_env_1958_);
lean_ctor_set(v___x_1963_, 1, v_mctx_1960_);
lean_ctor_set(v___x_1963_, 2, v_lctx_1961_);
lean_ctor_set(v___x_1963_, 3, v_options_1962_);
v___x_1964_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_msgData_1951_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_ref_1979_; lean_object* v___x_1980_; lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1989_; 
v_ref_1979_ = lean_ctor_get(v___y_1976_, 5);
v___x_1980_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1989_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
lean_inc(v_ref_1979_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_ref_1979_);
lean_ctor_set(v___x_1985_, 1, v_a_1981_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 1);
lean_ctor_set(v___x_1983_, 0, v___x_1985_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1996_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1999_ = l_Lean_stringToMessageData(v___x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_2000_, lean_object* v_todo_2001_, lean_object* v_e_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_2002_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_2002_, v_root_2000_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2149_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2149_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2149_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_v_2015_; lean_object* v___x_2021_; lean_object* v_k_2023_; lean_object* v_nargs_2024_; lean_object* v_todo_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; 
v___x_2021_ = l_Lean_Expr_getAppFn(v_a_2010_);
switch(lean_obj_tag(v___x_2021_))
{
case 9:
{
lean_object* v_a_2068_; 
lean_dec(v_a_2010_);
v_a_2068_ = lean_ctor_get(v___x_2021_, 0);
lean_inc_ref(v_a_2068_);
lean_dec_ref_known(v___x_2021_, 1);
v_v_2015_ = v_a_2068_;
goto v___jp_2014_;
}
case 4:
{
lean_object* v_declName_2069_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; 
v_declName_2069_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_declName_2069_);
if (v_root_2000_ == 0)
{
lean_object* v___x_2077_; 
lean_inc(v_a_2010_);
v___x_2077_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_2010_);
if (lean_obj_tag(v___x_2077_) == 1)
{
lean_object* v_val_2078_; 
lean_dec_ref_known(v___x_2021_, 2);
lean_dec(v_declName_2069_);
lean_dec(v_a_2010_);
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v_v_2015_ = v_val_2078_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2079_; 
lean_dec(v___x_2077_);
lean_del_object(v___x_2012_);
v___x_2079_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2069_, v_a_2010_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2090_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2090_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_unbox(v_a_2080_);
lean_dec(v_a_2080_);
if (v___x_2084_ == 0)
{
lean_del_object(v___x_2082_);
v___y_2071_ = v_a_2003_;
v___y_2072_ = v_a_2004_;
v___y_2073_ = v_a_2005_;
v___y_2074_ = v_a_2006_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2021_, 2);
lean_dec(v_declName_2069_);
lean_dec(v_a_2010_);
v___x_2085_ = lean_box(3);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v_todo_2001_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2086_);
v___x_2088_ = v___x_2082_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
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
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref_known(v___x_2021_, 2);
lean_dec(v_declName_2069_);
lean_dec(v_a_2010_);
lean_dec_ref(v_todo_2001_);
v_a_2091_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2079_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2079_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
else
{
lean_del_object(v___x_2012_);
v___y_2071_ = v_a_2003_;
v___y_2072_ = v_a_2004_;
v___y_2073_ = v_a_2005_;
v___y_2074_ = v_a_2006_;
goto v___jp_2070_;
}
v___jp_2070_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = l_Lean_Expr_getAppNumArgs(v_a_2010_);
lean_inc(v___x_2075_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_declName_2069_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v_k_2023_ = v___x_2076_;
v_nargs_2024_ = v___x_2075_;
v_todo_2025_ = v_todo_2001_;
v___y_2026_ = v___y_2071_;
v___y_2027_ = v___y_2072_;
v___y_2028_ = v___y_2073_;
v___y_2029_ = v___y_2074_;
goto v___jp_2022_;
}
}
case 11:
{
lean_object* v_typeName_2099_; lean_object* v_idx_2100_; lean_object* v_struct_2101_; lean_object* v___x_2102_; lean_object* v___y_2104_; lean_object* v_env_2108_; uint8_t v___x_2109_; 
lean_del_object(v___x_2012_);
v_typeName_2099_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_typeName_2099_);
v_idx_2100_ = lean_ctor_get(v___x_2021_, 1);
lean_inc(v_idx_2100_);
v_struct_2101_ = lean_ctor_get(v___x_2021_, 2);
lean_inc_ref(v_struct_2101_);
v___x_2102_ = lean_st_ref_get(v_a_2006_);
v_env_2108_ = lean_ctor_get(v___x_2102_, 0);
lean_inc_ref(v_env_2108_);
lean_dec(v___x_2102_);
v___x_2109_ = l_Lean_isClass(v_env_2108_, v_typeName_2099_);
if (v___x_2109_ == 0)
{
v___y_2104_ = v_struct_2101_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2101_);
v___y_2104_ = v___x_2110_;
goto v___jp_2103_;
}
v___jp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = l_Lean_Expr_getAppNumArgs(v_a_2010_);
lean_inc(v___x_2105_);
v___x_2106_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2106_, 0, v_typeName_2099_);
lean_ctor_set(v___x_2106_, 1, v_idx_2100_);
lean_ctor_set(v___x_2106_, 2, v___x_2105_);
v___x_2107_ = lean_array_push(v_todo_2001_, v___y_2104_);
v_k_2023_ = v___x_2106_;
v_nargs_2024_ = v___x_2105_;
v_todo_2025_ = v___x_2107_;
v___y_2026_ = v_a_2003_;
v___y_2027_ = v_a_2004_;
v___y_2028_ = v_a_2005_;
v___y_2029_ = v_a_2006_;
goto v___jp_2022_;
}
}
case 1:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref_known(v___x_2021_, 1);
lean_del_object(v___x_2012_);
lean_dec(v_a_2010_);
v___x_2111_ = lean_box(3);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v_todo_2001_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
case 2:
{
lean_object* v_mvarId_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
lean_del_object(v___x_2012_);
lean_dec(v_a_2010_);
v_mvarId_2114_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_mvarId_2114_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2115_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2116_ = l_Lean_instBEqMVarId_beq(v_mvarId_2114_, v___x_2115_);
lean_dec(v_mvarId_2114_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref(v_todo_2001_);
v___x_2117_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2118_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2117_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = lean_box(3);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v_todo_2001_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
case 7:
{
lean_object* v_binderType_2122_; lean_object* v_body_2123_; lean_object* v_b_2125_; uint8_t v___x_2135_; 
lean_del_object(v___x_2012_);
lean_dec(v_a_2010_);
v_binderType_2122_ = lean_ctor_get(v___x_2021_, 1);
lean_inc_ref(v_binderType_2122_);
v_body_2123_ = lean_ctor_get(v___x_2021_, 2);
lean_inc_ref(v_body_2123_);
lean_dec_ref_known(v___x_2021_, 3);
v___x_2135_ = l_Lean_Expr_hasLooseBVars(v_body_2123_);
if (v___x_2135_ == 0)
{
v_b_2125_ = v_body_2123_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2123_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v_b_2125_ = v_a_2137_;
goto v___jp_2124_;
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_binderType_2122_);
lean_dec_ref(v_todo_2001_);
v_a_2138_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2136_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2136_);
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
v___jp_2124_:
{
uint8_t v___x_2126_; 
v___x_2126_ = l_Lean_Expr_hasLooseBVars(v_b_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2127_ = lean_box(5);
v___x_2128_ = lean_array_push(v_todo_2001_, v_binderType_2122_);
v___x_2129_ = lean_array_push(v___x_2128_, v_b_2125_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2127_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref(v_b_2125_);
lean_dec_ref(v_binderType_2122_);
v___x_2132_ = lean_box(4);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v_todo_2001_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
}
default: 
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref(v___x_2021_);
lean_del_object(v___x_2012_);
lean_dec(v_a_2010_);
v___x_2146_ = lean_box(4);
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v_todo_2001_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
v___jp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2016_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_v_2015_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v_todo_2001_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2017_);
v___x_2019_ = v___x_2012_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
v___jp_2022_:
{
lean_object* v___x_2030_; 
lean_inc(v_nargs_2024_);
v___x_2030_ = l_Lean_Meta_getFunInfoNArgs(v___x_2021_, v_nargs_2024_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v_paramInfo_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2058_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v_paramInfo_2032_ = lean_ctor_get(v_a_2031_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_a_2031_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_a_2031_, 1);
lean_dec(v_unused_2059_);
v___x_2034_ = v_a_2031_;
v_isShared_2035_ = v_isSharedCheck_2058_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_paramInfo_2032_);
lean_dec(v_a_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2058_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = lean_nat_sub(v_nargs_2024_, v___x_2036_);
lean_dec(v_nargs_2024_);
v___x_2038_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2032_, v___x_2037_, v_a_2010_, v_todo_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec_ref(v_paramInfo_2032_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2049_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_a_2039_);
lean_ctor_set(v___x_2034_, 0, v_k_2023_);
v___x_2044_ = v___x_2034_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_k_2023_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2044_);
v___x_2046_ = v___x_2041_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_del_object(v___x_2034_);
lean_dec(v_k_2023_);
v_a_2050_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2038_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2038_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v_todo_2025_);
lean_dec(v_nargs_2024_);
lean_dec(v_k_2023_);
lean_dec(v_a_2010_);
v_a_2060_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2030_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2030_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v_todo_2001_);
v_a_2150_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2009_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2009_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v_e_2002_);
v___x_2158_ = lean_box(3);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v_todo_2001_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2161_, lean_object* v_todo_2162_, lean_object* v_e_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
uint8_t v_root_boxed_2169_; lean_object* v_res_2170_; 
v_root_boxed_2169_ = lean_unbox(v_root_2161_);
v_res_2170_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2169_, v_todo_2162_, v_e_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2171_, lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2179_, v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2186_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_unsigned_to_nat(8u);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = 1;
v___x_2195_ = lean_unsigned_to_nat(8u);
v___x_2196_ = lean_mk_empty_array_with_capacity(v___x_2195_);
v___x_2197_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2194_, v___x_2196_, v_e_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2205_, uint8_t v_root_2206_, lean_object* v_todo_2207_, lean_object* v_keys_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2214_ = lean_array_get_size(v_todo_2207_);
v___x_2215_ = lean_unsigned_to_nat(0u);
v___x_2216_ = lean_nat_dec_eq(v___x_2214_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v_e_2220_; lean_object* v_todo_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2217_ = l_Lean_instInhabitedExpr;
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_sub(v___x_2214_, v___x_2218_);
v_e_2220_ = lean_array_get(v___x_2217_, v_todo_2207_, v___x_2219_);
lean_dec(v___x_2219_);
v_todo_2221_ = lean_array_pop(v_todo_2207_);
v___x_2222_ = lean_box(v_root_2206_);
lean_inc_ref(v_op_2205_);
lean_inc(v_a_2212_);
lean_inc_ref(v_a_2211_);
lean_inc(v_a_2210_);
lean_inc_ref(v_a_2209_);
v___x_2223_ = lean_apply_8(v_op_2205_, v___x_2222_, v_todo_2221_, v_e_2220_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, lean_box(0));
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v_fst_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v_fst_2225_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_fst_2225_);
v_snd_2226_ = lean_ctor_get(v_a_2224_, 1);
lean_inc(v_snd_2226_);
lean_dec(v_a_2224_);
v___x_2227_ = lean_array_push(v_keys_2208_, v_fst_2225_);
v_root_2206_ = v___x_2216_;
v_todo_2207_ = v_snd_2226_;
v_keys_2208_ = v___x_2227_;
goto _start;
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v_keys_2208_);
lean_dec_ref(v_op_2205_);
v_a_2229_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2223_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2223_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v___x_2237_; 
lean_dec_ref(v_todo_2207_);
lean_dec_ref(v_op_2205_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v_keys_2208_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2238_, lean_object* v_root_2239_, lean_object* v_todo_2240_, lean_object* v_keys_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
uint8_t v_root_boxed_2247_; lean_object* v_res_2248_; 
v_root_boxed_2247_ = lean_unbox(v_root_2239_);
v_res_2248_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2238_, v_root_boxed_2247_, v_todo_2240_, v_keys_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
lean_dec(v_a_2245_);
lean_dec_ref(v_a_2244_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_op_2256_; lean_object* v___x_2257_; lean_object* v_todo_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_op_2256_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2257_ = lean_unsigned_to_nat(8u);
v_todo_2258_ = lean_mk_empty_array_with_capacity(v___x_2257_);
v___x_2259_ = 1;
lean_inc_ref(v_todo_2258_);
v___x_2260_ = lean_array_push(v_todo_2258_, v_e_2250_);
v___x_2261_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2256_, v___x_2259_, v___x_2260_, v_todo_2258_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2269_, lean_object* v_todo_2270_, lean_object* v_e_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
uint8_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = 1;
v___x_2278_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2271_, v___x_2277_, v_root_2269_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2296_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2296_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2296_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_fst_2283_; lean_object* v_snd_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2295_; 
v_fst_2283_ = lean_ctor_get(v_a_2279_, 0);
v_snd_2284_ = lean_ctor_get(v_a_2279_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_a_2279_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2286_ = v_a_2279_;
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_snd_2284_);
lean_inc(v_fst_2283_);
lean_dec(v_a_2279_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = l_Array_append___redArg(v_todo_2270_, v_snd_2284_);
lean_dec(v_snd_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 1, v___x_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_fst_2283_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2290_);
v___x_2292_ = v___x_2281_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2270_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2297_, lean_object* v_todo_2298_, lean_object* v_e_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_root_boxed_2305_; lean_object* v_res_2306_; 
v_root_boxed_2305_ = lean_unbox(v_root_2297_);
v_res_2306_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2305_, v_todo_2298_, v_e_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_op_2314_; lean_object* v___x_2315_; lean_object* v_todo_2316_; uint8_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_op_2314_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2315_ = lean_unsigned_to_nat(8u);
v_todo_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
v___x_2317_ = 1;
lean_inc_ref(v_todo_2316_);
v___x_2318_ = lean_array_push(v_todo_2316_, v_e_2308_);
v___x_2319_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2314_, v___x_2317_, v___x_2318_, v_todo_2316_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2327_, lean_object* v_m_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_tries_2334_; lean_object* v_roots_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2376_; 
v_tries_2334_ = lean_ctor_get(v_d_2327_, 0);
v_roots_2335_ = lean_ctor_get(v_d_2327_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_d_2327_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2337_ = v_d_2327_;
v_isShared_2338_ = v_isSharedCheck_2376_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_roots_2335_);
lean_inc(v_tries_2334_);
lean_dec(v_d_2327_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2376_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v_keyedConfig_2340_; uint8_t v_trackZetaDelta_2341_; lean_object* v_zetaDeltaSet_2342_; lean_object* v_lctx_2343_; lean_object* v_localInstances_2344_; lean_object* v_defEqCtx_x3f_2345_; lean_object* v_synthPendingDepth_2346_; lean_object* v_customCanUnfoldPredicate_x3f_2347_; uint8_t v_univApprox_2348_; uint8_t v_inTypeClassResolution_2349_; uint8_t v_cacheInferType_2350_; uint8_t v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2339_ = lean_st_mk_ref(v_tries_2334_);
v_keyedConfig_2340_ = lean_ctor_get(v_a_2329_, 0);
v_trackZetaDelta_2341_ = lean_ctor_get_uint8(v_a_2329_, sizeof(void*)*7);
v_zetaDeltaSet_2342_ = lean_ctor_get(v_a_2329_, 1);
v_lctx_2343_ = lean_ctor_get(v_a_2329_, 2);
v_localInstances_2344_ = lean_ctor_get(v_a_2329_, 3);
v_defEqCtx_x3f_2345_ = lean_ctor_get(v_a_2329_, 4);
v_synthPendingDepth_2346_ = lean_ctor_get(v_a_2329_, 5);
v_customCanUnfoldPredicate_x3f_2347_ = lean_ctor_get(v_a_2329_, 6);
v_univApprox_2348_ = lean_ctor_get_uint8(v_a_2329_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2349_ = lean_ctor_get_uint8(v_a_2329_, sizeof(void*)*7 + 2);
v_cacheInferType_2350_ = lean_ctor_get_uint8(v_a_2329_, sizeof(void*)*7 + 3);
v___x_2351_ = 2;
lean_inc_ref(v_keyedConfig_2340_);
v___x_2352_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2351_, v_keyedConfig_2340_);
lean_inc(v_customCanUnfoldPredicate_x3f_2347_);
lean_inc(v_synthPendingDepth_2346_);
lean_inc(v_defEqCtx_x3f_2345_);
lean_inc_ref(v_localInstances_2344_);
lean_inc_ref(v_lctx_2343_);
lean_inc(v_zetaDeltaSet_2342_);
v___x_2353_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v_zetaDeltaSet_2342_);
lean_ctor_set(v___x_2353_, 2, v_lctx_2343_);
lean_ctor_set(v___x_2353_, 3, v_localInstances_2344_);
lean_ctor_set(v___x_2353_, 4, v_defEqCtx_x3f_2345_);
lean_ctor_set(v___x_2353_, 5, v_synthPendingDepth_2346_);
lean_ctor_set(v___x_2353_, 6, v_customCanUnfoldPredicate_x3f_2347_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7, v_trackZetaDelta_2341_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7 + 1, v_univApprox_2348_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2349_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7 + 3, v_cacheInferType_2350_);
lean_inc(v_a_2332_);
lean_inc_ref(v_a_2331_);
lean_inc(v_a_2330_);
lean_inc(v___x_2339_);
v___x_2354_ = lean_apply_6(v_m_2328_, v___x_2339_, v___x_2353_, v_a_2330_, v_a_2331_, v_a_2332_, lean_box(0));
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2367_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2367_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2367_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2359_ = lean_st_ref_get(v___x_2339_);
lean_dec(v___x_2339_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2359_);
v___x_2361_ = v___x_2337_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_roots_2335_);
v___x_2361_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_a_2355_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2362_);
v___x_2364_ = v___x_2357_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v___x_2339_);
lean_del_object(v___x_2337_);
lean_dec_ref(v_roots_2335_);
v_a_2368_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2354_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2354_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2377_, lean_object* v_m_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2377_, v_m_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2385_, lean_object* v_00_u03b2_2386_, lean_object* v_d_2387_, lean_object* v_m_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2387_, v_m_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_00_u03b2_2396_, lean_object* v_d_2397_, lean_object* v_m_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2395_, v_00_u03b2_2396_, v_d_2397_, v_m_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2405_, lean_object* v_v_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2409_ = lean_st_ref_take(v_a_2407_);
v___x_2410_ = lean_array_set(v___x_2409_, v_i_2405_, v_v_2406_);
v___x_2411_ = lean_st_ref_set(v_a_2407_, v___x_2410_);
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2414_, lean_object* v_v_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2414_, v_v_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec(v_i_2414_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2419_, lean_object* v_i_2420_, lean_object* v_v_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2420_, v_v_2421_, v_a_2422_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2429_, lean_object* v_i_2430_, lean_object* v_v_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2429_, v_i_2430_, v_v_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec(v_i_2430_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_sz_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v_sz_2441_ = lean_array_get_size(v_a_2440_);
v___x_2442_ = lean_unsigned_to_nat(0u);
v___x_2443_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2444_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2445_ = lean_unsigned_to_nat(1u);
v___x_2446_ = lean_mk_empty_array_with_capacity(v___x_2445_);
v___x_2447_ = lean_array_push(v___x_2446_, v_e_2439_);
v___x_2448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2443_);
lean_ctor_set(v___x_2448_, 1, v___x_2442_);
lean_ctor_set(v___x_2448_, 2, v___x_2444_);
lean_ctor_set(v___x_2448_, 3, v___x_2447_);
v___x_2449_ = lean_array_push(v_a_2440_, v___x_2448_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v_sz_2441_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2451_, lean_object* v_e_2452_){
_start:
{
lean_object* v_modifyGet_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; 
v_modifyGet_2453_ = lean_ctor_get(v_inst_2451_, 2);
lean_inc(v_modifyGet_2453_);
lean_dec_ref(v_inst_2451_);
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2454_, 0, v_e_2452_);
v___x_2455_ = lean_apply_2(v_modifyGet_2453_, lean_box(0), v___f_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2456_, lean_object* v_00_u03b1_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_e_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2459_, v_e_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2462_, lean_object* v_00_u03b1_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_e_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2462_, v_00_u03b1_2463_, v_inst_2464_, v_inst_2465_, v_e_2466_);
lean_dec_ref(v_inst_2464_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2468_, lean_object* v_e_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; lean_object* v_fst_2474_; lean_object* v_snd_2475_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2472_ = lean_st_ref_take(v_a_2470_);
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_array_get_size(v___x_2472_);
v___x_2480_ = lean_nat_dec_lt(v_i_2468_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_dec_ref(v_e_2469_);
v_fst_2474_ = v___x_2478_;
v_snd_2475_ = v___x_2472_;
goto v___jp_2473_;
}
else
{
lean_object* v_v_2481_; lean_object* v_xs_x27_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_v_2481_ = lean_array_fget(v___x_2472_, v_i_2468_);
v_xs_x27_2482_ = lean_array_fset(v___x_2472_, v_i_2468_, v___x_2478_);
v___x_2483_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2481_, v_e_2469_);
v___x_2484_ = lean_array_fset(v_xs_x27_2482_, v_i_2468_, v___x_2483_);
v_fst_2474_ = v___x_2478_;
v_snd_2475_ = v___x_2484_;
goto v___jp_2473_;
}
v___jp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_st_ref_set(v_a_2470_, v_snd_2475_);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v_fst_2474_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2485_, lean_object* v_e_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2485_, v_e_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec(v_i_2485_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2490_, lean_object* v_i_2491_, lean_object* v_e_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2491_, v_e_2492_, v_a_2493_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2500_, lean_object* v_i_2501_, lean_object* v_e_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2500_, v_i_2501_, v_e_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec(v_i_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; 
lean_inc(v___y_2511_);
v___x_2517_ = lean_apply_6(v_x_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, lean_box(0));
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2519_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2526_, lean_object* v_localInsts_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___f_2535_; lean_object* v___x_2536_; 
lean_inc(v___y_2529_);
v___f_2535_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2535_, 0, v_x_2528_);
lean_closure_set(v___f_2535_, 1, v___y_2529_);
v___x_2536_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2526_, v_localInsts_2527_, v___f_2535_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2536_) == 0)
{
return v___x_2536_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2545_, lean_object* v_localInsts_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2545_, v_localInsts_2546_, v_x_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2555_, lean_object* v_00_u03b1_2556_, lean_object* v_lctx_2557_, lean_object* v_localInsts_2558_, lean_object* v_x_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2557_, v_localInsts_2558_, v_x_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_00_u03b1_2568_, lean_object* v_lctx_2569_, lean_object* v_localInsts_2570_, lean_object* v_x_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2567_, v_00_u03b1_2568_, v_lctx_2569_, v_localInsts_2570_, v_x_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; lean_object* v_sz_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2582_ = lean_st_ref_take(v___y_2580_);
v_sz_2583_ = lean_array_get_size(v___x_2582_);
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2586_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2587_ = lean_unsigned_to_nat(1u);
v___x_2588_ = lean_mk_empty_array_with_capacity(v___x_2587_);
v___x_2589_ = lean_array_push(v___x_2588_, v_e_2579_);
v___x_2590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2585_);
lean_ctor_set(v___x_2590_, 1, v___x_2584_);
lean_ctor_set(v___x_2590_, 2, v___x_2586_);
lean_ctor_set(v___x_2590_, 3, v___x_2589_);
v___x_2591_ = lean_array_push(v___x_2582_, v___x_2590_);
v___x_2592_ = lean_st_ref_set(v___y_2580_, v___x_2591_);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v_sz_2583_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2594_, v___y_2595_);
lean_dec(v___y_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2598_, lean_object* v_e_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2599_, v___y_2600_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2607_, lean_object* v_e_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2607_, v_e_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2616_, lean_object* v_todo_2617_, lean_object* v_e_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2616_, v_todo_2617_, v_e_2618_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2626_, lean_object* v_todo_2627_, lean_object* v_e_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
uint8_t v___x_4138__boxed_2635_; lean_object* v_res_2636_; 
v___x_4138__boxed_2635_ = lean_unbox(v___x_2626_);
v_res_2636_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_4138__boxed_2635_, v_todo_2627_, v_e_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2637_, lean_object* v_b_2638_, lean_object* v_x_2639_){
_start:
{
if (lean_obj_tag(v_x_2639_) == 0)
{
lean_dec(v_b_2638_);
lean_dec(v_a_2637_);
return v_x_2639_;
}
else
{
lean_object* v_key_2640_; lean_object* v_value_2641_; lean_object* v_tail_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2654_; 
v_key_2640_ = lean_ctor_get(v_x_2639_, 0);
v_value_2641_ = lean_ctor_get(v_x_2639_, 1);
v_tail_2642_ = lean_ctor_get(v_x_2639_, 2);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_x_2639_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2644_ = v_x_2639_;
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_tail_2642_);
lean_inc(v_value_2641_);
lean_inc(v_key_2640_);
lean_dec(v_x_2639_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; 
v___x_2646_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2640_, v_a_2637_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2637_, v_b_2638_, v_tail_2642_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 2, v___x_2647_);
v___x_2649_ = v___x_2644_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_key_2640_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_value_2641_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
else
{
lean_object* v___x_2652_; 
lean_dec(v_value_2641_);
lean_dec(v_key_2640_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v_b_2638_);
lean_ctor_set(v___x_2644_, 0, v_a_2637_);
v___x_2652_ = v___x_2644_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2637_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_b_2638_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_tail_2642_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2655_, lean_object* v_x_2656_){
_start:
{
if (lean_obj_tag(v_x_2656_) == 0)
{
uint8_t v___x_2657_; 
v___x_2657_ = 0;
return v___x_2657_;
}
else
{
lean_object* v_key_2658_; lean_object* v_tail_2659_; uint8_t v___x_2660_; 
v_key_2658_ = lean_ctor_get(v_x_2656_, 0);
v_tail_2659_ = lean_ctor_get(v_x_2656_, 2);
v___x_2660_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2658_, v_a_2655_);
if (v___x_2660_ == 0)
{
v_x_2656_ = v_tail_2659_;
goto _start;
}
else
{
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2662_, lean_object* v_x_2663_){
_start:
{
uint8_t v_res_2664_; lean_object* v_r_2665_; 
v_res_2664_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2662_, v_x_2663_);
lean_dec(v_x_2663_);
lean_dec(v_a_2662_);
v_r_2665_ = lean_box(v_res_2664_);
return v_r_2665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2666_, lean_object* v_x_2667_){
_start:
{
if (lean_obj_tag(v_x_2667_) == 0)
{
return v_x_2666_;
}
else
{
lean_object* v_key_2668_; lean_object* v_value_2669_; lean_object* v_tail_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2693_; 
v_key_2668_ = lean_ctor_get(v_x_2667_, 0);
v_value_2669_ = lean_ctor_get(v_x_2667_, 1);
v_tail_2670_ = lean_ctor_get(v_x_2667_, 2);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_x_2667_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2672_ = v_x_2667_;
v_isShared_2673_ = v_isSharedCheck_2693_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_tail_2670_);
lean_inc(v_value_2669_);
lean_inc(v_key_2668_);
lean_dec(v_x_2667_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2693_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; uint64_t v___x_2675_; uint64_t v___x_2676_; uint64_t v___x_2677_; uint64_t v_fold_2678_; uint64_t v___x_2679_; uint64_t v___x_2680_; uint64_t v___x_2681_; size_t v___x_2682_; size_t v___x_2683_; size_t v___x_2684_; size_t v___x_2685_; size_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2674_ = lean_array_get_size(v_x_2666_);
v___x_2675_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2668_);
v___x_2676_ = 32ULL;
v___x_2677_ = lean_uint64_shift_right(v___x_2675_, v___x_2676_);
v_fold_2678_ = lean_uint64_xor(v___x_2675_, v___x_2677_);
v___x_2679_ = 16ULL;
v___x_2680_ = lean_uint64_shift_right(v_fold_2678_, v___x_2679_);
v___x_2681_ = lean_uint64_xor(v_fold_2678_, v___x_2680_);
v___x_2682_ = lean_uint64_to_usize(v___x_2681_);
v___x_2683_ = lean_usize_of_nat(v___x_2674_);
v___x_2684_ = ((size_t)1ULL);
v___x_2685_ = lean_usize_sub(v___x_2683_, v___x_2684_);
v___x_2686_ = lean_usize_land(v___x_2682_, v___x_2685_);
v___x_2687_ = lean_array_uget_borrowed(v_x_2666_, v___x_2686_);
lean_inc(v___x_2687_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 2, v___x_2687_);
v___x_2689_ = v___x_2672_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_key_2668_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_value_2669_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_array_uset(v_x_2666_, v___x_2686_, v___x_2689_);
v_x_2666_ = v___x_2690_;
v_x_2667_ = v_tail_2670_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2694_, lean_object* v_source_2695_, lean_object* v_target_2696_){
_start:
{
lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = lean_array_get_size(v_source_2695_);
v___x_2698_ = lean_nat_dec_lt(v_i_2694_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_dec_ref(v_source_2695_);
lean_dec(v_i_2694_);
return v_target_2696_;
}
else
{
lean_object* v_es_2699_; lean_object* v___x_2700_; lean_object* v_source_2701_; lean_object* v_target_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_es_2699_ = lean_array_fget(v_source_2695_, v_i_2694_);
v___x_2700_ = lean_box(0);
v_source_2701_ = lean_array_fset(v_source_2695_, v_i_2694_, v___x_2700_);
v_target_2702_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2696_, v_es_2699_);
v___x_2703_ = lean_unsigned_to_nat(1u);
v___x_2704_ = lean_nat_add(v_i_2694_, v___x_2703_);
lean_dec(v_i_2694_);
v_i_2694_ = v___x_2704_;
v_source_2695_ = v_source_2701_;
v_target_2696_ = v_target_2702_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2706_){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v_nbuckets_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2707_ = lean_array_get_size(v_data_2706_);
v___x_2708_ = lean_unsigned_to_nat(2u);
v_nbuckets_2709_ = lean_nat_mul(v___x_2707_, v___x_2708_);
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_mk_array(v_nbuckets_2709_, v___x_2711_);
v___x_2713_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2710_, v_data_2706_, v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2714_, lean_object* v_a_2715_, lean_object* v_b_2716_){
_start:
{
lean_object* v_size_2717_; lean_object* v_buckets_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2761_; 
v_size_2717_ = lean_ctor_get(v_m_2714_, 0);
v_buckets_2718_ = lean_ctor_get(v_m_2714_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_m_2714_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2720_ = v_m_2714_;
v_isShared_2721_ = v_isSharedCheck_2761_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_buckets_2718_);
lean_inc(v_size_2717_);
lean_dec(v_m_2714_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2761_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; uint64_t v___x_2723_; uint64_t v___x_2724_; uint64_t v___x_2725_; uint64_t v_fold_2726_; uint64_t v___x_2727_; uint64_t v___x_2728_; uint64_t v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; size_t v___x_2734_; lean_object* v_bkt_2735_; uint8_t v___x_2736_; 
v___x_2722_ = lean_array_get_size(v_buckets_2718_);
v___x_2723_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2715_);
v___x_2724_ = 32ULL;
v___x_2725_ = lean_uint64_shift_right(v___x_2723_, v___x_2724_);
v_fold_2726_ = lean_uint64_xor(v___x_2723_, v___x_2725_);
v___x_2727_ = 16ULL;
v___x_2728_ = lean_uint64_shift_right(v_fold_2726_, v___x_2727_);
v___x_2729_ = lean_uint64_xor(v_fold_2726_, v___x_2728_);
v___x_2730_ = lean_uint64_to_usize(v___x_2729_);
v___x_2731_ = lean_usize_of_nat(v___x_2722_);
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_sub(v___x_2731_, v___x_2732_);
v___x_2734_ = lean_usize_land(v___x_2730_, v___x_2733_);
v_bkt_2735_ = lean_array_uget_borrowed(v_buckets_2718_, v___x_2734_);
v___x_2736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2715_, v_bkt_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v_size_x27_2738_; lean_object* v___x_2739_; lean_object* v_buckets_x27_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v___x_2737_ = lean_unsigned_to_nat(1u);
v_size_x27_2738_ = lean_nat_add(v_size_2717_, v___x_2737_);
lean_dec(v_size_2717_);
lean_inc(v_bkt_2735_);
v___x_2739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2739_, 0, v_a_2715_);
lean_ctor_set(v___x_2739_, 1, v_b_2716_);
lean_ctor_set(v___x_2739_, 2, v_bkt_2735_);
v_buckets_x27_2740_ = lean_array_uset(v_buckets_2718_, v___x_2734_, v___x_2739_);
v___x_2741_ = lean_unsigned_to_nat(4u);
v___x_2742_ = lean_nat_mul(v_size_x27_2738_, v___x_2741_);
v___x_2743_ = lean_unsigned_to_nat(3u);
v___x_2744_ = lean_nat_div(v___x_2742_, v___x_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_array_get_size(v_buckets_x27_2740_);
v___x_2746_ = lean_nat_dec_le(v___x_2744_, v___x_2745_);
lean_dec(v___x_2744_);
if (v___x_2746_ == 0)
{
lean_object* v_val_2747_; lean_object* v___x_2749_; 
v_val_2747_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2740_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 1, v_val_2747_);
lean_ctor_set(v___x_2720_, 0, v_size_x27_2738_);
v___x_2749_ = v___x_2720_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_size_x27_2738_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_val_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
else
{
lean_object* v___x_2752_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 1, v_buckets_x27_2740_);
lean_ctor_set(v___x_2720_, 0, v_size_x27_2738_);
v___x_2752_ = v___x_2720_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_size_x27_2738_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_buckets_x27_2740_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v___x_2754_; lean_object* v_buckets_x27_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_inc(v_bkt_2735_);
v___x_2754_ = lean_box(0);
v_buckets_x27_2755_ = lean_array_uset(v_buckets_2718_, v___x_2734_, v___x_2754_);
v___x_2756_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2715_, v_b_2716_, v_bkt_2735_);
v___x_2757_ = lean_array_uset(v_buckets_x27_2755_, v___x_2734_, v___x_2756_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 1, v___x_2757_);
v___x_2759_ = v___x_2720_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_size_2717_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2762_, lean_object* v_x_2763_){
_start:
{
if (lean_obj_tag(v_x_2763_) == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_box(0);
return v___x_2764_;
}
else
{
lean_object* v_key_2765_; lean_object* v_value_2766_; lean_object* v_tail_2767_; uint8_t v___x_2768_; 
v_key_2765_ = lean_ctor_get(v_x_2763_, 0);
v_value_2766_ = lean_ctor_get(v_x_2763_, 1);
v_tail_2767_ = lean_ctor_get(v_x_2763_, 2);
v___x_2768_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2765_, v_a_2762_);
if (v___x_2768_ == 0)
{
v_x_2763_ = v_tail_2767_;
goto _start;
}
else
{
lean_object* v___x_2770_; 
lean_inc(v_value_2766_);
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_value_2766_);
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2771_, v_x_2772_);
lean_dec(v_x_2772_);
lean_dec(v_a_2771_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v_buckets_2776_; lean_object* v___x_2777_; uint64_t v___x_2778_; uint64_t v___x_2779_; uint64_t v___x_2780_; uint64_t v_fold_2781_; uint64_t v___x_2782_; uint64_t v___x_2783_; uint64_t v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; size_t v___x_2787_; size_t v___x_2788_; size_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_buckets_2776_ = lean_ctor_get(v_m_2774_, 1);
v___x_2777_ = lean_array_get_size(v_buckets_2776_);
v___x_2778_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2775_);
v___x_2779_ = 32ULL;
v___x_2780_ = lean_uint64_shift_right(v___x_2778_, v___x_2779_);
v_fold_2781_ = lean_uint64_xor(v___x_2778_, v___x_2780_);
v___x_2782_ = 16ULL;
v___x_2783_ = lean_uint64_shift_right(v_fold_2781_, v___x_2782_);
v___x_2784_ = lean_uint64_xor(v_fold_2781_, v___x_2783_);
v___x_2785_ = lean_uint64_to_usize(v___x_2784_);
v___x_2786_ = lean_usize_of_nat(v___x_2777_);
v___x_2787_ = ((size_t)1ULL);
v___x_2788_ = lean_usize_sub(v___x_2786_, v___x_2787_);
v___x_2789_ = lean_usize_land(v___x_2785_, v___x_2788_);
v___x_2790_ = lean_array_uget_borrowed(v_buckets_2776_, v___x_2789_);
v___x_2791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2775_, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_m_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2795_, lean_object* v_entry_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_snd_2803_; lean_object* v_snd_2804_; lean_object* v_fst_2805_; lean_object* v_fst_2806_; lean_object* v_snd_2807_; lean_object* v_fst_2808_; lean_object* v_fst_2809_; lean_object* v_snd_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_snd_2803_ = lean_ctor_get(v_p_2795_, 1);
v_snd_2804_ = lean_ctor_get(v_entry_2796_, 1);
lean_inc(v_snd_2804_);
v_fst_2805_ = lean_ctor_get(v_p_2795_, 0);
v_fst_2806_ = lean_ctor_get(v_snd_2803_, 0);
v_snd_2807_ = lean_ctor_get(v_snd_2803_, 1);
v_fst_2808_ = lean_ctor_get(v_entry_2796_, 0);
lean_inc(v_fst_2808_);
lean_dec_ref(v_entry_2796_);
v_fst_2809_ = lean_ctor_get(v_snd_2804_, 0);
lean_inc(v_fst_2809_);
v_snd_2810_ = lean_ctor_get(v_snd_2804_, 1);
v___x_2811_ = lean_array_get_size(v_fst_2808_);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = lean_nat_dec_eq(v___x_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2920_; 
v_fst_2814_ = lean_ctor_get(v_fst_2809_, 0);
v_snd_2815_ = lean_ctor_get(v_fst_2809_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_fst_2809_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2817_ = v_fst_2809_;
v_isShared_2818_ = v_isSharedCheck_2920_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_snd_2815_);
lean_inc(v_fst_2814_);
lean_dec(v_fst_2809_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2920_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v_e_2822_; lean_object* v_todo_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; 
v___x_2819_ = l_Lean_instInhabitedExpr;
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_nat_sub(v___x_2811_, v___x_2820_);
v_e_2822_ = lean_array_get(v___x_2819_, v_fst_2808_, v___x_2821_);
lean_dec(v___x_2821_);
v_todo_2823_ = lean_array_pop(v_fst_2808_);
v___x_2824_ = lean_box(v___x_2813_);
v___f_2825_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2825_, 0, v___x_2824_);
lean_closure_set(v___f_2825_, 1, v_todo_2823_);
lean_closure_set(v___f_2825_, 2, v_e_2822_);
v___x_2826_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2814_, v_snd_2815_, v___f_2825_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2911_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v_fst_2828_ = lean_ctor_get(v_a_2827_, 0);
v_snd_2829_ = lean_ctor_get(v_a_2827_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_a_2827_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2831_ = v_a_2827_;
v_isShared_2832_ = v_isSharedCheck_2911_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_snd_2829_);
lean_inc(v_fst_2828_);
lean_dec(v_a_2827_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2911_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = lean_box(3);
v___x_2834_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2828_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2807_, v_fst_2828_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v___x_2837_; 
lean_inc(v_snd_2807_);
lean_inc(v_fst_2806_);
lean_inc(v_fst_2805_);
lean_dec_ref(v_p_2795_);
lean_inc(v_snd_2804_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v_snd_2804_);
lean_ctor_set(v___x_2831_, 0, v_snd_2829_);
v___x_2837_ = v___x_2831_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_snd_2829_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_snd_2804_);
v___x_2837_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2857_; 
v_isSharedCheck_2857_ = !lean_is_exclusive(v_snd_2804_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; lean_object* v_unused_2859_; 
v_unused_2858_ = lean_ctor_get(v_snd_2804_, 1);
lean_dec(v_unused_2858_);
v_unused_2859_ = lean_ctor_get(v_snd_2804_, 0);
lean_dec(v_unused_2859_);
v___x_2839_ = v_snd_2804_;
v_isShared_2840_ = v_isSharedCheck_2857_;
goto v_resetjp_2838_;
}
else
{
lean_dec(v_snd_2804_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2857_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2856_; 
v___x_2841_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2837_, v_a_2797_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2856_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2856_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2846_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2807_, v_fst_2828_, v_a_2842_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___x_2846_);
lean_ctor_set(v___x_2817_, 0, v_fst_2806_);
v___x_2848_ = v___x_2817_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_fst_2806_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2850_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v___x_2848_);
lean_ctor_set(v___x_2839_, 0, v_fst_2805_);
v___x_2850_ = v___x_2839_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_fst_2805_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2852_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2850_);
v___x_2852_ = v___x_2844_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2861_; lean_object* v___x_2863_; 
lean_dec(v_fst_2828_);
lean_del_object(v___x_2817_);
v_val_2861_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_val_2861_);
lean_dec_ref_known(v___x_2835_, 1);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v_snd_2804_);
lean_ctor_set(v___x_2831_, 0, v_snd_2829_);
v___x_2863_ = v___x_2831_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_snd_2829_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_snd_2804_);
v___x_2863_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v___x_2864_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2861_, v___x_2863_, v_a_2797_);
lean_dec(v_val_2861_);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v___x_2864_, 0);
lean_dec(v_unused_2872_);
v___x_2866_ = v___x_2864_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_dec(v___x_2864_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v_p_2795_);
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_p_2795_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
else
{
uint8_t v___x_2874_; 
lean_dec(v_fst_2828_);
v___x_2874_ = lean_nat_dec_eq(v_fst_2806_, v___x_2812_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2876_; 
lean_del_object(v___x_2817_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v_snd_2804_);
lean_ctor_set(v___x_2831_, 0, v_snd_2829_);
v___x_2876_ = v___x_2831_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_snd_2829_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_snd_2804_);
v___x_2876_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
v___x_2877_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2806_, v___x_2876_, v_a_2797_);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2877_, 0);
lean_dec(v_unused_2885_);
v___x_2879_ = v___x_2877_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_dec(v___x_2877_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v_p_2795_);
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_p_2795_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
else
{
lean_object* v___x_2888_; 
lean_inc(v_snd_2807_);
lean_inc(v_fst_2805_);
lean_dec_ref(v_p_2795_);
lean_inc(v_snd_2804_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v_snd_2804_);
lean_ctor_set(v___x_2831_, 0, v_snd_2829_);
v___x_2888_ = v___x_2831_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_snd_2829_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_snd_2804_);
v___x_2888_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2907_; 
v_isSharedCheck_2907_ = !lean_is_exclusive(v_snd_2804_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; lean_object* v_unused_2909_; 
v_unused_2908_ = lean_ctor_get(v_snd_2804_, 1);
lean_dec(v_unused_2908_);
v_unused_2909_ = lean_ctor_get(v_snd_2804_, 0);
lean_dec(v_unused_2909_);
v___x_2890_ = v_snd_2804_;
v_isShared_2891_ = v_isSharedCheck_2907_;
goto v_resetjp_2889_;
}
else
{
lean_dec(v_snd_2804_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2907_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2906_; 
v___x_2892_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2888_, v_a_2797_);
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2906_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2906_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v_snd_2807_);
lean_ctor_set(v___x_2817_, 0, v_a_2893_);
v___x_2898_ = v___x_2817_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2893_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_snd_2807_);
v___x_2898_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 1, v___x_2898_);
lean_ctor_set(v___x_2890_, 0, v_fst_2805_);
v___x_2900_ = v___x_2890_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_fst_2805_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2902_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2900_);
v___x_2902_ = v___x_2895_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
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
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_del_object(v___x_2817_);
lean_dec(v_snd_2804_);
lean_dec_ref(v_p_2795_);
v_a_2912_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2826_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2826_);
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
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2929_; 
lean_inc(v_snd_2810_);
lean_inc(v_fst_2805_);
lean_inc(v_snd_2803_);
lean_dec(v_fst_2809_);
lean_dec(v_fst_2808_);
lean_dec_ref(v_p_2795_);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_snd_2804_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; lean_object* v_unused_2931_; 
v_unused_2930_ = lean_ctor_get(v_snd_2804_, 1);
lean_dec(v_unused_2930_);
v_unused_2931_ = lean_ctor_get(v_snd_2804_, 0);
lean_dec(v_unused_2931_);
v___x_2922_ = v_snd_2804_;
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v_snd_2804_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v_values_2924_; lean_object* v___x_2926_; 
v_values_2924_ = lean_array_push(v_fst_2805_, v_snd_2810_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v_snd_2803_);
lean_ctor_set(v___x_2922_, 0, v_values_2924_);
v___x_2926_ = v___x_2922_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_values_2924_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_snd_2803_);
v___x_2926_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2932_, lean_object* v_entry_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2932_, v_entry_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2941_, lean_object* v_p_2942_, lean_object* v_entry_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2942_, v_entry_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2951_, lean_object* v_p_2952_, lean_object* v_entry_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2951_, v_p_2952_, v_entry_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2961_, lean_object* v_m_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2962_, v_a_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2965_, lean_object* v_m_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2965_, v_m_2966_, v_a_2967_);
lean_dec(v_a_2967_);
lean_dec_ref(v_m_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2969_, lean_object* v_m_2970_, lean_object* v_a_2971_, lean_object* v_b_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2970_, v_a_2971_, v_b_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2974_, lean_object* v_a_2975_, lean_object* v_x_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2975_, v_x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2978_, lean_object* v_a_2979_, lean_object* v_x_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2978_, v_a_2979_, v_x_2980_);
lean_dec(v_x_2980_);
lean_dec(v_a_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2982_, lean_object* v_a_2983_, lean_object* v_x_2984_){
_start:
{
uint8_t v___x_2985_; 
v___x_2985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2983_, v_x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2986_, lean_object* v_a_2987_, lean_object* v_x_2988_){
_start:
{
uint8_t v_res_2989_; lean_object* v_r_2990_; 
v_res_2989_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2986_, v_a_2987_, v_x_2988_);
lean_dec(v_x_2988_);
lean_dec(v_a_2987_);
v_r_2990_ = lean_box(v_res_2989_);
return v_r_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2991_, lean_object* v_data_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_2994_, lean_object* v_a_2995_, lean_object* v_b_2996_, lean_object* v_x_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2995_, v_b_2996_, v_x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2999_, lean_object* v_i_3000_, lean_object* v_source_3001_, lean_object* v_target_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3000_, v_source_3001_, v_target_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3004_, lean_object* v_x_3005_, lean_object* v_x_3006_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3005_, v_x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3008_, size_t v_i_3009_, size_t v_stop_3010_, lean_object* v_b_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = lean_usize_dec_eq(v_i_3009_, v_stop_3010_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_array_uget_borrowed(v_as_3008_, v_i_3009_);
lean_inc(v___x_3019_);
v___x_3020_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3011_, v___x_3019_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; size_t v___x_3022_; size_t v___x_3023_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_add(v_i_3009_, v___x_3022_);
v_i_3009_ = v___x_3023_;
v_b_3011_ = v_a_3021_;
goto _start;
}
else
{
return v___x_3020_;
}
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_b_3011_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3026_, lean_object* v_i_3027_, lean_object* v_stop_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
size_t v_i_boxed_3036_; size_t v_stop_boxed_3037_; lean_object* v_res_3038_; 
v_i_boxed_3036_ = lean_unbox_usize(v_i_3027_);
lean_dec(v_i_3027_);
v_stop_boxed_3037_ = lean_unbox_usize(v_stop_3028_);
lean_dec(v_stop_3028_);
v_res_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3026_, v_i_boxed_3036_, v_stop_boxed_3037_, v_b_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v_as_3026_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3039_, lean_object* v_starIdx_3040_, lean_object* v_children_3041_, lean_object* v_entries_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3049_, 0, v_starIdx_3040_);
lean_ctor_set(v___x_3049_, 1, v_children_3041_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v_values_3039_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = lean_unsigned_to_nat(0u);
v___x_3052_ = lean_array_get_size(v_entries_3042_);
v___x_3053_ = lean_nat_dec_lt(v___x_3051_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3050_);
return v___x_3054_;
}
else
{
uint8_t v___x_3055_; 
v___x_3055_ = lean_nat_dec_le(v___x_3052_, v___x_3052_);
if (v___x_3055_ == 0)
{
if (v___x_3053_ == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3050_);
return v___x_3056_;
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___x_3052_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3042_, v___x_3057_, v___x_3058_, v___x_3050_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
return v___x_3059_;
}
}
else
{
size_t v___x_3060_; size_t v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = ((size_t)0ULL);
v___x_3061_ = lean_usize_of_nat(v___x_3052_);
v___x_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3042_, v___x_3060_, v___x_3061_, v___x_3050_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
return v___x_3062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3063_, lean_object* v_starIdx_3064_, lean_object* v_children_3065_, lean_object* v_entries_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3063_, v_starIdx_3064_, v_children_3065_, v_entries_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_entries_3066_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3074_, lean_object* v_values_3075_, lean_object* v_starIdx_3076_, lean_object* v_children_3077_, lean_object* v_entries_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3075_, v_starIdx_3076_, v_children_3077_, v_entries_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3086_, lean_object* v_values_3087_, lean_object* v_starIdx_3088_, lean_object* v_children_3089_, lean_object* v_entries_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3086_, v_values_3087_, v_starIdx_3088_, v_children_3089_, v_entries_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_entries_3090_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3098_, lean_object* v_as_3099_, size_t v_i_3100_, size_t v_stop_3101_, lean_object* v_b_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3099_, v_i_3100_, v_stop_3101_, v_b_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3110_, lean_object* v_as_3111_, lean_object* v_i_3112_, lean_object* v_stop_3113_, lean_object* v_b_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
size_t v_i_boxed_3121_; size_t v_stop_boxed_3122_; lean_object* v_res_3123_; 
v_i_boxed_3121_ = lean_unbox_usize(v_i_3112_);
lean_dec(v_i_3112_);
v_stop_boxed_3122_ = lean_unbox_usize(v_stop_3113_);
lean_dec(v_stop_3113_);
v_res_3123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3110_, v_as_3111_, v_i_boxed_3121_, v_stop_boxed_3122_, v_b_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v_as_3111_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v_values_3134_; lean_object* v_star_3135_; lean_object* v_children_3136_; lean_object* v_pending_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3167_; 
v___x_3131_ = lean_st_ref_get(v_a_3125_);
v___x_3132_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3133_ = lean_array_get(v___x_3132_, v___x_3131_, v_c_3124_);
lean_dec(v___x_3131_);
v_values_3134_ = lean_ctor_get(v___x_3133_, 0);
v_star_3135_ = lean_ctor_get(v___x_3133_, 1);
v_children_3136_ = lean_ctor_get(v___x_3133_, 2);
v_pending_3137_ = lean_ctor_get(v___x_3133_, 3);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3139_ = v___x_3133_;
v_isShared_3140_ = v_isSharedCheck_3167_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_pending_3137_);
lean_inc(v_children_3136_);
lean_inc(v_star_3135_);
lean_inc(v_values_3134_);
lean_dec(v___x_3133_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3167_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3141_ = lean_array_get_size(v_pending_3137_);
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_nat_dec_eq(v___x_3141_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3124_, v___x_3132_, v_a_3125_);
lean_dec_ref(v___x_3144_);
v___x_3145_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3134_, v_star_3135_, v_children_3136_, v_pending_3137_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
lean_dec_ref(v_pending_3137_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v_snd_3147_; lean_object* v_fst_3148_; lean_object* v_fst_3149_; lean_object* v_snd_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___x_3145_, 1);
v_snd_3147_ = lean_ctor_get(v_a_3146_, 1);
v_fst_3148_ = lean_ctor_get(v_a_3146_, 0);
v_fst_3149_ = lean_ctor_get(v_snd_3147_, 0);
v_snd_3150_ = lean_ctor_get(v_snd_3147_, 1);
v___x_3151_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
lean_inc(v_snd_3150_);
lean_inc(v_fst_3149_);
lean_inc(v_fst_3148_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 3, v___x_3151_);
lean_ctor_set(v___x_3139_, 2, v_snd_3150_);
lean_ctor_set(v___x_3139_, 1, v_fst_3149_);
lean_ctor_set(v___x_3139_, 0, v_fst_3148_);
v___x_3153_ = v___x_3139_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_fst_3148_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_fst_3149_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v_snd_3150_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v___x_3154_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3124_, v___x_3153_, v_a_3125_);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v___x_3154_, 0);
lean_dec(v_unused_3162_);
v___x_3156_ = v___x_3154_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_dec(v___x_3154_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v_a_3146_);
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3146_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_del_object(v___x_3139_);
return v___x_3145_;
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_del_object(v___x_3139_);
lean_dec_ref(v_pending_3137_);
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_star_3135_);
lean_ctor_set(v___x_3164_, 1, v_children_3136_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v_values_3134_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec(v_c_3168_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3176_, lean_object* v_c_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3185_, lean_object* v_c_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3185_, v_c_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec(v_c_3186_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3194_, lean_object* v_fallback_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_inc(v_fallback_3195_);
return v_fallback_3195_;
}
else
{
lean_object* v_key_3197_; lean_object* v_value_3198_; lean_object* v_tail_3199_; uint8_t v___x_3200_; 
v_key_3197_ = lean_ctor_get(v_x_3196_, 0);
v_value_3198_ = lean_ctor_get(v_x_3196_, 1);
v_tail_3199_ = lean_ctor_get(v_x_3196_, 2);
v___x_3200_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3197_, v_a_3194_);
if (v___x_3200_ == 0)
{
v_x_3196_ = v_tail_3199_;
goto _start;
}
else
{
lean_inc(v_value_3198_);
return v_value_3198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3202_, lean_object* v_fallback_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3202_, v_fallback_3203_, v_x_3204_);
lean_dec(v_x_3204_);
lean_dec(v_fallback_3203_);
lean_dec(v_a_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3206_, lean_object* v_a_3207_, lean_object* v_fallback_3208_){
_start:
{
lean_object* v_buckets_3209_; lean_object* v___x_3210_; uint64_t v___x_3211_; uint64_t v___x_3212_; uint64_t v___x_3213_; uint64_t v_fold_3214_; uint64_t v___x_3215_; uint64_t v___x_3216_; uint64_t v___x_3217_; size_t v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; size_t v___x_3221_; size_t v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_buckets_3209_ = lean_ctor_get(v_m_3206_, 1);
v___x_3210_ = lean_array_get_size(v_buckets_3209_);
v___x_3211_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3207_);
v___x_3212_ = 32ULL;
v___x_3213_ = lean_uint64_shift_right(v___x_3211_, v___x_3212_);
v_fold_3214_ = lean_uint64_xor(v___x_3211_, v___x_3213_);
v___x_3215_ = 16ULL;
v___x_3216_ = lean_uint64_shift_right(v_fold_3214_, v___x_3215_);
v___x_3217_ = lean_uint64_xor(v_fold_3214_, v___x_3216_);
v___x_3218_ = lean_uint64_to_usize(v___x_3217_);
v___x_3219_ = lean_usize_of_nat(v___x_3210_);
v___x_3220_ = ((size_t)1ULL);
v___x_3221_ = lean_usize_sub(v___x_3219_, v___x_3220_);
v___x_3222_ = lean_usize_land(v___x_3218_, v___x_3221_);
v___x_3223_ = lean_array_uget_borrowed(v_buckets_3209_, v___x_3222_);
v___x_3224_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3207_, v_fallback_3208_, v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3225_, lean_object* v_a_3226_, lean_object* v_fallback_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3225_, v_a_3226_, v_fallback_3227_);
lean_dec(v_fallback_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_m_3225_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3229_, lean_object* v_rest_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = lean_unsigned_to_nat(0u);
v___x_3238_ = lean_nat_dec_eq(v_next_3229_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3229_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3265_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3265_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3265_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v_snd_3244_; 
v_snd_3244_ = lean_ctor_get(v_a_3240_, 1);
lean_inc(v_snd_3244_);
lean_dec(v_a_3240_);
if (lean_obj_tag(v_rest_3230_) == 0)
{
lean_object* v_fst_3245_; lean_object* v_snd_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v_fst_3245_ = lean_ctor_get(v_snd_3244_, 0);
lean_inc(v_fst_3245_);
v_snd_3246_ = lean_ctor_get(v_snd_3244_, 1);
lean_inc(v_snd_3246_);
lean_dec(v_snd_3244_);
v___x_3247_ = lean_st_ref_take(v_a_3231_);
v___x_3248_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v_fst_3245_);
lean_ctor_set(v___x_3249_, 2, v_snd_3246_);
lean_ctor_set(v___x_3249_, 3, v___x_3248_);
v___x_3250_ = lean_array_set(v___x_3247_, v_next_3229_, v___x_3249_);
lean_dec(v_next_3229_);
v___x_3251_ = lean_st_ref_set(v_a_3231_, v___x_3250_);
v___x_3252_ = lean_box(0);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3252_);
v___x_3254_ = v___x_3242_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
else
{
lean_object* v_fst_3256_; lean_object* v_snd_3257_; lean_object* v_head_3258_; lean_object* v_tail_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
lean_del_object(v___x_3242_);
lean_dec(v_next_3229_);
v_fst_3256_ = lean_ctor_get(v_snd_3244_, 0);
lean_inc(v_fst_3256_);
v_snd_3257_ = lean_ctor_get(v_snd_3244_, 1);
lean_inc(v_snd_3257_);
lean_dec(v_snd_3244_);
v_head_3258_ = lean_ctor_get(v_rest_3230_, 0);
v_tail_3259_ = lean_ctor_get(v_rest_3230_, 1);
v___x_3260_ = lean_box(3);
v___x_3261_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3258_, v___x_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; 
lean_dec(v_fst_3256_);
v___x_3262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3257_, v_head_3258_, v___x_3237_);
lean_dec(v_snd_3257_);
v_next_3229_ = v___x_3262_;
v_rest_3230_ = v_tail_3259_;
goto _start;
}
else
{
lean_dec(v_snd_3257_);
v_next_3229_ = v_fst_3256_;
v_rest_3230_ = v_tail_3259_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec(v_next_3229_);
v_a_3266_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3239_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3239_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v_next_3229_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3276_, lean_object* v_rest_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3276_, v_rest_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec(v_rest_3277_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3285_, lean_object* v_next_3286_, lean_object* v_rest_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3286_, v_rest_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3295_, lean_object* v_next_3296_, lean_object* v_rest_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3295_, v_next_3296_, v_rest_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec(v_rest_3297_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3305_, lean_object* v_m_3306_, lean_object* v_a_3307_, lean_object* v_fallback_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3306_, v_a_3307_, v_fallback_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3310_, lean_object* v_m_3311_, lean_object* v_a_3312_, lean_object* v_fallback_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3310_, v_m_3311_, v_a_3312_, v_fallback_3313_);
lean_dec(v_fallback_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_m_3311_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3315_, lean_object* v_a_3316_, lean_object* v_fallback_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3316_, v_fallback_3317_, v_x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3320_, lean_object* v_a_3321_, lean_object* v_fallback_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3320_, v_a_3321_, v_fallback_3322_, v_x_3323_);
lean_dec(v_x_3323_);
lean_dec(v_fallback_3322_);
lean_dec(v_a_3321_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3325_, lean_object* v_path_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
if (lean_obj_tag(v_path_3326_) == 0)
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v_t_3325_);
return v___x_3332_;
}
else
{
lean_object* v_head_3333_; lean_object* v_tail_3334_; lean_object* v_roots_3335_; lean_object* v___x_3336_; lean_object* v_idx_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_head_3333_ = lean_ctor_get(v_path_3326_, 0);
lean_inc(v_head_3333_);
v_tail_3334_ = lean_ctor_get(v_path_3326_, 1);
lean_inc(v_tail_3334_);
lean_dec_ref_known(v_path_3326_, 2);
v_roots_3335_ = lean_ctor_get(v_t_3325_, 1);
v___x_3336_ = lean_unsigned_to_nat(0u);
v_idx_3337_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3335_, v_head_3333_, v___x_3336_);
lean_dec(v_head_3333_);
v___x_3338_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3338_, 0, lean_box(0));
lean_closure_set(v___x_3338_, 1, v_idx_3337_);
lean_closure_set(v___x_3338_, 2, v_tail_3334_);
v___x_3339_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3325_, v___x_3338_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3348_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3342_ = v___x_3339_;
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_snd_3344_; lean_object* v___x_3346_; 
v_snd_3344_ = lean_ctor_get(v_a_3340_, 1);
lean_inc(v_snd_3344_);
lean_dec(v_a_3340_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v_snd_3344_);
v___x_3346_ = v___x_3342_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_snd_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3339_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3339_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3357_, lean_object* v_path_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3357_, v_path_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3365_, lean_object* v_t_3366_, lean_object* v_path_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3366_, v_path_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3374_, lean_object* v_t_3375_, lean_object* v_path_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3374_, v_t_3375_, v_path_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3385_, lean_object* v_e_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3388_ = lean_array_get_size(v_a_3387_);
v___x_3389_ = lean_nat_dec_lt(v___x_3388_, v_score_3385_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_mk_empty_array_with_capacity(v___x_3390_);
v___x_3392_ = lean_array_push(v___x_3391_, v_e_3386_);
v___x_3393_ = lean_array_push(v_a_3387_, v___x_3392_);
return v___x_3393_;
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3395_ = lean_array_push(v_a_3387_, v___x_3394_);
v_a_3387_ = v___x_3395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3397_, lean_object* v_e_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3397_, v_e_3398_, v_a_3399_);
lean_dec(v_score_3397_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3401_, lean_object* v_score_3402_, lean_object* v_e_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3402_, v_e_3403_, v_a_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3406_, lean_object* v_score_3407_, lean_object* v_e_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3406_, v_score_3407_, v_e_3408_, v_a_3409_);
lean_dec(v_score_3407_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3411_, lean_object* v_score_3412_, lean_object* v_e_3413_){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3414_ = lean_array_get_size(v_e_3413_);
v___x_3415_ = lean_unsigned_to_nat(0u);
v___x_3416_ = lean_nat_dec_eq(v___x_3414_, v___x_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3417_ = lean_array_get_size(v_r_3411_);
v___x_3418_ = lean_nat_dec_lt(v_score_3412_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; 
v___x_3419_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3412_, v_e_3413_, v_r_3411_);
return v___x_3419_;
}
else
{
if (v___x_3418_ == 0)
{
lean_dec_ref(v_e_3413_);
return v_r_3411_;
}
else
{
lean_object* v_v_3420_; lean_object* v___x_3421_; lean_object* v_xs_x27_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_v_3420_ = lean_array_fget(v_r_3411_, v_score_3412_);
v___x_3421_ = lean_box(0);
v_xs_x27_3422_ = lean_array_fset(v_r_3411_, v_score_3412_, v___x_3421_);
v___x_3423_ = lean_array_push(v_v_3420_, v_e_3413_);
v___x_3424_ = lean_array_fset(v_xs_x27_3422_, v_score_3412_, v___x_3423_);
return v___x_3424_;
}
}
}
else
{
lean_dec_ref(v_e_3413_);
return v_r_3411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3425_, lean_object* v_score_3426_, lean_object* v_e_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3425_, v_score_3426_, v_e_3427_);
lean_dec(v_score_3426_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3429_, lean_object* v_r_3430_, lean_object* v_score_3431_, lean_object* v_e_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3430_, v_score_3431_, v_e_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3434_, lean_object* v_r_3435_, lean_object* v_score_3436_, lean_object* v_e_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3434_, v_r_3435_, v_score_3436_, v_e_3437_);
lean_dec(v_score_3436_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3439_, size_t v_i_3440_, size_t v_stop_3441_, lean_object* v_b_3442_){
_start:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_usize_dec_eq(v_i_3440_, v_stop_3441_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; size_t v___x_3447_; size_t v___x_3448_; 
v___x_3444_ = lean_array_uget_borrowed(v_as_3439_, v_i_3440_);
v___x_3445_ = lean_array_get_size(v___x_3444_);
v___x_3446_ = lean_nat_add(v_b_3442_, v___x_3445_);
lean_dec(v_b_3442_);
v___x_3447_ = ((size_t)1ULL);
v___x_3448_ = lean_usize_add(v_i_3440_, v___x_3447_);
v_i_3440_ = v___x_3448_;
v_b_3442_ = v___x_3446_;
goto _start;
}
else
{
return v_b_3442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3450_, lean_object* v_i_3451_, lean_object* v_stop_3452_, lean_object* v_b_3453_){
_start:
{
size_t v_i_boxed_3454_; size_t v_stop_boxed_3455_; lean_object* v_res_3456_; 
v_i_boxed_3454_ = lean_unbox_usize(v_i_3451_);
lean_dec(v_i_3451_);
v_stop_boxed_3455_ = lean_unbox_usize(v_stop_3452_);
lean_dec(v_stop_3452_);
v_res_3456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3450_, v_i_boxed_3454_, v_stop_boxed_3455_, v_b_3453_);
lean_dec_ref(v_as_3450_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3457_, size_t v_i_3458_, size_t v_stop_3459_, lean_object* v_b_3460_){
_start:
{
lean_object* v___y_3462_; uint8_t v___x_3466_; 
v___x_3466_ = lean_usize_dec_eq(v_i_3458_, v_stop_3459_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v___x_3467_ = lean_array_uget_borrowed(v_as_3457_, v_i_3458_);
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_array_get_size(v___x_3467_);
v___x_3470_ = lean_nat_dec_lt(v___x_3468_, v___x_3469_);
if (v___x_3470_ == 0)
{
v___y_3462_ = v_b_3460_;
goto v___jp_3461_;
}
else
{
uint8_t v___x_3471_; 
v___x_3471_ = lean_nat_dec_le(v___x_3469_, v___x_3469_);
if (v___x_3471_ == 0)
{
if (v___x_3470_ == 0)
{
v___y_3462_ = v_b_3460_;
goto v___jp_3461_;
}
else
{
size_t v___x_3472_; size_t v___x_3473_; lean_object* v___x_3474_; 
v___x_3472_ = ((size_t)0ULL);
v___x_3473_ = lean_usize_of_nat(v___x_3469_);
v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3467_, v___x_3472_, v___x_3473_, v_b_3460_);
v___y_3462_ = v___x_3474_;
goto v___jp_3461_;
}
}
else
{
size_t v___x_3475_; size_t v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = ((size_t)0ULL);
v___x_3476_ = lean_usize_of_nat(v___x_3469_);
v___x_3477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3467_, v___x_3475_, v___x_3476_, v_b_3460_);
v___y_3462_ = v___x_3477_;
goto v___jp_3461_;
}
}
}
else
{
return v_b_3460_;
}
v___jp_3461_:
{
size_t v___x_3463_; size_t v___x_3464_; 
v___x_3463_ = ((size_t)1ULL);
v___x_3464_ = lean_usize_add(v_i_3458_, v___x_3463_);
v_i_3458_ = v___x_3464_;
v_b_3460_ = v___y_3462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3478_, lean_object* v_i_3479_, lean_object* v_stop_3480_, lean_object* v_b_3481_){
_start:
{
size_t v_i_boxed_3482_; size_t v_stop_boxed_3483_; lean_object* v_res_3484_; 
v_i_boxed_3482_ = lean_unbox_usize(v_i_3479_);
lean_dec(v_i_3479_);
v_stop_boxed_3483_ = lean_unbox_usize(v_stop_3480_);
lean_dec(v_stop_3480_);
v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3478_, v_i_boxed_3482_, v_stop_boxed_3483_, v_b_3481_);
lean_dec_ref(v_as_3478_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3485_){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = lean_array_get_size(v_mr_3485_);
v___x_3488_ = lean_nat_dec_lt(v___x_3486_, v___x_3487_);
if (v___x_3488_ == 0)
{
return v___x_3486_;
}
else
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_nat_dec_le(v___x_3487_, v___x_3487_);
if (v___x_3489_ == 0)
{
if (v___x_3488_ == 0)
{
return v___x_3486_;
}
else
{
size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = lean_usize_of_nat(v___x_3487_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3485_, v___x_3490_, v___x_3491_, v___x_3486_);
return v___x_3492_;
}
}
else
{
size_t v___x_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = ((size_t)0ULL);
v___x_3494_ = lean_usize_of_nat(v___x_3487_);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3485_, v___x_3493_, v___x_3494_, v___x_3486_);
return v___x_3495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3496_);
lean_dec_ref(v_mr_3496_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3498_, lean_object* v_mr_3499_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3501_, lean_object* v_mr_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3501_, v_mr_3502_);
lean_dec_ref(v_mr_3502_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3504_, lean_object* v_as_3505_, size_t v_i_3506_, size_t v_stop_3507_, lean_object* v_b_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3505_, v_i_3506_, v_stop_3507_, v_b_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3510_, lean_object* v_as_3511_, lean_object* v_i_3512_, lean_object* v_stop_3513_, lean_object* v_b_3514_){
_start:
{
size_t v_i_boxed_3515_; size_t v_stop_boxed_3516_; lean_object* v_res_3517_; 
v_i_boxed_3515_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_stop_boxed_3516_ = lean_unbox_usize(v_stop_3513_);
lean_dec(v_stop_3513_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3510_, v_as_3511_, v_i_boxed_3515_, v_stop_boxed_3516_, v_b_3514_);
lean_dec_ref(v_as_3511_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3518_, lean_object* v_as_3519_, size_t v_i_3520_, size_t v_stop_3521_, lean_object* v_b_3522_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3519_, v_i_3520_, v_stop_3521_, v_b_3522_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3524_, lean_object* v_as_3525_, lean_object* v_i_3526_, lean_object* v_stop_3527_, lean_object* v_b_3528_){
_start:
{
size_t v_i_boxed_3529_; size_t v_stop_boxed_3530_; lean_object* v_res_3531_; 
v_i_boxed_3529_ = lean_unbox_usize(v_i_3526_);
lean_dec(v_i_3526_);
v_stop_boxed_3530_ = lean_unbox_usize(v_stop_3527_);
lean_dec(v_stop_3527_);
v_res_3531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3524_, v_as_3525_, v_i_boxed_3529_, v_stop_boxed_3530_, v_b_3528_);
lean_dec_ref(v_as_3525_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3532_, lean_object* v_j_3533_, lean_object* v_x_3534_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_apply_2(v_f_3532_, v_j_3533_, v_x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3555_, lean_object* v_x1_3556_, lean_object* v_x2_3557_){
_start:
{
lean_object* v___x_3558_; size_t v_sz_3559_; size_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3558_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3559_ = lean_array_size(v_x2_3557_);
v___x_3560_ = ((size_t)0ULL);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3558_, v___f_3555_, v_sz_3559_, v___x_3560_, v_x2_3557_);
v___x_3562_ = l_Array_append___redArg(v_x1_3556_, v___x_3561_);
lean_dec(v___x_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3563_, lean_object* v_mr_3564_, lean_object* v_f_3565_, lean_object* v_i_3566_, lean_object* v_x_3567_, lean_object* v_r_3568_){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v_j_3571_; lean_object* v_b_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3569_ = lean_unsigned_to_nat(1u);
v___x_3570_ = lean_nat_sub(v_n_3563_, v___x_3569_);
v_j_3571_ = lean_nat_sub(v___x_3570_, v_i_3566_);
lean_dec(v___x_3570_);
v_b_3572_ = lean_array_fget_borrowed(v_mr_3564_, v_j_3571_);
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = lean_array_get_size(v_b_3572_);
v___x_3575_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3576_ = lean_nat_dec_lt(v___x_3573_, v___x_3574_);
if (v___x_3576_ == 0)
{
lean_dec(v_j_3571_);
lean_dec(v_f_3565_);
return v_r_3568_;
}
else
{
lean_object* v___f_3577_; lean_object* v___f_3578_; uint8_t v___x_3579_; 
v___f_3577_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3577_, 0, v_f_3565_);
lean_closure_set(v___f_3577_, 1, v_j_3571_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3578_, 0, v___f_3577_);
v___x_3579_ = lean_nat_dec_le(v___x_3574_, v___x_3574_);
if (v___x_3579_ == 0)
{
if (v___x_3576_ == 0)
{
lean_dec_ref(v___f_3578_);
return v_r_3568_;
}
else
{
size_t v___x_3580_; size_t v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = ((size_t)0ULL);
v___x_3581_ = lean_usize_of_nat(v___x_3574_);
lean_inc(v_b_3572_);
v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3575_, v___f_3578_, v_b_3572_, v___x_3580_, v___x_3581_, v_r_3568_);
return v___x_3582_;
}
}
else
{
size_t v___x_3583_; size_t v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = ((size_t)0ULL);
v___x_3584_ = lean_usize_of_nat(v___x_3574_);
lean_inc(v_b_3572_);
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3575_, v___f_3578_, v_b_3572_, v___x_3583_, v___x_3584_, v_r_3568_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3586_, lean_object* v_mr_3587_, lean_object* v_f_3588_, lean_object* v_i_3589_, lean_object* v_x_3590_, lean_object* v_r_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3586_, v_mr_3587_, v_f_3588_, v_i_3589_, v_x_3590_, v_r_3591_);
lean_dec(v_i_3589_);
lean_dec_ref(v_mr_3587_);
lean_dec(v_n_3586_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3593_, lean_object* v_a_3594_, lean_object* v_f_3595_){
_start:
{
lean_object* v_n_3596_; lean_object* v___f_3597_; lean_object* v___x_3598_; 
v_n_3596_ = lean_array_get_size(v_mr_3593_);
v___f_3597_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3597_, 0, v_n_3596_);
lean_closure_set(v___f_3597_, 1, v_mr_3593_);
lean_closure_set(v___f_3597_, 2, v_f_3595_);
v___x_3598_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3596_, v___f_3597_, v_n_3596_, lean_box(0), v_a_3594_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3599_, lean_object* v_00_u03b2_3600_, lean_object* v_mr_3601_, lean_object* v_a_3602_, lean_object* v_f_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3601_, v_a_3602_, v_f_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3605_, size_t v_i_3606_, lean_object* v_bs_3607_){
_start:
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_usize_dec_lt(v_i_3606_, v_sz_3605_);
if (v___x_3608_ == 0)
{
return v_bs_3607_;
}
else
{
lean_object* v_v_3609_; lean_object* v___x_3610_; lean_object* v_bs_x27_3611_; size_t v___x_3612_; size_t v___x_3613_; lean_object* v___x_3614_; 
v_v_3609_ = lean_array_uget(v_bs_3607_, v_i_3606_);
v___x_3610_ = lean_unsigned_to_nat(0u);
v_bs_x27_3611_ = lean_array_uset(v_bs_3607_, v_i_3606_, v___x_3610_);
v___x_3612_ = ((size_t)1ULL);
v___x_3613_ = lean_usize_add(v_i_3606_, v___x_3612_);
v___x_3614_ = lean_array_uset(v_bs_x27_3611_, v_i_3606_, v_v_3609_);
v_i_3606_ = v___x_3613_;
v_bs_3607_ = v___x_3614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3616_, lean_object* v_i_3617_, lean_object* v_bs_3618_){
_start:
{
size_t v_sz_boxed_3619_; size_t v_i_boxed_3620_; lean_object* v_res_3621_; 
v_sz_boxed_3619_ = lean_unbox_usize(v_sz_3616_);
lean_dec(v_sz_3616_);
v_i_boxed_3620_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_res_3621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3619_, v_i_boxed_3620_, v_bs_3618_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3622_, size_t v_i_3623_, size_t v_stop_3624_, lean_object* v_b_3625_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_eq(v_i_3623_, v_stop_3624_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; size_t v_sz_3628_; size_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; size_t v___x_3632_; size_t v___x_3633_; 
v___x_3627_ = lean_array_uget_borrowed(v_as_3622_, v_i_3623_);
v_sz_3628_ = lean_array_size(v___x_3627_);
v___x_3629_ = ((size_t)0ULL);
lean_inc(v___x_3627_);
v___x_3630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3628_, v___x_3629_, v___x_3627_);
v___x_3631_ = l_Array_append___redArg(v_b_3625_, v___x_3630_);
lean_dec_ref(v___x_3630_);
v___x_3632_ = ((size_t)1ULL);
v___x_3633_ = lean_usize_add(v_i_3623_, v___x_3632_);
v_i_3623_ = v___x_3633_;
v_b_3625_ = v___x_3631_;
goto _start;
}
else
{
return v_b_3625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_stop_3637_, lean_object* v_b_3638_){
_start:
{
size_t v_i_boxed_3639_; size_t v_stop_boxed_3640_; lean_object* v_res_3641_; 
v_i_boxed_3639_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_stop_boxed_3640_ = lean_unbox_usize(v_stop_3637_);
lean_dec(v_stop_3637_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3635_, v_i_boxed_3639_, v_stop_boxed_3640_, v_b_3638_);
lean_dec_ref(v_as_3635_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3642_, lean_object* v_aa_3643_, lean_object* v_n_3644_, lean_object* v_j_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_zero_3647_; uint8_t v_isZero_3648_; 
v_zero_3647_ = lean_unsigned_to_nat(0u);
v_isZero_3648_ = lean_nat_dec_eq(v_j_3645_, v_zero_3647_);
if (v_isZero_3648_ == 1)
{
lean_dec(v_j_3645_);
return v_a_3646_;
}
else
{
lean_object* v_one_3649_; lean_object* v_n_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_j_3653_; lean_object* v_b_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v_one_3649_ = lean_unsigned_to_nat(1u);
v_n_3650_ = lean_nat_sub(v_j_3645_, v_one_3649_);
v___x_3651_ = lean_nat_sub(v_n_3644_, v_j_3645_);
lean_dec(v_j_3645_);
v___x_3652_ = lean_nat_sub(v_n_3642_, v_one_3649_);
v_j_3653_ = lean_nat_sub(v___x_3652_, v___x_3651_);
lean_dec(v___x_3651_);
lean_dec(v___x_3652_);
v_b_3654_ = lean_array_fget_borrowed(v_aa_3643_, v_j_3653_);
lean_dec(v_j_3653_);
v___x_3655_ = lean_array_get_size(v_b_3654_);
v___x_3656_ = lean_nat_dec_lt(v_zero_3647_, v___x_3655_);
if (v___x_3656_ == 0)
{
v_j_3645_ = v_n_3650_;
goto _start;
}
else
{
uint8_t v___x_3658_; 
v___x_3658_ = lean_nat_dec_le(v___x_3655_, v___x_3655_);
if (v___x_3658_ == 0)
{
if (v___x_3656_ == 0)
{
v_j_3645_ = v_n_3650_;
goto _start;
}
else
{
size_t v___x_3660_; size_t v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = ((size_t)0ULL);
v___x_3661_ = lean_usize_of_nat(v___x_3655_);
v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3654_, v___x_3660_, v___x_3661_, v_a_3646_);
v_j_3645_ = v_n_3650_;
v_a_3646_ = v___x_3662_;
goto _start;
}
}
else
{
size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = ((size_t)0ULL);
v___x_3665_ = lean_usize_of_nat(v___x_3655_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3654_, v___x_3664_, v___x_3665_, v_a_3646_);
v_j_3645_ = v_n_3650_;
v_a_3646_ = v___x_3666_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3668_, lean_object* v_aa_3669_, lean_object* v_n_3670_, lean_object* v_j_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3668_, v_aa_3669_, v_n_3670_, v_j_3671_, v_a_3672_);
lean_dec(v_n_3670_);
lean_dec_ref(v_aa_3669_);
lean_dec(v_n_3668_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v_n_3676_; lean_object* v___x_3677_; 
v_n_3676_ = lean_array_get_size(v_mr_3674_);
v___x_3677_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3676_, v_mr_3674_, v_n_3676_, v_n_3676_, v_a_3675_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3678_, v_a_3679_);
lean_dec_ref(v_mr_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3681_, v_a_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3684_, v_a_3685_);
lean_dec_ref(v_mr_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3687_, lean_object* v_mr_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3688_, v_a_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3691_, lean_object* v_mr_3692_, lean_object* v_a_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3691_, v_mr_3692_, v_a_3693_);
lean_dec_ref(v_mr_3692_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3695_, lean_object* v_mr_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3696_, v_a_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3699_, lean_object* v_mr_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3699_, v_mr_3700_, v_a_3701_);
lean_dec_ref(v_mr_3700_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3703_, size_t v_sz_3704_, size_t v_i_3705_, lean_object* v_bs_3706_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3704_, v_i_3705_, v_bs_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3708_, lean_object* v_sz_3709_, lean_object* v_i_3710_, lean_object* v_bs_3711_){
_start:
{
size_t v_sz_boxed_3712_; size_t v_i_boxed_3713_; lean_object* v_res_3714_; 
v_sz_boxed_3712_ = lean_unbox_usize(v_sz_3709_);
lean_dec(v_sz_3709_);
v_i_boxed_3713_ = lean_unbox_usize(v_i_3710_);
lean_dec(v_i_3710_);
v_res_3714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3708_, v_sz_boxed_3712_, v_i_boxed_3713_, v_bs_3711_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3715_, lean_object* v_as_3716_, size_t v_i_3717_, size_t v_stop_3718_, lean_object* v_b_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3716_, v_i_3717_, v_stop_3718_, v_b_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3721_, lean_object* v_as_3722_, lean_object* v_i_3723_, lean_object* v_stop_3724_, lean_object* v_b_3725_){
_start:
{
size_t v_i_boxed_3726_; size_t v_stop_boxed_3727_; lean_object* v_res_3728_; 
v_i_boxed_3726_ = lean_unbox_usize(v_i_3723_);
lean_dec(v_i_3723_);
v_stop_boxed_3727_ = lean_unbox_usize(v_stop_3724_);
lean_dec(v_stop_3724_);
v_res_3728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3721_, v_as_3722_, v_i_boxed_3726_, v_stop_boxed_3727_, v_b_3725_);
lean_dec_ref(v_as_3722_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3729_, lean_object* v_n_3730_, lean_object* v_aa_3731_, lean_object* v_n_3732_, lean_object* v_j_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3730_, v_aa_3731_, v_n_3732_, v_j_3733_, v_a_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3737_, lean_object* v_n_3738_, lean_object* v_aa_3739_, lean_object* v_n_3740_, lean_object* v_j_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3737_, v_n_3738_, v_aa_3739_, v_n_3740_, v_j_3741_, v_a_3742_, v_a_3743_);
lean_dec(v_n_3740_);
lean_dec_ref(v_aa_3739_);
lean_dec(v_n_3738_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3752_, lean_object* v___x_3753_, lean_object* v_score_3754_, lean_object* v___x_3755_, lean_object* v_k_3756_, lean_object* v_args_3757_, lean_object* v_cases_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3752_, v_k_3756_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_dec_ref(v___x_3753_);
return v_cases_3758_;
}
else
{
lean_object* v_val_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_val_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_val_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = l_Array_append___redArg(v___x_3753_, v_args_3757_);
v___x_3762_ = lean_nat_add(v_score_3754_, v___x_3755_);
v___x_3763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
lean_ctor_set(v___x_3763_, 2, v_val_3760_);
v___x_3764_ = lean_array_push(v_cases_3758_, v___x_3763_);
return v___x_3764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3765_, lean_object* v___x_3766_, lean_object* v_score_3767_, lean_object* v___x_3768_, lean_object* v_k_3769_, lean_object* v_args_3770_, lean_object* v_cases_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3765_, v___x_3766_, v_score_3767_, v___x_3768_, v_k_3769_, v_args_3770_, v_cases_3771_);
lean_dec_ref(v_args_3770_);
lean_dec(v_k_3769_);
lean_dec(v___x_3768_);
lean_dec(v_score_3767_);
lean_dec_ref(v_snd_3765_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3773_, lean_object* v_result_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3781_ = lean_array_get_size(v_cases_3773_);
v___x_3782_ = lean_unsigned_to_nat(0u);
v___x_3783_ = lean_nat_dec_eq(v___x_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v_ca_3787_; lean_object* v_todo_3788_; lean_object* v_score_3789_; lean_object* v_c_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3856_; 
v___x_3784_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3785_ = lean_unsigned_to_nat(1u);
v___x_3786_ = lean_nat_sub(v___x_3781_, v___x_3785_);
v_ca_3787_ = lean_array_get(v___x_3784_, v_cases_3773_, v___x_3786_);
lean_dec(v___x_3786_);
v_todo_3788_ = lean_ctor_get(v_ca_3787_, 0);
v_score_3789_ = lean_ctor_get(v_ca_3787_, 1);
v_c_3790_ = lean_ctor_get(v_ca_3787_, 2);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_ca_3787_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3792_ = v_ca_3787_;
v_isShared_3793_ = v_isSharedCheck_3856_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_c_3790_);
lean_inc(v_score_3789_);
lean_inc(v_todo_3788_);
lean_dec(v_ca_3787_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3856_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3790_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_c_3790_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___y_3797_; lean_object* v___y_3798_; uint8_t v___y_3799_; lean_object* v___y_3800_; lean_object* v_snd_3823_; lean_object* v_fst_3824_; lean_object* v_fst_3825_; lean_object* v_snd_3826_; lean_object* v_cases_3827_; lean_object* v___x_3828_; uint8_t v___y_3830_; uint8_t v___x_3842_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
v_snd_3823_ = lean_ctor_get(v_a_3795_, 1);
lean_inc(v_snd_3823_);
v_fst_3824_ = lean_ctor_get(v_a_3795_, 0);
lean_inc(v_fst_3824_);
lean_dec(v_a_3795_);
v_fst_3825_ = lean_ctor_get(v_snd_3823_, 0);
lean_inc(v_fst_3825_);
v_snd_3826_ = lean_ctor_get(v_snd_3823_, 1);
lean_inc(v_snd_3826_);
lean_dec(v_snd_3823_);
v_cases_3827_ = lean_array_pop(v_cases_3773_);
v___x_3828_ = lean_array_get_size(v_todo_3788_);
v___x_3842_ = lean_nat_dec_eq(v___x_3828_, v___x_3782_);
if (v___x_3842_ == 0)
{
uint8_t v___x_3843_; 
lean_dec(v_fst_3824_);
v___x_3843_ = lean_nat_dec_eq(v_fst_3825_, v___x_3782_);
if (v___x_3843_ == 0)
{
v___y_3830_ = v___x_3843_;
goto v___jp_3829_;
}
else
{
lean_object* v_size_3844_; uint8_t v___x_3845_; 
v_size_3844_ = lean_ctor_get(v_snd_3826_, 0);
v___x_3845_ = lean_nat_dec_eq(v_size_3844_, v___x_3782_);
v___y_3830_ = v___x_3845_;
goto v___jp_3829_;
}
}
else
{
lean_object* v___x_3846_; 
lean_dec(v_snd_3826_);
lean_dec(v_fst_3825_);
lean_del_object(v___x_3792_);
lean_dec_ref(v_todo_3788_);
v___x_3846_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3774_, v_score_3789_, v_fst_3824_);
lean_dec(v_score_3789_);
v_cases_3773_ = v_cases_3827_;
v_result_3774_ = v___x_3846_;
goto _start;
}
v___jp_3796_:
{
uint8_t v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = 1;
v___x_3802_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3797_, v___x_3801_, v___y_3799_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v_fst_3804_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
v_fst_3804_ = lean_ctor_get(v_a_3803_, 0);
lean_inc(v_fst_3804_);
switch(lean_obj_tag(v_fst_3804_))
{
case 3:
{
lean_dec(v_a_3803_);
lean_dec_ref(v___y_3798_);
v_cases_3773_ = v___y_3800_;
goto _start;
}
case 5:
{
lean_object* v_snd_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v_snd_3806_ = lean_ctor_get(v_a_3803_, 1);
lean_inc(v_snd_3806_);
lean_dec(v_a_3803_);
v___x_3807_ = lean_box(4);
v___x_3808_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3798_);
v___x_3809_ = lean_apply_3(v___y_3798_, v___x_3807_, v___x_3808_, v___y_3800_);
v___x_3810_ = lean_apply_3(v___y_3798_, v_fst_3804_, v_snd_3806_, v___x_3809_);
v_cases_3773_ = v___x_3810_;
goto _start;
}
default: 
{
lean_object* v_snd_3812_; lean_object* v___x_3813_; 
v_snd_3812_ = lean_ctor_get(v_a_3803_, 1);
lean_inc(v_snd_3812_);
lean_dec(v_a_3803_);
v___x_3813_ = lean_apply_3(v___y_3798_, v_fst_3804_, v_snd_3812_, v___y_3800_);
v_cases_3773_ = v___x_3813_;
goto _start;
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec_ref(v___y_3800_);
lean_dec_ref(v___y_3798_);
lean_dec_ref(v_result_3774_);
v_a_3815_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3802_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3802_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
v___jp_3829_:
{
if (v___y_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___f_3835_; uint8_t v___x_3836_; 
v___x_3831_ = l_Lean_instInhabitedExpr;
v___x_3832_ = lean_nat_sub(v___x_3828_, v___x_3785_);
v___x_3833_ = lean_array_get(v___x_3831_, v_todo_3788_, v___x_3832_);
lean_dec(v___x_3832_);
v___x_3834_ = lean_array_pop(v_todo_3788_);
lean_inc(v_score_3789_);
lean_inc_ref(v___x_3834_);
v___f_3835_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3835_, 0, v_snd_3826_);
lean_closure_set(v___f_3835_, 1, v___x_3834_);
lean_closure_set(v___f_3835_, 2, v_score_3789_);
lean_closure_set(v___f_3835_, 3, v___x_3785_);
v___x_3836_ = lean_nat_dec_eq(v_fst_3825_, v___x_3782_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3838_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 2, v_fst_3825_);
lean_ctor_set(v___x_3792_, 0, v___x_3834_);
v___x_3838_ = v___x_3792_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_score_3789_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v_fst_3825_);
v___x_3838_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_array_push(v_cases_3827_, v___x_3838_);
v___y_3797_ = v___x_3833_;
v___y_3798_ = v___f_3835_;
v___y_3799_ = v___y_3830_;
v___y_3800_ = v___x_3839_;
goto v___jp_3796_;
}
}
else
{
lean_dec_ref(v___x_3834_);
lean_dec(v_fst_3825_);
lean_del_object(v___x_3792_);
lean_dec(v_score_3789_);
v___y_3797_ = v___x_3833_;
v___y_3798_ = v___f_3835_;
v___y_3799_ = v___y_3830_;
v___y_3800_ = v_cases_3827_;
goto v___jp_3796_;
}
}
else
{
lean_dec(v_snd_3826_);
lean_dec(v_fst_3825_);
lean_del_object(v___x_3792_);
lean_dec(v_score_3789_);
lean_dec_ref(v_todo_3788_);
v_cases_3773_ = v_cases_3827_;
goto _start;
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_del_object(v___x_3792_);
lean_dec(v_score_3789_);
lean_dec_ref(v_todo_3788_);
lean_dec_ref(v_result_3774_);
lean_dec_ref(v_cases_3773_);
v_a_3848_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3794_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3794_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
else
{
lean_object* v___x_3857_; 
lean_dec_ref(v_cases_3773_);
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v_result_3774_);
return v___x_3857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3858_, lean_object* v_result_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3858_, v_result_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3867_, lean_object* v_cases_3868_, lean_object* v_result_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3868_, v_result_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3877_, lean_object* v_cases_3878_, lean_object* v_result_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3877_, v_cases_3878_, v_result_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_box(3);
v___x_3897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3889_, v___x_3896_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
else
{
lean_object* v_val_3900_; lean_object* v___x_3901_; 
v_val_3900_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_val_3900_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3901_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3900_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
lean_dec(v_val_3900_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3913_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3913_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3913_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v_fst_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v_fst_3906_ = lean_ctor_get(v_a_3902_, 0);
lean_inc(v_fst_3906_);
lean_dec(v_a_3902_);
v___x_3907_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3908_ = lean_unsigned_to_nat(1u);
v___x_3909_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3907_, v___x_3908_, v_fst_3906_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3909_);
v___x_3911_ = v___x_3904_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
v_a_3914_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3901_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3901_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_root_3922_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3930_, lean_object* v_root_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3939_, lean_object* v_root_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3939_, v_root_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_root_3940_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3948_, lean_object* v_k_3949_, lean_object* v_args_3950_, lean_object* v_cases_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3948_, v_k_3949_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_dec_ref(v_args_3950_);
return v_cases_3951_;
}
else
{
lean_object* v_val_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_val_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_val_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3955_, 0, v_args_3950_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
lean_ctor_set(v___x_3955_, 2, v_val_3953_);
v___x_3956_ = lean_array_push(v_cases_3951_, v___x_3955_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3957_, lean_object* v_k_3958_, lean_object* v_args_3959_, lean_object* v_cases_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3957_, v_k_3958_, v_args_3959_, v_cases_3960_);
lean_dec(v_k_3958_);
lean_dec_ref(v_r_3957_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3964_, lean_object* v_e_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3964_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; uint8_t v___x_3974_; lean_object* v___x_3975_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = 1;
v___x_3975_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3965_, v___x_3974_, v___x_3974_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v_fst_3977_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref_known(v___x_3975_, 1);
v_fst_3977_ = lean_ctor_get(v_a_3976_, 0);
lean_inc(v_fst_3977_);
switch(lean_obj_tag(v_fst_3977_))
{
case 3:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_dec(v_a_3976_);
v___x_3978_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3979_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3978_, v_a_3973_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
return v___x_3979_;
}
case 5:
{
lean_object* v_snd_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v_snd_3980_ = lean_ctor_get(v_a_3976_, 1);
lean_inc(v_snd_3980_);
lean_dec(v_a_3976_);
v___x_3981_ = lean_box(4);
v___x_3982_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3983_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3964_, v___x_3981_, v___x_3982_, v___x_3982_);
v___x_3984_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3964_, v_fst_3977_, v_snd_3980_, v___x_3983_);
v___x_3985_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3984_, v_a_3973_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
return v___x_3985_;
}
default: 
{
lean_object* v_snd_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_snd_3986_ = lean_ctor_get(v_a_3976_, 1);
lean_inc(v_snd_3986_);
lean_dec(v_a_3976_);
v___x_3987_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3988_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3964_, v_fst_3977_, v_snd_3986_, v___x_3987_);
lean_dec(v_fst_3977_);
v___x_3989_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3988_, v_a_3973_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
return v___x_3989_;
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_a_3973_);
v_a_3990_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3975_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3975_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_dec_ref(v_e_3965_);
return v___x_3972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3998_, lean_object* v_e_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3998_, v_e_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_root_3998_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4007_, lean_object* v_root_4008_, lean_object* v_e_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4008_, v_e_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4017_, lean_object* v_root_4018_, lean_object* v_e_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4017_, v_root_4018_, v_e_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
lean_dec(v_a_4024_);
lean_dec_ref(v_a_4023_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_root_4018_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4027_, lean_object* v_e_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v_roots_4034_; lean_object* v_keyedConfig_4035_; uint8_t v_trackZetaDelta_4036_; lean_object* v_zetaDeltaSet_4037_; lean_object* v_lctx_4038_; lean_object* v_localInstances_4039_; lean_object* v_defEqCtx_x3f_4040_; lean_object* v_synthPendingDepth_4041_; lean_object* v_customCanUnfoldPredicate_x3f_4042_; uint8_t v_univApprox_4043_; uint8_t v_inTypeClassResolution_4044_; uint8_t v_cacheInferType_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_roots_4034_ = lean_ctor_get(v_d_4027_, 1);
v_keyedConfig_4035_ = lean_ctor_get(v_a_4029_, 0);
v_trackZetaDelta_4036_ = lean_ctor_get_uint8(v_a_4029_, sizeof(void*)*7);
v_zetaDeltaSet_4037_ = lean_ctor_get(v_a_4029_, 1);
v_lctx_4038_ = lean_ctor_get(v_a_4029_, 2);
v_localInstances_4039_ = lean_ctor_get(v_a_4029_, 3);
v_defEqCtx_x3f_4040_ = lean_ctor_get(v_a_4029_, 4);
v_synthPendingDepth_4041_ = lean_ctor_get(v_a_4029_, 5);
v_customCanUnfoldPredicate_x3f_4042_ = lean_ctor_get(v_a_4029_, 6);
v_univApprox_4043_ = lean_ctor_get_uint8(v_a_4029_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4044_ = lean_ctor_get_uint8(v_a_4029_, sizeof(void*)*7 + 2);
v_cacheInferType_4045_ = lean_ctor_get_uint8(v_a_4029_, sizeof(void*)*7 + 3);
lean_inc_ref(v_roots_4034_);
v___x_4046_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4046_, 0, lean_box(0));
lean_closure_set(v___x_4046_, 1, v_roots_4034_);
lean_closure_set(v___x_4046_, 2, v_e_4028_);
v___x_4047_ = 2;
lean_inc_ref(v_keyedConfig_4035_);
v___x_4048_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4047_, v_keyedConfig_4035_);
lean_inc(v_customCanUnfoldPredicate_x3f_4042_);
lean_inc(v_synthPendingDepth_4041_);
lean_inc(v_defEqCtx_x3f_4040_);
lean_inc_ref(v_localInstances_4039_);
lean_inc_ref(v_lctx_4038_);
lean_inc(v_zetaDeltaSet_4037_);
v___x_4049_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
lean_ctor_set(v___x_4049_, 1, v_zetaDeltaSet_4037_);
lean_ctor_set(v___x_4049_, 2, v_lctx_4038_);
lean_ctor_set(v___x_4049_, 3, v_localInstances_4039_);
lean_ctor_set(v___x_4049_, 4, v_defEqCtx_x3f_4040_);
lean_ctor_set(v___x_4049_, 5, v_synthPendingDepth_4041_);
lean_ctor_set(v___x_4049_, 6, v_customCanUnfoldPredicate_x3f_4042_);
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*7, v_trackZetaDelta_4036_);
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*7 + 1, v_univApprox_4043_);
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4044_);
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*7 + 3, v_cacheInferType_4045_);
v___x_4050_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4027_, v___x_4046_, v___x_4049_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec_ref_known(v___x_4049_, 7);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4051_, lean_object* v_e_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4051_, v_e_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4059_, lean_object* v_d_4060_, lean_object* v_e_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4060_, v_e_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4068_, lean_object* v_d_4069_, lean_object* v_e_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4068_, v_d_4069_, v_e_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_);
lean_dec(v_a_4074_);
lean_dec_ref(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
return v_res_4076_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4080_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4079_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4085_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4087_, lean_object* v_k_4088_, lean_object* v_f_4089_){
_start:
{
lean_object* v_roots_4090_; lean_object* v_tries_4091_; lean_object* v___x_4092_; 
v_roots_4090_ = lean_ctor_get(v_d_4087_, 0);
v_tries_4091_ = lean_ctor_get(v_d_4087_, 1);
v___x_4092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4090_, v_k_4088_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4104_; 
lean_inc_ref(v_tries_4091_);
lean_inc_ref(v_roots_4090_);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_d_4087_);
if (v_isSharedCheck_4104_ == 0)
{
lean_object* v_unused_4105_; lean_object* v_unused_4106_; 
v_unused_4105_ = lean_ctor_get(v_d_4087_, 1);
lean_dec(v_unused_4105_);
v_unused_4106_ = lean_ctor_get(v_d_4087_, 0);
lean_dec(v_unused_4106_);
v___x_4094_ = v_d_4087_;
v_isShared_4095_ = v_isSharedCheck_4104_;
goto v_resetjp_4093_;
}
else
{
lean_dec(v_d_4087_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4104_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v_roots_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4102_; 
v___x_4096_ = lean_array_get_size(v_tries_4091_);
v_roots_4097_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4090_, v_k_4088_, v___x_4096_);
v___x_4098_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_4099_ = lean_apply_1(v_f_4089_, v___x_4098_);
v___x_4100_ = lean_array_push(v_tries_4091_, v___x_4099_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v___x_4100_);
lean_ctor_set(v___x_4094_, 0, v_roots_4097_);
v___x_4102_ = v___x_4094_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_roots_4097_);
lean_ctor_set(v_reuseFailAlloc_4103_, 1, v___x_4100_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
else
{
lean_object* v_val_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
lean_dec(v_k_4088_);
v_val_4107_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_val_4107_);
lean_dec_ref_known(v___x_4092_, 1);
v___x_4108_ = lean_array_get_size(v_tries_4091_);
v___x_4109_ = lean_nat_dec_lt(v_val_4107_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_dec(v_val_4107_);
lean_dec_ref(v_f_4089_);
return v_d_4087_;
}
else
{
lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4121_; 
lean_inc_ref(v_tries_4091_);
lean_inc_ref(v_roots_4090_);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_d_4087_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; lean_object* v_unused_4123_; 
v_unused_4122_ = lean_ctor_get(v_d_4087_, 1);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_d_4087_, 0);
lean_dec(v_unused_4123_);
v___x_4111_ = v_d_4087_;
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
else
{
lean_dec(v_d_4087_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v_v_4113_; lean_object* v___x_4114_; lean_object* v_xs_x27_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4119_; 
v_v_4113_ = lean_array_fget(v_tries_4091_, v_val_4107_);
v___x_4114_ = lean_box(0);
v_xs_x27_4115_ = lean_array_fset(v_tries_4091_, v_val_4107_, v___x_4114_);
v___x_4116_ = lean_apply_1(v_f_4089_, v_v_4113_);
v___x_4117_ = lean_array_fset(v_xs_x27_4115_, v_val_4107_, v___x_4116_);
lean_dec(v_val_4107_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 1, v___x_4117_);
v___x_4119_ = v___x_4111_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_roots_4090_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4124_, lean_object* v_d_4125_, lean_object* v_k_4126_, lean_object* v_f_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4125_, v_k_4126_, v_f_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4129_, lean_object* v_x_4130_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_array_push(v_x_4130_, v_e_4129_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4132_, lean_object* v_k_4133_, lean_object* v_e_4134_){
_start:
{
lean_object* v___f_4135_; lean_object* v___x_4136_; 
v___f_4135_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4135_, 0, v_e_4134_);
v___x_4136_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4132_, v_k_4133_, v___f_4135_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4137_, lean_object* v_d_4138_, lean_object* v_k_4139_, lean_object* v_e_4140_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4138_, v_k_4139_, v_e_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4142_, size_t v_i_4143_, lean_object* v_bs_4144_){
_start:
{
uint8_t v___x_4145_; 
v___x_4145_ = lean_usize_dec_lt(v_i_4143_, v_sz_4142_);
if (v___x_4145_ == 0)
{
return v_bs_4144_;
}
else
{
lean_object* v_v_4146_; lean_object* v___x_4147_; lean_object* v_bs_x27_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; size_t v___x_4152_; size_t v___x_4153_; lean_object* v___x_4154_; 
v_v_4146_ = lean_array_uget(v_bs_4144_, v_i_4143_);
v___x_4147_ = lean_unsigned_to_nat(0u);
v_bs_x27_4148_ = lean_array_uset(v_bs_4144_, v_i_4143_, v___x_4147_);
v___x_4149_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4150_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4147_);
lean_ctor_set(v___x_4151_, 2, v___x_4150_);
lean_ctor_set(v___x_4151_, 3, v_v_4146_);
v___x_4152_ = ((size_t)1ULL);
v___x_4153_ = lean_usize_add(v_i_4143_, v___x_4152_);
v___x_4154_ = lean_array_uset(v_bs_x27_4148_, v_i_4143_, v___x_4151_);
v_i_4143_ = v___x_4153_;
v_bs_4144_ = v___x_4154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4156_, lean_object* v_i_4157_, lean_object* v_bs_4158_){
_start:
{
size_t v_sz_boxed_4159_; size_t v_i_boxed_4160_; lean_object* v_res_4161_; 
v_sz_boxed_4159_ = lean_unbox_usize(v_sz_4156_);
lean_dec(v_sz_4156_);
v_i_boxed_4160_ = lean_unbox_usize(v_i_4157_);
lean_dec(v_i_4157_);
v_res_4161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4159_, v_i_boxed_4160_, v_bs_4158_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4162_, lean_object* v_x_4163_){
_start:
{
if (lean_obj_tag(v_x_4163_) == 0)
{
return v_x_4162_;
}
else
{
lean_object* v_key_4164_; lean_object* v_value_4165_; lean_object* v_tail_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_key_4164_ = lean_ctor_get(v_x_4163_, 0);
lean_inc(v_key_4164_);
v_value_4165_ = lean_ctor_get(v_x_4163_, 1);
lean_inc(v_value_4165_);
v_tail_4166_ = lean_ctor_get(v_x_4163_, 2);
lean_inc(v_tail_4166_);
lean_dec_ref_known(v_x_4163_, 3);
v___x_4167_ = lean_unsigned_to_nat(1u);
v___x_4168_ = lean_nat_add(v_value_4165_, v___x_4167_);
lean_dec(v_value_4165_);
v___x_4169_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4162_, v_key_4164_, v___x_4168_);
v_x_4162_ = v___x_4169_;
v_x_4163_ = v_tail_4166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4171_, size_t v_i_4172_, size_t v_stop_4173_, lean_object* v_b_4174_){
_start:
{
uint8_t v___x_4175_; 
v___x_4175_ = lean_usize_dec_eq(v_i_4172_, v_stop_4173_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; lean_object* v___x_4177_; size_t v___x_4178_; size_t v___x_4179_; 
v___x_4176_ = lean_array_uget_borrowed(v_as_4171_, v_i_4172_);
lean_inc(v___x_4176_);
v___x_4177_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4174_, v___x_4176_);
v___x_4178_ = ((size_t)1ULL);
v___x_4179_ = lean_usize_add(v_i_4172_, v___x_4178_);
v_i_4172_ = v___x_4179_;
v_b_4174_ = v___x_4177_;
goto _start;
}
else
{
return v_b_4174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4181_, lean_object* v_i_4182_, lean_object* v_stop_4183_, lean_object* v_b_4184_){
_start:
{
size_t v_i_boxed_4185_; size_t v_stop_boxed_4186_; lean_object* v_res_4187_; 
v_i_boxed_4185_ = lean_unbox_usize(v_i_4182_);
lean_dec(v_i_4182_);
v_stop_boxed_4186_ = lean_unbox_usize(v_stop_4183_);
lean_dec(v_stop_4183_);
v_res_4187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4181_, v_i_boxed_4185_, v_stop_boxed_4186_, v_b_4184_);
lean_dec_ref(v_as_4181_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4188_){
_start:
{
lean_object* v_roots_4189_; lean_object* v_tries_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4217_; 
v_roots_4189_ = lean_ctor_get(v_d_4188_, 0);
v_tries_4190_ = lean_ctor_get(v_d_4188_, 1);
v_isSharedCheck_4217_ = !lean_is_exclusive(v_d_4188_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4192_ = v_d_4188_;
v_isShared_4193_ = v_isSharedCheck_4217_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_tries_4190_);
lean_inc(v_roots_4189_);
lean_dec(v_d_4188_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4217_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___y_4195_; lean_object* v_buckets_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; 
v_buckets_4206_ = lean_ctor_get(v_roots_4189_, 1);
v___x_4207_ = lean_unsigned_to_nat(0u);
v___x_4208_ = lean_array_get_size(v_buckets_4206_);
v___x_4209_ = lean_nat_dec_lt(v___x_4207_, v___x_4208_);
if (v___x_4209_ == 0)
{
v___y_4195_ = v_roots_4189_;
goto v___jp_4194_;
}
else
{
uint8_t v___x_4210_; 
v___x_4210_ = lean_nat_dec_le(v___x_4208_, v___x_4208_);
if (v___x_4210_ == 0)
{
if (v___x_4209_ == 0)
{
v___y_4195_ = v_roots_4189_;
goto v___jp_4194_;
}
else
{
size_t v___x_4211_; size_t v___x_4212_; lean_object* v___x_4213_; 
lean_inc_ref(v_buckets_4206_);
v___x_4211_ = ((size_t)0ULL);
v___x_4212_ = lean_usize_of_nat(v___x_4208_);
v___x_4213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4206_, v___x_4211_, v___x_4212_, v_roots_4189_);
lean_dec_ref(v_buckets_4206_);
v___y_4195_ = v___x_4213_;
goto v___jp_4194_;
}
}
else
{
size_t v___x_4214_; size_t v___x_4215_; lean_object* v___x_4216_; 
lean_inc_ref(v_buckets_4206_);
v___x_4214_ = ((size_t)0ULL);
v___x_4215_ = lean_usize_of_nat(v___x_4208_);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4206_, v___x_4214_, v___x_4215_, v_roots_4189_);
lean_dec_ref(v_buckets_4206_);
v___y_4195_ = v___x_4216_;
goto v___jp_4194_;
}
}
v___jp_4194_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; size_t v_sz_4199_; size_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4204_; 
v___x_4196_ = lean_unsigned_to_nat(1u);
v___x_4197_ = lean_mk_empty_array_with_capacity(v___x_4196_);
lean_dec_ref(v___x_4197_);
v___x_4198_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4199_ = lean_array_size(v_tries_4190_);
v___x_4200_ = ((size_t)0ULL);
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4199_, v___x_4200_, v_tries_4190_);
v___x_4202_ = l_Array_append___redArg(v___x_4198_, v___x_4201_);
lean_dec_ref(v___x_4201_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 1, v___y_4195_);
lean_ctor_set(v___x_4192_, 0, v___x_4202_);
v___x_4204_ = v___x_4192_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4202_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v___y_4195_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4218_, lean_object* v_d_4219_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4221_, size_t v_sz_4222_, size_t v_i_4223_, lean_object* v_bs_4224_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4222_, v_i_4223_, v_bs_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4226_, lean_object* v_sz_4227_, lean_object* v_i_4228_, lean_object* v_bs_4229_){
_start:
{
size_t v_sz_boxed_4230_; size_t v_i_boxed_4231_; lean_object* v_res_4232_; 
v_sz_boxed_4230_ = lean_unbox_usize(v_sz_4227_);
lean_dec(v_sz_4227_);
v_i_boxed_4231_ = lean_unbox_usize(v_i_4228_);
lean_dec(v_i_4228_);
v_res_4232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4226_, v_sz_boxed_4230_, v_i_boxed_4231_, v_bs_4229_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4233_, lean_object* v_x_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Array_append___redArg(v_x_4234_, v_y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4236_, lean_object* v_x_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4236_, v_x_4237_);
lean_dec_ref(v_y_4236_);
return v_res_4238_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Array_instInhabited(lean_box(0));
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4240_, lean_object* v_snd_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_){
_start:
{
if (lean_obj_tag(v_x_4243_) == 0)
{
lean_dec_ref(v_snd_4241_);
return v_x_4242_;
}
else
{
lean_object* v_key_4244_; lean_object* v_value_4245_; lean_object* v_tail_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v_key_4244_ = lean_ctor_get(v_x_4243_, 0);
lean_inc(v_key_4244_);
v_value_4245_ = lean_ctor_get(v_x_4243_, 1);
lean_inc(v_value_4245_);
v_tail_4246_ = lean_ctor_get(v_x_4243_, 2);
lean_inc(v_tail_4246_);
lean_dec_ref_known(v_x_4243_, 3);
v___x_4247_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4248_ = lean_array_get_borrowed(v___x_4247_, v_tries_4240_, v_value_4245_);
lean_dec(v_value_4245_);
lean_inc_ref(v_snd_4241_);
lean_inc(v___x_4248_);
v___x_4249_ = lean_apply_1(v_snd_4241_, v___x_4248_);
v___x_4250_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4242_, v_key_4244_, v___x_4249_);
v_x_4242_ = v___x_4250_;
v_x_4243_ = v_tail_4246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4252_, lean_object* v_snd_4253_, lean_object* v_x_4254_, lean_object* v_x_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4252_, v_snd_4253_, v_x_4254_, v_x_4255_);
lean_dec_ref(v_tries_4252_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4257_, lean_object* v_snd_4258_, lean_object* v_as_4259_, size_t v_i_4260_, size_t v_stop_4261_, lean_object* v_b_4262_){
_start:
{
uint8_t v___x_4263_; 
v___x_4263_ = lean_usize_dec_eq(v_i_4260_, v_stop_4261_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; lean_object* v___x_4265_; size_t v___x_4266_; size_t v___x_4267_; 
v___x_4264_ = lean_array_uget_borrowed(v_as_4259_, v_i_4260_);
lean_inc(v___x_4264_);
lean_inc_ref(v_snd_4258_);
v___x_4265_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4257_, v_snd_4258_, v_b_4262_, v___x_4264_);
v___x_4266_ = ((size_t)1ULL);
v___x_4267_ = lean_usize_add(v_i_4260_, v___x_4266_);
v_i_4260_ = v___x_4267_;
v_b_4262_ = v___x_4265_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4258_);
return v_b_4262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4269_, lean_object* v_snd_4270_, lean_object* v_as_4271_, lean_object* v_i_4272_, lean_object* v_stop_4273_, lean_object* v_b_4274_){
_start:
{
size_t v_i_boxed_4275_; size_t v_stop_boxed_4276_; lean_object* v_res_4277_; 
v_i_boxed_4275_ = lean_unbox_usize(v_i_4272_);
lean_dec(v_i_4272_);
v_stop_boxed_4276_ = lean_unbox_usize(v_stop_4273_);
lean_dec(v_stop_4273_);
v_res_4277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4269_, v_snd_4270_, v_as_4271_, v_i_boxed_4275_, v_stop_boxed_4276_, v_b_4274_);
lean_dec_ref(v_as_4271_);
lean_dec_ref(v_tries_4269_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4280_, lean_object* v_y_4281_){
_start:
{
lean_object* v_fst_4283_; lean_object* v_buckets_4284_; lean_object* v_tries_4285_; lean_object* v_snd_4286_; lean_object* v_roots_4297_; lean_object* v_roots_4298_; lean_object* v_tries_4299_; lean_object* v_size_4300_; lean_object* v_buckets_4301_; lean_object* v_tries_4302_; lean_object* v_size_4303_; lean_object* v_buckets_4304_; uint8_t v___x_4305_; 
v_roots_4297_ = lean_ctor_get(v_y_4281_, 0);
v_roots_4298_ = lean_ctor_get(v_x_4280_, 0);
v_tries_4299_ = lean_ctor_get(v_y_4281_, 1);
v_size_4300_ = lean_ctor_get(v_roots_4297_, 0);
v_buckets_4301_ = lean_ctor_get(v_roots_4297_, 1);
v_tries_4302_ = lean_ctor_get(v_x_4280_, 1);
v_size_4303_ = lean_ctor_get(v_roots_4298_, 0);
v_buckets_4304_ = lean_ctor_get(v_roots_4298_, 1);
v___x_4305_ = lean_nat_dec_le(v_size_4300_, v_size_4303_);
if (v___x_4305_ == 0)
{
lean_object* v___f_4306_; 
lean_inc_ref(v_buckets_4304_);
lean_inc_ref(v_tries_4302_);
lean_dec_ref(v_x_4280_);
v___f_4306_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4283_ = v_y_4281_;
v_buckets_4284_ = v_buckets_4304_;
v_tries_4285_ = v_tries_4302_;
v_snd_4286_ = v___f_4306_;
goto v___jp_4282_;
}
else
{
lean_object* v___f_4307_; 
lean_inc_ref(v_buckets_4301_);
lean_inc_ref(v_tries_4299_);
lean_dec_ref(v_y_4281_);
v___f_4307_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4283_ = v_x_4280_;
v_buckets_4284_ = v_buckets_4301_;
v_tries_4285_ = v_tries_4299_;
v_snd_4286_ = v___f_4307_;
goto v___jp_4282_;
}
v___jp_4282_:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
v___x_4287_ = lean_unsigned_to_nat(0u);
v___x_4288_ = lean_array_get_size(v_buckets_4284_);
v___x_4289_ = lean_nat_dec_lt(v___x_4287_, v___x_4288_);
if (v___x_4289_ == 0)
{
lean_dec_ref(v_tries_4285_);
lean_dec_ref(v_buckets_4284_);
return v_fst_4283_;
}
else
{
uint8_t v___x_4290_; 
v___x_4290_ = lean_nat_dec_le(v___x_4288_, v___x_4288_);
if (v___x_4290_ == 0)
{
if (v___x_4289_ == 0)
{
lean_dec_ref(v_tries_4285_);
lean_dec_ref(v_buckets_4284_);
return v_fst_4283_;
}
else
{
size_t v___x_4291_; size_t v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = ((size_t)0ULL);
v___x_4292_ = lean_usize_of_nat(v___x_4288_);
lean_inc_ref(v_snd_4286_);
v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4285_, v_snd_4286_, v_buckets_4284_, v___x_4291_, v___x_4292_, v_fst_4283_);
lean_dec_ref(v_buckets_4284_);
lean_dec_ref(v_tries_4285_);
return v___x_4293_;
}
}
else
{
size_t v___x_4294_; size_t v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = ((size_t)0ULL);
v___x_4295_ = lean_usize_of_nat(v___x_4288_);
lean_inc_ref(v_snd_4286_);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4285_, v_snd_4286_, v_buckets_4284_, v___x_4294_, v___x_4295_, v_fst_4283_);
lean_dec_ref(v_buckets_4284_);
lean_dec_ref(v_tries_4285_);
return v___x_4296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4308_, lean_object* v_x_4309_, lean_object* v_y_4310_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4309_, v_y_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4312_, lean_object* v_tries_4313_, lean_object* v_snd_4314_, lean_object* v_x_4315_, lean_object* v_x_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4313_, v_snd_4314_, v_x_4315_, v_x_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4318_, lean_object* v_tries_4319_, lean_object* v_snd_4320_, lean_object* v_x_4321_, lean_object* v_x_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4318_, v_tries_4319_, v_snd_4320_, v_x_4321_, v_x_4322_);
lean_dec_ref(v_tries_4319_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4324_, lean_object* v_tries_4325_, lean_object* v_snd_4326_, lean_object* v_as_4327_, size_t v_i_4328_, size_t v_stop_4329_, lean_object* v_b_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4325_, v_snd_4326_, v_as_4327_, v_i_4328_, v_stop_4329_, v_b_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4332_, lean_object* v_tries_4333_, lean_object* v_snd_4334_, lean_object* v_as_4335_, lean_object* v_i_4336_, lean_object* v_stop_4337_, lean_object* v_b_4338_){
_start:
{
size_t v_i_boxed_4339_; size_t v_stop_boxed_4340_; lean_object* v_res_4341_; 
v_i_boxed_4339_ = lean_unbox_usize(v_i_4336_);
lean_dec(v_i_4336_);
v_stop_boxed_4340_ = lean_unbox_usize(v_stop_4337_);
lean_dec(v_stop_4337_);
v_res_4341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4332_, v_tries_4333_, v_snd_4334_, v_as_4335_, v_i_boxed_4339_, v_stop_boxed_4340_, v_b_4338_);
lean_dec_ref(v_as_4335_);
lean_dec_ref(v_tries_4333_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4343_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4345_, lean_object* v_value_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4345_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4374_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4374_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4374_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v_fst_4357_; lean_object* v_snd_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4373_; 
v_fst_4357_ = lean_ctor_get(v_a_4353_, 0);
v_snd_4358_ = lean_ctor_get(v_a_4353_, 1);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_a_4353_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4360_ = v_a_4353_;
v_isShared_4361_ = v_isSharedCheck_4373_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_snd_4358_);
lean_inc(v_fst_4357_);
lean_dec(v_a_4353_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4373_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v_lctx_4362_; lean_object* v_localInstances_4363_; lean_object* v___x_4365_; 
v_lctx_4362_ = lean_ctor_get(v_a_4347_, 2);
v_localInstances_4363_ = lean_ctor_get(v_a_4347_, 3);
lean_inc_ref(v_localInstances_4363_);
lean_inc_ref(v_lctx_4362_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 1, v_localInstances_4363_);
lean_ctor_set(v___x_4360_, 0, v_lctx_4362_);
v___x_4365_ = v___x_4360_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_lctx_4362_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_localInstances_4363_);
v___x_4365_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
lean_ctor_set(v___x_4366_, 1, v_value_4346_);
v___x_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4367_, 0, v_snd_4358_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v_fst_4357_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4368_);
v___x_4370_ = v___x_4355_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec(v_value_4346_);
v_a_4375_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4352_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4352_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4383_, lean_object* v_value_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4383_, v_value_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4391_, lean_object* v_expr_4392_, lean_object* v_value_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4392_, v_value_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4400_, lean_object* v_expr_4401_, lean_object* v_value_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4400_, v_expr_4401_, v_value_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_a_4406_);
lean_dec_ref(v_a_4405_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4409_, lean_object* v_idx_4410_, lean_object* v_value_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v_entry_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4463_; 
v_entry_4417_ = lean_ctor_get(v_e_4409_, 1);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_e_4409_);
if (v_isSharedCheck_4463_ == 0)
{
lean_object* v_unused_4464_; 
v_unused_4464_ = lean_ctor_get(v_e_4409_, 0);
lean_dec(v_unused_4464_);
v___x_4419_ = v_e_4409_;
v_isShared_4420_ = v_isSharedCheck_4463_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_entry_4417_);
lean_dec(v_e_4409_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4463_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v_snd_4421_; lean_object* v_fst_4422_; lean_object* v_fst_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4461_; 
v_snd_4421_ = lean_ctor_get(v_entry_4417_, 1);
lean_inc(v_snd_4421_);
v_fst_4422_ = lean_ctor_get(v_entry_4417_, 0);
lean_inc(v_fst_4422_);
lean_dec_ref(v_entry_4417_);
v_fst_4423_ = lean_ctor_get(v_snd_4421_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_snd_4421_);
if (v_isSharedCheck_4461_ == 0)
{
lean_object* v_unused_4462_; 
v_unused_4462_ = lean_ctor_get(v_snd_4421_, 1);
lean_dec(v_unused_4462_);
v___x_4425_ = v_snd_4421_;
v_isShared_4426_ = v_isSharedCheck_4461_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_fst_4423_);
lean_dec(v_snd_4421_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4461_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4427_ = l_Lean_instInhabitedExpr;
v___x_4428_ = lean_array_get(v___x_4427_, v_fst_4422_, v_idx_4410_);
lean_dec(v_fst_4422_);
v___x_4429_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4428_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4452_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4432_ = v___x_4429_;
v_isShared_4433_ = v_isSharedCheck_4452_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4452_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v_fst_4434_; lean_object* v_snd_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4451_; 
v_fst_4434_ = lean_ctor_get(v_a_4430_, 0);
v_snd_4435_ = lean_ctor_get(v_a_4430_, 1);
v_isSharedCheck_4451_ = !lean_is_exclusive(v_a_4430_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4437_ = v_a_4430_;
v_isShared_4438_ = v_isSharedCheck_4451_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_snd_4435_);
lean_inc(v_fst_4434_);
lean_dec(v_a_4430_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4451_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
lean_ctor_set(v___x_4437_, 1, v_value_4411_);
lean_ctor_set(v___x_4437_, 0, v_fst_4423_);
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_fst_4423_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_value_4411_);
v___x_4440_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
lean_object* v___x_4442_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 1, v___x_4440_);
lean_ctor_set(v___x_4425_, 0, v_snd_4435_);
v___x_4442_ = v___x_4425_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_snd_4435_);
lean_ctor_set(v_reuseFailAlloc_4449_, 1, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4444_; 
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 1, v___x_4442_);
lean_ctor_set(v___x_4419_, 0, v_fst_4434_);
v___x_4444_ = v___x_4419_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_fst_4434_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4442_);
v___x_4444_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4446_; 
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4444_);
v___x_4446_ = v___x_4432_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4425_);
lean_dec(v_fst_4423_);
lean_del_object(v___x_4419_);
lean_dec(v_value_4411_);
v_a_4453_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4429_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4429_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4465_, lean_object* v_idx_4466_, lean_object* v_value_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4465_, v_idx_4466_, v_value_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
lean_dec(v_a_4471_);
lean_dec_ref(v_a_4470_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_idx_4466_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4474_, lean_object* v_e_4475_, lean_object* v_idx_4476_, lean_object* v_value_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4475_, v_idx_4476_, v_value_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4484_, lean_object* v_e_4485_, lean_object* v_idx_4486_, lean_object* v_value_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4484_, v_e_4485_, v_idx_4486_, v_value_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
lean_dec(v_idx_4486_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4497_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4498_ = lean_st_mk_ref(v___x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4500_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4501_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
return v___x_4503_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
return v___x_4505_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4507_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
lean_ctor_set(v___x_4507_, 1, v___x_4506_);
lean_ctor_set(v___x_4507_, 2, v___x_4506_);
lean_ctor_set(v___x_4507_, 3, v___x_4506_);
lean_ctor_set(v___x_4507_, 4, v___x_4506_);
lean_ctor_set(v___x_4507_, 5, v___x_4506_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4508_){
_start:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4509_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4510_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4511_, 0, v_ngen_4508_);
lean_ctor_set(v___x_4511_, 1, v___x_4509_);
lean_ctor_set(v___x_4511_, 2, v___x_4510_);
return v___x_4511_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4512_, lean_object* v_declName_4513_){
_start:
{
uint8_t v___x_4514_; 
v___x_4514_ = l_Lean_isPrivateName(v_declName_4513_);
if (v___x_4514_ == 0)
{
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4512_, v_declName_4513_);
if (lean_obj_tag(v___x_4515_) == 0)
{
return v___x_4514_;
}
else
{
lean_object* v_val_4516_; lean_object* v___x_4517_; uint8_t v_isModule_4518_; 
v_val_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_val_4516_);
lean_dec_ref_known(v___x_4515_, 1);
v___x_4517_ = l_Lean_Environment_header(v_env_4512_);
v_isModule_4518_ = lean_ctor_get_uint8(v___x_4517_, sizeof(void*)*7 + 4);
if (v_isModule_4518_ == 0)
{
lean_dec_ref(v___x_4517_);
lean_dec(v_val_4516_);
return v_isModule_4518_;
}
else
{
lean_object* v_modules_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v_modules_4519_ = lean_ctor_get(v___x_4517_, 3);
lean_inc_ref(v_modules_4519_);
lean_dec_ref(v___x_4517_);
v___x_4520_ = lean_array_get_size(v_modules_4519_);
v___x_4521_ = lean_nat_dec_lt(v_val_4516_, v___x_4520_);
if (v___x_4521_ == 0)
{
lean_dec_ref(v_modules_4519_);
lean_dec(v_val_4516_);
return v___x_4521_;
}
else
{
lean_object* v___x_4522_; lean_object* v_toImport_4523_; uint8_t v_importAll_4524_; 
v___x_4522_ = lean_array_fget(v_modules_4519_, v_val_4516_);
lean_dec(v_val_4516_);
lean_dec_ref(v_modules_4519_);
v_toImport_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc_ref(v_toImport_4523_);
lean_dec(v___x_4522_);
v_importAll_4524_ = lean_ctor_get_uint8(v_toImport_4523_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4523_);
return v_importAll_4524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4525_, lean_object* v_declName_4526_){
_start:
{
uint8_t v_res_4527_; lean_object* v_r_4528_; 
v_res_4527_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4525_, v_declName_4526_);
lean_dec(v_declName_4526_);
lean_dec_ref(v_env_4525_);
v_r_4528_ = lean_box(v_res_4527_);
return v_r_4528_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4534_, lean_object* v_declName_4535_){
_start:
{
uint8_t v___x_4536_; 
lean_inc(v_declName_4535_);
lean_inc_ref(v_env_4534_);
v___x_4536_ = l_Lean_Meta_allowCompletion(v_env_4534_, v_declName_4535_);
if (v___x_4536_ == 0)
{
uint8_t v___x_4537_; 
lean_dec(v_declName_4535_);
lean_dec_ref(v_env_4534_);
v___x_4537_ = 1;
return v___x_4537_;
}
else
{
lean_object* v___x_4538_; uint8_t v___x_4539_; uint8_t v___y_4549_; 
v___x_4538_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4539_ = lean_name_eq(v_declName_4535_, v___x_4538_);
if (v___x_4539_ == 0)
{
uint8_t v___x_4550_; 
lean_inc(v_declName_4535_);
v___x_4550_ = l_Lean_Name_isInternalDetail(v_declName_4535_);
if (v___x_4550_ == 0)
{
lean_dec_ref(v_env_4534_);
v___y_4549_ = v___x_4550_;
goto v___jp_4548_;
}
else
{
uint8_t v___x_4551_; 
v___x_4551_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4534_, v_declName_4535_);
lean_dec_ref(v_env_4534_);
if (v___x_4551_ == 0)
{
v___y_4549_ = v___x_4550_;
goto v___jp_4548_;
}
else
{
goto v___jp_4544_;
}
}
}
else
{
lean_dec(v_declName_4535_);
lean_dec_ref(v_env_4534_);
return v___x_4539_;
}
v___jp_4540_:
{
if (lean_obj_tag(v_declName_4535_) == 1)
{
lean_object* v_str_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; 
v_str_4541_ = lean_ctor_get(v_declName_4535_, 1);
lean_inc_ref(v_str_4541_);
lean_dec_ref_known(v_declName_4535_, 2);
v___x_4542_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4543_ = lean_string_dec_eq(v_str_4541_, v___x_4542_);
lean_dec_ref(v_str_4541_);
if (v___x_4543_ == 0)
{
return v___x_4539_;
}
else
{
return v___x_4536_;
}
}
else
{
lean_dec(v_declName_4535_);
return v___x_4539_;
}
}
v___jp_4544_:
{
if (lean_obj_tag(v_declName_4535_) == 1)
{
lean_object* v_str_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; 
v_str_4545_ = lean_ctor_get(v_declName_4535_, 1);
v___x_4546_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4547_ = lean_string_dec_eq(v_str_4545_, v___x_4546_);
if (v___x_4547_ == 0)
{
goto v___jp_4540_;
}
else
{
lean_dec_ref_known(v_declName_4535_, 2);
return v___x_4536_;
}
}
else
{
goto v___jp_4540_;
}
}
v___jp_4548_:
{
if (v___y_4549_ == 0)
{
goto v___jp_4544_;
}
else
{
lean_dec(v_declName_4535_);
return v___y_4549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4552_, lean_object* v_declName_4553_){
_start:
{
uint8_t v_res_4554_; lean_object* v_r_4555_; 
v_res_4554_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4552_, v_declName_4553_);
v_r_4555_ = lean_box(v_res_4554_);
return v_r_4555_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4556_, lean_object* v_opt_4557_){
_start:
{
lean_object* v_name_4558_; lean_object* v_defValue_4559_; lean_object* v_map_4560_; lean_object* v___x_4561_; 
v_name_4558_ = lean_ctor_get(v_opt_4557_, 0);
v_defValue_4559_ = lean_ctor_get(v_opt_4557_, 1);
v_map_4560_ = lean_ctor_get(v_opts_4556_, 0);
v___x_4561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4560_, v_name_4558_);
if (lean_obj_tag(v___x_4561_) == 0)
{
uint8_t v___x_4562_; 
v___x_4562_ = lean_unbox(v_defValue_4559_);
return v___x_4562_;
}
else
{
lean_object* v_val_4563_; 
v_val_4563_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_val_4563_);
lean_dec_ref_known(v___x_4561_, 1);
if (lean_obj_tag(v_val_4563_) == 1)
{
uint8_t v_v_4564_; 
v_v_4564_ = lean_ctor_get_uint8(v_val_4563_, 0);
lean_dec_ref_known(v_val_4563_, 0);
return v_v_4564_;
}
else
{
uint8_t v___x_4565_; 
lean_dec(v_val_4563_);
v___x_4565_ = lean_unbox(v_defValue_4559_);
return v___x_4565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4566_, lean_object* v_opt_4567_){
_start:
{
uint8_t v_res_4568_; lean_object* v_r_4569_; 
v_res_4568_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4566_, v_opt_4567_);
lean_dec_ref(v_opt_4567_);
lean_dec_ref(v_opts_4566_);
v_r_4569_ = lean_box(v_res_4568_);
return v_r_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4570_, lean_object* v_opt_4571_){
_start:
{
lean_object* v_name_4572_; lean_object* v_defValue_4573_; lean_object* v_map_4574_; lean_object* v___x_4575_; 
v_name_4572_ = lean_ctor_get(v_opt_4571_, 0);
v_defValue_4573_ = lean_ctor_get(v_opt_4571_, 1);
v_map_4574_ = lean_ctor_get(v_opts_4570_, 0);
v___x_4575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4574_, v_name_4572_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_inc(v_defValue_4573_);
return v_defValue_4573_;
}
else
{
lean_object* v_val_4576_; 
v_val_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_val_4576_);
lean_dec_ref_known(v___x_4575_, 1);
if (lean_obj_tag(v_val_4576_) == 3)
{
lean_object* v_v_4577_; 
v_v_4577_ = lean_ctor_get(v_val_4576_, 0);
lean_inc(v_v_4577_);
lean_dec_ref_known(v_val_4576_, 1);
return v_v_4577_;
}
else
{
lean_dec(v_val_4576_);
lean_inc(v_defValue_4573_);
return v_defValue_4573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4578_, lean_object* v_opt_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4578_, v_opt_4579_);
lean_dec_ref(v_opt_4579_);
lean_dec_ref(v_opts_4578_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4581_, size_t v_i_4582_, size_t v_stop_4583_, lean_object* v_b_4584_){
_start:
{
uint8_t v___x_4585_; 
v___x_4585_ = lean_usize_dec_eq(v_i_4582_, v_stop_4583_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; lean_object* v_key_4587_; lean_object* v_entry_4588_; lean_object* v___x_4589_; size_t v___x_4590_; size_t v___x_4591_; 
v___x_4586_ = lean_array_uget_borrowed(v_as_4581_, v_i_4582_);
v_key_4587_ = lean_ctor_get(v___x_4586_, 0);
v_entry_4588_ = lean_ctor_get(v___x_4586_, 1);
lean_inc_ref(v_entry_4588_);
lean_inc(v_key_4587_);
v___x_4589_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4584_, v_key_4587_, v_entry_4588_);
v___x_4590_ = ((size_t)1ULL);
v___x_4591_ = lean_usize_add(v_i_4582_, v___x_4590_);
v_i_4582_ = v___x_4591_;
v_b_4584_ = v___x_4589_;
goto _start;
}
else
{
return v_b_4584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4593_, lean_object* v_i_4594_, lean_object* v_stop_4595_, lean_object* v_b_4596_){
_start:
{
size_t v_i_boxed_4597_; size_t v_stop_boxed_4598_; lean_object* v_res_4599_; 
v_i_boxed_4597_ = lean_unbox_usize(v_i_4594_);
lean_dec(v_i_4594_);
v_stop_boxed_4598_ = lean_unbox_usize(v_stop_4595_);
lean_dec(v_stop_4595_);
v_res_4599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4593_, v_i_boxed_4597_, v_stop_boxed_4598_, v_b_4596_);
lean_dec_ref(v_as_4593_);
return v_res_4599_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4600_; 
v___x_4600_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4600_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4601_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
return v___x_4602_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4603_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4604_ = lean_unsigned_to_nat(0u);
v___x_4605_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
lean_ctor_set(v___x_4605_, 2, v___x_4604_);
lean_ctor_set(v___x_4605_, 3, v___x_4604_);
lean_ctor_set(v___x_4605_, 4, v___x_4603_);
lean_ctor_set(v___x_4605_, 5, v___x_4603_);
lean_ctor_set(v___x_4605_, 6, v___x_4603_);
lean_ctor_set(v___x_4605_, 7, v___x_4603_);
lean_ctor_set(v___x_4605_, 8, v___x_4603_);
lean_ctor_set(v___x_4605_, 9, v___x_4603_);
return v___x_4605_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4606_ = lean_unsigned_to_nat(32u);
v___x_4607_ = lean_mk_empty_array_with_capacity(v___x_4606_);
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
return v___x_4608_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4609_ = ((size_t)5ULL);
v___x_4610_ = lean_unsigned_to_nat(0u);
v___x_4611_ = lean_unsigned_to_nat(32u);
v___x_4612_ = lean_mk_empty_array_with_capacity(v___x_4611_);
v___x_4613_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4614_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4614_, 0, v___x_4613_);
lean_ctor_set(v___x_4614_, 1, v___x_4612_);
lean_ctor_set(v___x_4614_, 2, v___x_4610_);
lean_ctor_set(v___x_4614_, 3, v___x_4610_);
lean_ctor_set_usize(v___x_4614_, 4, v___x_4609_);
return v___x_4614_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
lean_ctor_set(v___x_4616_, 2, v___x_4615_);
lean_ctor_set(v___x_4616_, 3, v___x_4615_);
lean_ctor_set(v___x_4616_, 4, v___x_4615_);
return v___x_4616_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4617_ = lean_box(1);
v___x_4618_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4619_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
lean_ctor_set(v___x_4620_, 1, v___x_4618_);
lean_ctor_set(v___x_4620_, 2, v___x_4617_);
return v___x_4620_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4623_ = lean_unsigned_to_nat(1u);
v___x_4624_ = l_Lean_firstFrontendMacroScope;
v___x_4625_ = lean_nat_add(v___x_4624_, v___x_4623_);
return v___x_4625_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4630_; uint64_t v___x_4631_; lean_object* v___x_4632_; 
v___x_4630_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4631_ = 0ULL;
v___x_4632_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4632_, 0, v___x_4630_);
lean_ctor_set_uint64(v___x_4632_, sizeof(void*)*1, v___x_4631_);
return v___x_4632_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4633_ = l_Lean_NameSet_empty;
v___x_4634_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
lean_ctor_set(v___x_4635_, 2, v___x_4633_);
return v___x_4635_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; lean_object* v___x_4639_; 
v___x_4636_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4637_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4638_ = 1;
v___x_4639_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4639_, 0, v___x_4637_);
lean_ctor_set(v___x_4639_, 1, v___x_4637_);
lean_ctor_set(v___x_4639_, 2, v___x_4636_);
lean_ctor_set_uint8(v___x_4639_, sizeof(void*)*3, v___x_4638_);
return v___x_4639_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4640_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4640_);
lean_ctor_set(v___x_4641_, 1, v___x_4640_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4642_, lean_object* v_env_4643_, lean_object* v_modName_4644_, lean_object* v_d_4645_, lean_object* v_cacheRef_4646_, lean_object* v_tree_4647_, lean_object* v_act_4648_, lean_object* v_c_4649_){
_start:
{
uint8_t v___x_4651_; 
lean_inc_ref(v_c_4649_);
v___x_4651_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4649_);
if (v___x_4651_ == 0)
{
lean_object* v_name_4652_; uint8_t v___x_4653_; 
v_name_4652_ = lean_ctor_get(v_c_4649_, 0);
lean_inc_n(v_name_4652_, 2);
lean_inc_ref(v_env_4643_);
v___x_4653_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4643_, v_name_4652_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; lean_object* v_ngen_4655_; lean_object* v_core_4656_; lean_object* v_meta_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4791_; 
v___x_4654_ = lean_st_ref_get(v_cacheRef_4646_);
v_ngen_4655_ = lean_ctor_get(v___x_4654_, 0);
v_core_4656_ = lean_ctor_get(v___x_4654_, 1);
v_meta_4657_ = lean_ctor_get(v___x_4654_, 2);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4659_ = v___x_4654_;
v_isShared_4660_ = v_isSharedCheck_4791_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_meta_4657_);
lean_inc(v_core_4656_);
lean_inc(v_ngen_4655_);
lean_dec(v___x_4654_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4791_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; uint8_t v___x_4671_; uint8_t v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v_fileName_4689_; lean_object* v_fileMap_4690_; lean_object* v_options_4691_; lean_object* v_currRecDepth_4692_; lean_object* v_maxRecDepth_4693_; lean_object* v_ref_4694_; lean_object* v_currNamespace_4695_; lean_object* v_openDecls_4696_; lean_object* v_initHeartbeats_4697_; lean_object* v_maxHeartbeats_4698_; lean_object* v_quotContext_4699_; lean_object* v_currMacroScope_4700_; uint8_t v_diag_4701_; lean_object* v_cancelTk_x3f_4702_; uint8_t v_suppressElabErrors_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4789_; 
v___x_4661_ = lean_unsigned_to_nat(0u);
v___x_4662_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4663_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4664_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4655_);
v___x_4665_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4655_);
v___x_4666_ = lean_st_ref_set(v_cacheRef_4646_, v___x_4665_);
v___x_4667_ = lean_box(1);
v___x_4668_ = 1;
v___x_4669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4662_);
lean_ctor_set(v___x_4669_, 1, v_meta_4657_);
lean_ctor_set(v___x_4669_, 2, v___x_4667_);
lean_ctor_set(v___x_4669_, 3, v___x_4663_);
lean_ctor_set(v___x_4669_, 4, v___x_4664_);
v___x_4670_ = 2;
v___x_4671_ = 0;
v___x_4672_ = 2;
v___x_4673_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4673_, 0, v___x_4653_);
lean_ctor_set_uint8(v___x_4673_, 1, v___x_4653_);
lean_ctor_set_uint8(v___x_4673_, 2, v___x_4653_);
lean_ctor_set_uint8(v___x_4673_, 3, v___x_4653_);
lean_ctor_set_uint8(v___x_4673_, 4, v___x_4653_);
lean_ctor_set_uint8(v___x_4673_, 5, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 6, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 7, v___x_4653_);
lean_ctor_set_uint8(v___x_4673_, 8, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 9, v___x_4670_);
lean_ctor_set_uint8(v___x_4673_, 10, v___x_4671_);
lean_ctor_set_uint8(v___x_4673_, 11, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 12, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 13, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 14, v___x_4672_);
lean_ctor_set_uint8(v___x_4673_, 15, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 16, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 17, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 18, v___x_4668_);
lean_ctor_set_uint8(v___x_4673_, 19, v___x_4653_);
v___x_4674_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4673_);
v___x_4675_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4676_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4678_, 0, v___x_4674_);
lean_ctor_set(v___x_4678_, 1, v___x_4667_);
lean_ctor_set(v___x_4678_, 2, v___x_4675_);
lean_ctor_set(v___x_4678_, 3, v___x_4676_);
lean_ctor_set(v___x_4678_, 4, v___x_4677_);
lean_ctor_set(v___x_4678_, 5, v___x_4661_);
lean_ctor_set(v___x_4678_, 6, v___x_4677_);
lean_ctor_set_uint8(v___x_4678_, sizeof(void*)*7, v___x_4653_);
lean_ctor_set_uint8(v___x_4678_, sizeof(void*)*7 + 1, v___x_4653_);
lean_ctor_set_uint8(v___x_4678_, sizeof(void*)*7 + 2, v___x_4653_);
lean_ctor_set_uint8(v___x_4678_, sizeof(void*)*7 + 3, v___x_4668_);
v___x_4679_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4680_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4681_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4682_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4683_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4684_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4684_, 0, v_env_4643_);
lean_ctor_set(v___x_4684_, 1, v___x_4679_);
lean_ctor_set(v___x_4684_, 2, v_ngen_4655_);
lean_ctor_set(v___x_4684_, 3, v___x_4680_);
lean_ctor_set(v___x_4684_, 4, v___x_4681_);
lean_ctor_set(v___x_4684_, 5, v_core_4656_);
lean_ctor_set(v___x_4684_, 6, v___x_4682_);
lean_ctor_set(v___x_4684_, 7, v___x_4683_);
lean_ctor_set(v___x_4684_, 8, v___x_4676_);
v___x_4685_ = lean_st_mk_ref(v___x_4684_);
v___x_4686_ = l_Lean_inheritedTraceOptions;
v___x_4687_ = lean_st_ref_get(v___x_4686_);
v___x_4688_ = lean_st_ref_get(v___x_4685_);
v_fileName_4689_ = lean_ctor_get(v_cctx_4642_, 0);
v_fileMap_4690_ = lean_ctor_get(v_cctx_4642_, 1);
v_options_4691_ = lean_ctor_get(v_cctx_4642_, 2);
v_currRecDepth_4692_ = lean_ctor_get(v_cctx_4642_, 3);
v_maxRecDepth_4693_ = lean_ctor_get(v_cctx_4642_, 4);
v_ref_4694_ = lean_ctor_get(v_cctx_4642_, 5);
v_currNamespace_4695_ = lean_ctor_get(v_cctx_4642_, 6);
v_openDecls_4696_ = lean_ctor_get(v_cctx_4642_, 7);
v_initHeartbeats_4697_ = lean_ctor_get(v_cctx_4642_, 8);
v_maxHeartbeats_4698_ = lean_ctor_get(v_cctx_4642_, 9);
v_quotContext_4699_ = lean_ctor_get(v_cctx_4642_, 10);
v_currMacroScope_4700_ = lean_ctor_get(v_cctx_4642_, 11);
v_diag_4701_ = lean_ctor_get_uint8(v_cctx_4642_, sizeof(void*)*14);
v_cancelTk_x3f_4702_ = lean_ctor_get(v_cctx_4642_, 12);
v_suppressElabErrors_4703_ = lean_ctor_get_uint8(v_cctx_4642_, sizeof(void*)*14 + 1);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_cctx_4642_);
if (v_isSharedCheck_4789_ == 0)
{
lean_object* v_unused_4790_; 
v_unused_4790_ = lean_ctor_get(v_cctx_4642_, 13);
lean_dec(v_unused_4790_);
v___x_4705_ = v_cctx_4642_;
v_isShared_4706_ = v_isSharedCheck_4789_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_cancelTk_x3f_4702_);
lean_inc(v_currMacroScope_4700_);
lean_inc(v_quotContext_4699_);
lean_inc(v_maxHeartbeats_4698_);
lean_inc(v_initHeartbeats_4697_);
lean_inc(v_openDecls_4696_);
lean_inc(v_currNamespace_4695_);
lean_inc(v_ref_4694_);
lean_inc(v_maxRecDepth_4693_);
lean_inc(v_currRecDepth_4692_);
lean_inc(v_options_4691_);
lean_inc(v_fileMap_4690_);
lean_inc(v_fileName_4689_);
lean_dec(v_cctx_4642_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4789_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v_env_4707_; lean_object* v___x_4709_; 
v_env_4707_ = lean_ctor_get(v___x_4688_, 0);
lean_inc_ref(v_env_4707_);
lean_dec(v___x_4688_);
lean_inc_ref(v_options_4691_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 13, v___x_4687_);
v___x_4709_ = v___x_4705_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_fileName_4689_);
lean_ctor_set(v_reuseFailAlloc_4788_, 1, v_fileMap_4690_);
lean_ctor_set(v_reuseFailAlloc_4788_, 2, v_options_4691_);
lean_ctor_set(v_reuseFailAlloc_4788_, 3, v_currRecDepth_4692_);
lean_ctor_set(v_reuseFailAlloc_4788_, 4, v_maxRecDepth_4693_);
lean_ctor_set(v_reuseFailAlloc_4788_, 5, v_ref_4694_);
lean_ctor_set(v_reuseFailAlloc_4788_, 6, v_currNamespace_4695_);
lean_ctor_set(v_reuseFailAlloc_4788_, 7, v_openDecls_4696_);
lean_ctor_set(v_reuseFailAlloc_4788_, 8, v_initHeartbeats_4697_);
lean_ctor_set(v_reuseFailAlloc_4788_, 9, v_maxHeartbeats_4698_);
lean_ctor_set(v_reuseFailAlloc_4788_, 10, v_quotContext_4699_);
lean_ctor_set(v_reuseFailAlloc_4788_, 11, v_currMacroScope_4700_);
lean_ctor_set(v_reuseFailAlloc_4788_, 12, v_cancelTk_x3f_4702_);
lean_ctor_set(v_reuseFailAlloc_4788_, 13, v___x_4687_);
lean_ctor_set_uint8(v_reuseFailAlloc_4788_, sizeof(void*)*14, v_diag_4701_);
lean_ctor_set_uint8(v_reuseFailAlloc_4788_, sizeof(void*)*14 + 1, v_suppressElabErrors_4703_);
v___x_4709_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
lean_object* v___x_4710_; uint8_t v___x_4711_; lean_object* v___y_4713_; lean_object* v___y_4714_; uint8_t v___y_4766_; uint8_t v___x_4787_; 
v___x_4710_ = l_Lean_diagnostics;
v___x_4711_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4691_, v___x_4710_);
v___x_4787_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4707_);
lean_dec_ref(v_env_4707_);
if (v___x_4787_ == 0)
{
if (v___x_4711_ == 0)
{
lean_inc(v___x_4685_);
v___y_4713_ = v___x_4709_;
v___y_4714_ = v___x_4685_;
goto v___jp_4712_;
}
else
{
v___y_4766_ = v___x_4787_;
goto v___jp_4765_;
}
}
else
{
v___y_4766_ = v___x_4711_;
goto v___jp_4765_;
}
v___jp_4712_:
{
lean_object* v___x_4715_; lean_object* v_fileName_4716_; lean_object* v_fileMap_4717_; lean_object* v_currRecDepth_4718_; lean_object* v_ref_4719_; lean_object* v_currNamespace_4720_; lean_object* v_openDecls_4721_; lean_object* v_initHeartbeats_4722_; lean_object* v_maxHeartbeats_4723_; lean_object* v_quotContext_4724_; lean_object* v_currMacroScope_4725_; lean_object* v_cancelTk_x3f_4726_; uint8_t v_suppressElabErrors_4727_; lean_object* v_inheritedTraceOptions_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4762_; 
v___x_4715_ = lean_st_mk_ref(v___x_4669_);
v_fileName_4716_ = lean_ctor_get(v___y_4713_, 0);
v_fileMap_4717_ = lean_ctor_get(v___y_4713_, 1);
v_currRecDepth_4718_ = lean_ctor_get(v___y_4713_, 3);
v_ref_4719_ = lean_ctor_get(v___y_4713_, 5);
v_currNamespace_4720_ = lean_ctor_get(v___y_4713_, 6);
v_openDecls_4721_ = lean_ctor_get(v___y_4713_, 7);
v_initHeartbeats_4722_ = lean_ctor_get(v___y_4713_, 8);
v_maxHeartbeats_4723_ = lean_ctor_get(v___y_4713_, 9);
v_quotContext_4724_ = lean_ctor_get(v___y_4713_, 10);
v_currMacroScope_4725_ = lean_ctor_get(v___y_4713_, 11);
v_cancelTk_x3f_4726_ = lean_ctor_get(v___y_4713_, 12);
v_suppressElabErrors_4727_ = lean_ctor_get_uint8(v___y_4713_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4728_ = lean_ctor_get(v___y_4713_, 13);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___y_4713_);
if (v_isSharedCheck_4762_ == 0)
{
lean_object* v_unused_4763_; lean_object* v_unused_4764_; 
v_unused_4763_ = lean_ctor_get(v___y_4713_, 4);
lean_dec(v_unused_4763_);
v_unused_4764_ = lean_ctor_get(v___y_4713_, 2);
lean_dec(v_unused_4764_);
v___x_4730_ = v___y_4713_;
v_isShared_4731_ = v_isSharedCheck_4762_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_inheritedTraceOptions_4728_);
lean_inc(v_cancelTk_x3f_4726_);
lean_inc(v_currMacroScope_4725_);
lean_inc(v_quotContext_4724_);
lean_inc(v_maxHeartbeats_4723_);
lean_inc(v_initHeartbeats_4722_);
lean_inc(v_openDecls_4721_);
lean_inc(v_currNamespace_4720_);
lean_inc(v_ref_4719_);
lean_inc(v_currRecDepth_4718_);
lean_inc(v_fileMap_4717_);
lean_inc(v_fileName_4716_);
lean_dec(v___y_4713_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4762_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4735_; 
v___x_4732_ = l_Lean_maxRecDepth;
v___x_4733_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4691_, v___x_4732_);
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 4, v___x_4733_);
lean_ctor_set(v___x_4730_, 2, v_options_4691_);
v___x_4735_ = v___x_4730_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_fileName_4716_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v_fileMap_4717_);
lean_ctor_set(v_reuseFailAlloc_4761_, 2, v_options_4691_);
lean_ctor_set(v_reuseFailAlloc_4761_, 3, v_currRecDepth_4718_);
lean_ctor_set(v_reuseFailAlloc_4761_, 4, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4761_, 5, v_ref_4719_);
lean_ctor_set(v_reuseFailAlloc_4761_, 6, v_currNamespace_4720_);
lean_ctor_set(v_reuseFailAlloc_4761_, 7, v_openDecls_4721_);
lean_ctor_set(v_reuseFailAlloc_4761_, 8, v_initHeartbeats_4722_);
lean_ctor_set(v_reuseFailAlloc_4761_, 9, v_maxHeartbeats_4723_);
lean_ctor_set(v_reuseFailAlloc_4761_, 10, v_quotContext_4724_);
lean_ctor_set(v_reuseFailAlloc_4761_, 11, v_currMacroScope_4725_);
lean_ctor_set(v_reuseFailAlloc_4761_, 12, v_cancelTk_x3f_4726_);
lean_ctor_set(v_reuseFailAlloc_4761_, 13, v_inheritedTraceOptions_4728_);
lean_ctor_set_uint8(v_reuseFailAlloc_4761_, sizeof(void*)*14 + 1, v_suppressElabErrors_4727_);
v___x_4735_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_object* v___x_4736_; 
lean_ctor_set_uint8(v___x_4735_, sizeof(void*)*14, v___x_4711_);
lean_inc(v___x_4715_);
lean_inc(v_name_4652_);
v___x_4736_ = lean_apply_7(v_act_4648_, v_name_4652_, v_c_4649_, v___x_4678_, v___x_4715_, v___x_4735_, v___y_4714_, lean_box(0));
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v_ngen_4740_; lean_object* v_cache_4741_; lean_object* v_cache_4742_; lean_object* v___x_4744_; 
lean_dec(v_name_4652_);
lean_dec(v_modName_4644_);
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v___x_4736_, 1);
v___x_4738_ = lean_st_ref_get(v___x_4715_);
lean_dec(v___x_4715_);
v___x_4739_ = lean_st_ref_get(v___x_4685_);
lean_dec(v___x_4685_);
v_ngen_4740_ = lean_ctor_get(v___x_4739_, 2);
lean_inc_ref(v_ngen_4740_);
v_cache_4741_ = lean_ctor_get(v___x_4739_, 5);
lean_inc_ref(v_cache_4741_);
lean_dec(v___x_4739_);
v_cache_4742_ = lean_ctor_get(v___x_4738_, 1);
lean_inc_ref(v_cache_4742_);
lean_dec(v___x_4738_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 2, v_cache_4742_);
lean_ctor_set(v___x_4659_, 1, v_cache_4741_);
lean_ctor_set(v___x_4659_, 0, v_ngen_4740_);
v___x_4744_ = v___x_4659_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_ngen_4740_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_cache_4741_);
lean_ctor_set(v_reuseFailAlloc_4755_, 2, v_cache_4742_);
v___x_4744_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v___x_4745_ = lean_st_ref_set(v_cacheRef_4646_, v___x_4744_);
v___x_4746_ = lean_array_get_size(v_a_4737_);
v___x_4747_ = lean_nat_dec_lt(v___x_4661_, v___x_4746_);
if (v___x_4747_ == 0)
{
lean_dec(v_a_4737_);
return v_tree_4647_;
}
else
{
uint8_t v___x_4748_; 
v___x_4748_ = lean_nat_dec_le(v___x_4746_, v___x_4746_);
if (v___x_4748_ == 0)
{
if (v___x_4747_ == 0)
{
lean_dec(v_a_4737_);
return v_tree_4647_;
}
else
{
size_t v___x_4749_; size_t v___x_4750_; lean_object* v___x_4751_; 
v___x_4749_ = ((size_t)0ULL);
v___x_4750_ = lean_usize_of_nat(v___x_4746_);
v___x_4751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4737_, v___x_4749_, v___x_4750_, v_tree_4647_);
lean_dec(v_a_4737_);
return v___x_4751_;
}
}
else
{
size_t v___x_4752_; size_t v___x_4753_; lean_object* v___x_4754_; 
v___x_4752_ = ((size_t)0ULL);
v___x_4753_ = lean_usize_of_nat(v___x_4746_);
v___x_4754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4737_, v___x_4752_, v___x_4753_, v_tree_4647_);
lean_dec(v_a_4737_);
return v___x_4754_;
}
}
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
lean_dec(v___x_4715_);
lean_dec(v___x_4685_);
lean_del_object(v___x_4659_);
v_a_4756_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4756_);
lean_dec_ref_known(v___x_4736_, 1);
v___x_4757_ = lean_st_ref_take(v_d_4645_);
v___x_4758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4758_, 0, v_modName_4644_);
lean_ctor_set(v___x_4758_, 1, v_name_4652_);
lean_ctor_set(v___x_4758_, 2, v_a_4756_);
v___x_4759_ = lean_array_push(v___x_4757_, v___x_4758_);
v___x_4760_ = lean_st_ref_set(v_d_4645_, v___x_4759_);
return v_tree_4647_;
}
}
}
}
v___jp_4765_:
{
if (v___y_4766_ == 0)
{
lean_object* v___x_4767_; lean_object* v_env_4768_; lean_object* v_nextMacroScope_4769_; lean_object* v_ngen_4770_; lean_object* v_auxDeclNGen_4771_; lean_object* v_traceState_4772_; lean_object* v_messages_4773_; lean_object* v_infoState_4774_; lean_object* v_snapshotTasks_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4785_; 
v___x_4767_ = lean_st_ref_take(v___x_4685_);
v_env_4768_ = lean_ctor_get(v___x_4767_, 0);
v_nextMacroScope_4769_ = lean_ctor_get(v___x_4767_, 1);
v_ngen_4770_ = lean_ctor_get(v___x_4767_, 2);
v_auxDeclNGen_4771_ = lean_ctor_get(v___x_4767_, 3);
v_traceState_4772_ = lean_ctor_get(v___x_4767_, 4);
v_messages_4773_ = lean_ctor_get(v___x_4767_, 6);
v_infoState_4774_ = lean_ctor_get(v___x_4767_, 7);
v_snapshotTasks_4775_ = lean_ctor_get(v___x_4767_, 8);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4767_);
if (v_isSharedCheck_4785_ == 0)
{
lean_object* v_unused_4786_; 
v_unused_4786_ = lean_ctor_get(v___x_4767_, 5);
lean_dec(v_unused_4786_);
v___x_4777_ = v___x_4767_;
v_isShared_4778_ = v_isSharedCheck_4785_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_snapshotTasks_4775_);
lean_inc(v_infoState_4774_);
lean_inc(v_messages_4773_);
lean_inc(v_traceState_4772_);
lean_inc(v_auxDeclNGen_4771_);
lean_inc(v_ngen_4770_);
lean_inc(v_nextMacroScope_4769_);
lean_inc(v_env_4768_);
lean_dec(v___x_4767_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4785_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4782_; 
v___x_4779_ = l_Lean_Kernel_enableDiag(v_env_4768_, v___x_4711_);
v___x_4780_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 5, v___x_4780_);
lean_ctor_set(v___x_4777_, 0, v___x_4779_);
v___x_4782_ = v___x_4777_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4784_, 1, v_nextMacroScope_4769_);
lean_ctor_set(v_reuseFailAlloc_4784_, 2, v_ngen_4770_);
lean_ctor_set(v_reuseFailAlloc_4784_, 3, v_auxDeclNGen_4771_);
lean_ctor_set(v_reuseFailAlloc_4784_, 4, v_traceState_4772_);
lean_ctor_set(v_reuseFailAlloc_4784_, 5, v___x_4780_);
lean_ctor_set(v_reuseFailAlloc_4784_, 6, v_messages_4773_);
lean_ctor_set(v_reuseFailAlloc_4784_, 7, v_infoState_4774_);
lean_ctor_set(v_reuseFailAlloc_4784_, 8, v_snapshotTasks_4775_);
v___x_4782_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_st_ref_set(v___x_4685_, v___x_4782_);
lean_inc(v___x_4685_);
v___y_4713_ = v___x_4709_;
v___y_4714_ = v___x_4685_;
goto v___jp_4712_;
}
}
}
else
{
lean_inc(v___x_4685_);
v___y_4713_ = v___x_4709_;
v___y_4714_ = v___x_4685_;
goto v___jp_4712_;
}
}
}
}
}
}
else
{
lean_dec(v_name_4652_);
lean_dec_ref(v_c_4649_);
lean_dec_ref(v_act_4648_);
lean_dec(v_modName_4644_);
lean_dec_ref(v_env_4643_);
lean_dec_ref(v_cctx_4642_);
return v_tree_4647_;
}
}
else
{
lean_dec_ref(v_c_4649_);
lean_dec_ref(v_act_4648_);
lean_dec(v_modName_4644_);
lean_dec_ref(v_env_4643_);
lean_dec_ref(v_cctx_4642_);
return v_tree_4647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4792_, lean_object* v_env_4793_, lean_object* v_modName_4794_, lean_object* v_d_4795_, lean_object* v_cacheRef_4796_, lean_object* v_tree_4797_, lean_object* v_act_4798_, lean_object* v_c_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4792_, v_env_4793_, v_modName_4794_, v_d_4795_, v_cacheRef_4796_, v_tree_4797_, v_act_4798_, v_c_4799_);
lean_dec(v_cacheRef_4796_);
lean_dec(v_d_4795_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4802_, lean_object* v_cctx_4803_, lean_object* v_env_4804_, lean_object* v_modName_4805_, lean_object* v_d_4806_, lean_object* v_cacheRef_4807_, lean_object* v_tree_4808_, lean_object* v_act_4809_, lean_object* v_c_4810_){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4803_, v_env_4804_, v_modName_4805_, v_d_4806_, v_cacheRef_4807_, v_tree_4808_, v_act_4809_, v_c_4810_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4813_, lean_object* v_cctx_4814_, lean_object* v_env_4815_, lean_object* v_modName_4816_, lean_object* v_d_4817_, lean_object* v_cacheRef_4818_, lean_object* v_tree_4819_, lean_object* v_act_4820_, lean_object* v_c_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4813_, v_cctx_4814_, v_env_4815_, v_modName_4816_, v_d_4817_, v_cacheRef_4818_, v_tree_4819_, v_act_4820_, v_c_4821_);
lean_dec(v_cacheRef_4818_);
lean_dec(v_d_4817_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4824_, lean_object* v_as_4825_, size_t v_i_4826_, size_t v_stop_4827_, lean_object* v_b_4828_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4825_, v_i_4826_, v_stop_4827_, v_b_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4830_, lean_object* v_as_4831_, lean_object* v_i_4832_, lean_object* v_stop_4833_, lean_object* v_b_4834_){
_start:
{
size_t v_i_boxed_4835_; size_t v_stop_boxed_4836_; lean_object* v_res_4837_; 
v_i_boxed_4835_ = lean_unbox_usize(v_i_4832_);
lean_dec(v_i_4832_);
v_stop_boxed_4836_ = lean_unbox_usize(v_stop_4833_);
lean_dec(v_stop_4833_);
v_res_4837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4830_, v_as_4831_, v_i_boxed_4835_, v_stop_boxed_4836_, v_b_4834_);
lean_dec_ref(v_as_4831_);
return v_res_4837_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4839_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_4840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
lean_ctor_set(v___x_4840_, 1, v___x_4838_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4841_){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4843_, lean_object* v_y_4844_){
_start:
{
lean_object* v_tree_4845_; lean_object* v_errors_4846_; lean_object* v_tree_4847_; lean_object* v_errors_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4857_; 
v_tree_4845_ = lean_ctor_get(v_x_4843_, 0);
lean_inc_ref(v_tree_4845_);
v_errors_4846_ = lean_ctor_get(v_x_4843_, 1);
lean_inc_ref(v_errors_4846_);
lean_dec_ref(v_x_4843_);
v_tree_4847_ = lean_ctor_get(v_y_4844_, 0);
v_errors_4848_ = lean_ctor_get(v_y_4844_, 1);
v_isSharedCheck_4857_ = !lean_is_exclusive(v_y_4844_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4850_ = v_y_4844_;
v_isShared_4851_ = v_isSharedCheck_4857_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_errors_4848_);
lean_inc(v_tree_4847_);
lean_dec(v_y_4844_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4857_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4855_; 
v___x_4852_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4845_, v_tree_4847_);
v___x_4853_ = l_Array_append___redArg(v_errors_4846_, v_errors_4848_);
lean_dec_ref(v_errors_4848_);
if (v_isShared_4851_ == 0)
{
lean_ctor_set(v___x_4850_, 1, v___x_4853_);
lean_ctor_set(v___x_4850_, 0, v___x_4852_);
v___x_4855_ = v___x_4850_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4852_);
lean_ctor_set(v_reuseFailAlloc_4856_, 1, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4858_, lean_object* v_x_4859_, lean_object* v_y_4860_){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4859_, v_y_4860_);
return v___x_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4863_){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4865_, lean_object* v_tree_4866_){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4868_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4869_ = lean_st_ref_swap(v_d_4865_, v___x_4868_);
v___x_4870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4870_, 0, v_tree_4866_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4871_, lean_object* v_tree_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4871_, v_tree_4872_);
lean_dec(v_d_4871_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4875_, lean_object* v_d_4876_, lean_object* v_tree_4877_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4876_, v_tree_4877_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4880_, lean_object* v_d_4881_, lean_object* v_tree_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4880_, v_d_4881_, v_tree_4882_);
lean_dec(v_d_4881_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4885_, lean_object* v_env_4886_, lean_object* v_act_4887_, lean_object* v_d_4888_, lean_object* v_cacheRef_4889_, lean_object* v_tree_4890_, lean_object* v_mname_4891_, lean_object* v_mdata_4892_, lean_object* v_i_4893_){
_start:
{
lean_object* v_constants_4895_; lean_object* v___x_4896_; uint8_t v___x_4897_; 
v_constants_4895_ = lean_ctor_get(v_mdata_4892_, 2);
v___x_4896_ = lean_array_get_size(v_constants_4895_);
v___x_4897_ = lean_nat_dec_lt(v_i_4893_, v___x_4896_);
if (v___x_4897_ == 0)
{
lean_dec(v_i_4893_);
lean_dec(v_mname_4891_);
lean_dec_ref(v_act_4887_);
lean_dec_ref(v_env_4886_);
lean_dec_ref(v_cctx_4885_);
return v_tree_4890_;
}
else
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4898_ = lean_array_fget_borrowed(v_constants_4895_, v_i_4893_);
lean_inc(v___x_4898_);
v___x_4899_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4898_);
lean_inc_ref(v_act_4887_);
lean_inc(v_mname_4891_);
lean_inc_ref(v_env_4886_);
lean_inc_ref(v_cctx_4885_);
v___x_4900_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4885_, v_env_4886_, v_mname_4891_, v_d_4888_, v_cacheRef_4889_, v_tree_4890_, v_act_4887_, v___x_4899_);
v___x_4901_ = lean_unsigned_to_nat(1u);
v___x_4902_ = lean_nat_add(v_i_4893_, v___x_4901_);
lean_dec(v_i_4893_);
v_tree_4890_ = v___x_4900_;
v_i_4893_ = v___x_4902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4904_, lean_object* v_env_4905_, lean_object* v_act_4906_, lean_object* v_d_4907_, lean_object* v_cacheRef_4908_, lean_object* v_tree_4909_, lean_object* v_mname_4910_, lean_object* v_mdata_4911_, lean_object* v_i_4912_, lean_object* v_a_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4904_, v_env_4905_, v_act_4906_, v_d_4907_, v_cacheRef_4908_, v_tree_4909_, v_mname_4910_, v_mdata_4911_, v_i_4912_);
lean_dec_ref(v_mdata_4911_);
lean_dec(v_cacheRef_4908_);
lean_dec(v_d_4907_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4915_, lean_object* v_cctx_4916_, lean_object* v_env_4917_, lean_object* v_act_4918_, lean_object* v_d_4919_, lean_object* v_cacheRef_4920_, lean_object* v_tree_4921_, lean_object* v_mname_4922_, lean_object* v_mdata_4923_, lean_object* v_i_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4916_, v_env_4917_, v_act_4918_, v_d_4919_, v_cacheRef_4920_, v_tree_4921_, v_mname_4922_, v_mdata_4923_, v_i_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4927_, lean_object* v_cctx_4928_, lean_object* v_env_4929_, lean_object* v_act_4930_, lean_object* v_d_4931_, lean_object* v_cacheRef_4932_, lean_object* v_tree_4933_, lean_object* v_mname_4934_, lean_object* v_mdata_4935_, lean_object* v_i_4936_, lean_object* v_a_4937_){
_start:
{
lean_object* v_res_4938_; 
v_res_4938_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4927_, v_cctx_4928_, v_env_4929_, v_act_4930_, v_d_4931_, v_cacheRef_4932_, v_tree_4933_, v_mname_4934_, v_mdata_4935_, v_i_4936_);
lean_dec_ref(v_mdata_4935_);
lean_dec(v_cacheRef_4932_);
lean_dec(v_d_4931_);
return v_res_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4939_, lean_object* v_env_4940_, lean_object* v_act_4941_, lean_object* v_d_4942_, lean_object* v_cacheRef_4943_, lean_object* v_tree_4944_, lean_object* v_start_4945_, lean_object* v_stop_4946_){
_start:
{
uint8_t v___x_4948_; 
v___x_4948_ = lean_nat_dec_lt(v_start_4945_, v_stop_4946_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; 
lean_dec(v_start_4945_);
lean_dec_ref(v_act_4941_);
lean_dec_ref(v_env_4940_);
lean_dec_ref(v_cctx_4939_);
v___x_4949_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4942_, v_tree_4944_);
return v___x_4949_;
}
else
{
lean_object* v___x_4950_; lean_object* v_moduleData_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v_mname_4954_; lean_object* v___x_4955_; lean_object* v_mdata_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4950_ = l_Lean_Environment_header(v_env_4940_);
v_moduleData_4951_ = lean_ctor_get(v___x_4950_, 6);
lean_inc_ref(v_moduleData_4951_);
v___x_4952_ = lean_box(0);
v___x_4953_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4950_);
v_mname_4954_ = lean_array_get(v___x_4952_, v___x_4953_, v_start_4945_);
lean_dec_ref(v___x_4953_);
v___x_4955_ = l_Lean_instInhabitedModuleData_default;
v_mdata_4956_ = lean_array_get(v___x_4955_, v_moduleData_4951_, v_start_4945_);
lean_dec_ref(v_moduleData_4951_);
v___x_4957_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4941_);
lean_inc_ref(v_env_4940_);
lean_inc_ref(v_cctx_4939_);
v___x_4958_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4939_, v_env_4940_, v_act_4941_, v_d_4942_, v_cacheRef_4943_, v_tree_4944_, v_mname_4954_, v_mdata_4956_, v___x_4957_);
lean_dec(v_mdata_4956_);
v___x_4959_ = lean_unsigned_to_nat(1u);
v___x_4960_ = lean_nat_add(v_start_4945_, v___x_4959_);
lean_dec(v_start_4945_);
v_tree_4944_ = v___x_4958_;
v_start_4945_ = v___x_4960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4962_, lean_object* v_env_4963_, lean_object* v_act_4964_, lean_object* v_d_4965_, lean_object* v_cacheRef_4966_, lean_object* v_tree_4967_, lean_object* v_start_4968_, lean_object* v_stop_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4962_, v_env_4963_, v_act_4964_, v_d_4965_, v_cacheRef_4966_, v_tree_4967_, v_start_4968_, v_stop_4969_);
lean_dec(v_stop_4969_);
lean_dec(v_cacheRef_4966_);
lean_dec(v_d_4965_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_4972_, lean_object* v_cctx_4973_, lean_object* v_env_4974_, lean_object* v_act_4975_, lean_object* v_d_4976_, lean_object* v_cacheRef_4977_, lean_object* v_tree_4978_, lean_object* v_start_4979_, lean_object* v_stop_4980_){
_start:
{
lean_object* v___x_4982_; 
v___x_4982_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4973_, v_env_4974_, v_act_4975_, v_d_4976_, v_cacheRef_4977_, v_tree_4978_, v_start_4979_, v_stop_4980_);
return v___x_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_4983_, lean_object* v_cctx_4984_, lean_object* v_env_4985_, lean_object* v_act_4986_, lean_object* v_d_4987_, lean_object* v_cacheRef_4988_, lean_object* v_tree_4989_, lean_object* v_start_4990_, lean_object* v_stop_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_4983_, v_cctx_4984_, v_env_4985_, v_act_4986_, v_d_4987_, v_cacheRef_4988_, v_tree_4989_, v_start_4990_, v_stop_4991_);
lean_dec(v_stop_4991_);
lean_dec(v_cacheRef_4988_);
lean_dec(v_d_4987_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_4994_, lean_object* v_ngen_4995_, lean_object* v_env_4996_, lean_object* v_act_4997_, lean_object* v_start_4998_, lean_object* v_stop_4999_){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5001_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4995_);
v___x_5002_ = lean_st_mk_ref(v___x_5001_);
v___x_5003_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5004_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_5005_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4994_, v_env_4996_, v_act_4997_, v___x_5003_, v___x_5002_, v___x_5004_, v_start_4998_, v_stop_4999_);
lean_dec(v___x_5002_);
lean_dec(v___x_5003_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5006_, lean_object* v_ngen_5007_, lean_object* v_env_5008_, lean_object* v_act_5009_, lean_object* v_start_5010_, lean_object* v_stop_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5006_, v_ngen_5007_, v_env_5008_, v_act_5009_, v_start_5010_, v_stop_5011_);
lean_dec(v_stop_5011_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5014_, lean_object* v_cctx_5015_, lean_object* v_ngen_5016_, lean_object* v_env_5017_, lean_object* v_act_5018_, lean_object* v_start_5019_, lean_object* v_stop_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5015_, v_ngen_5016_, v_env_5017_, v_act_5018_, v_start_5019_, v_stop_5020_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5023_, lean_object* v_cctx_5024_, lean_object* v_ngen_5025_, lean_object* v_env_5026_, lean_object* v_act_5027_, lean_object* v_start_5028_, lean_object* v_stop_5029_, lean_object* v_a_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5023_, v_cctx_5024_, v_ngen_5025_, v_env_5026_, v_act_5027_, v_start_5028_, v_stop_5029_);
lean_dec(v_stop_5029_);
return v_res_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5032_, lean_object* v_x1_5033_, lean_object* v_x2_5034_){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5035_ = lean_task_get_own(v_x2_5034_);
v___x_5036_ = lean_apply_2(v_inst_5032_, v_x1_5033_, v___x_5035_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5037_, lean_object* v_z_5038_, lean_object* v_tasks_5039_){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; 
v___x_5040_ = lean_unsigned_to_nat(0u);
v___x_5041_ = lean_array_get_size(v_tasks_5039_);
v___x_5042_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5043_ = lean_nat_dec_lt(v___x_5040_, v___x_5041_);
if (v___x_5043_ == 0)
{
lean_dec_ref(v_tasks_5039_);
lean_dec(v_inst_5037_);
return v_z_5038_;
}
else
{
lean_object* v___f_5044_; uint8_t v___x_5045_; 
v___f_5044_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5044_, 0, v_inst_5037_);
v___x_5045_ = lean_nat_dec_le(v___x_5041_, v___x_5041_);
if (v___x_5045_ == 0)
{
if (v___x_5043_ == 0)
{
lean_dec_ref(v___f_5044_);
lean_dec_ref(v_tasks_5039_);
return v_z_5038_;
}
else
{
size_t v___x_5046_; size_t v___x_5047_; lean_object* v___x_5048_; 
v___x_5046_ = ((size_t)0ULL);
v___x_5047_ = lean_usize_of_nat(v___x_5041_);
v___x_5048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5042_, v___f_5044_, v_tasks_5039_, v___x_5046_, v___x_5047_, v_z_5038_);
return v___x_5048_;
}
}
else
{
size_t v___x_5049_; size_t v___x_5050_; lean_object* v___x_5051_; 
v___x_5049_ = ((size_t)0ULL);
v___x_5050_ = lean_usize_of_nat(v___x_5041_);
v___x_5051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5042_, v___f_5044_, v_tasks_5039_, v___x_5049_, v___x_5050_, v_z_5038_);
return v___x_5051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5052_, lean_object* v_inst_5053_, lean_object* v_z_5054_, lean_object* v_tasks_5055_){
_start:
{
lean_object* v___x_5056_; 
v___x_5056_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5053_, v_z_5054_, v_tasks_5055_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5057_, lean_object* v___x_5058_, lean_object* v_____r_5059_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = lean_apply_2(v_toPure_5057_, lean_box(0), v___x_5058_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5061_, lean_object* v_setNGen_5062_, lean_object* v_toBind_5063_, lean_object* v_ngen_5064_){
_start:
{
lean_object* v_namePrefix_5065_; lean_object* v_idx_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5080_; 
v_namePrefix_5065_ = lean_ctor_get(v_ngen_5064_, 0);
v_idx_5066_ = lean_ctor_get(v_ngen_5064_, 1);
v_isSharedCheck_5080_ = !lean_is_exclusive(v_ngen_5064_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5068_ = v_ngen_5064_;
v_isShared_5069_ = v_isSharedCheck_5080_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_idx_5066_);
lean_inc(v_namePrefix_5065_);
lean_dec(v_ngen_5064_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5080_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5073_; 
lean_inc(v_idx_5066_);
lean_inc(v_namePrefix_5065_);
v___x_5070_ = l_Lean_Name_num___override(v_namePrefix_5065_, v_idx_5066_);
v___x_5071_ = lean_unsigned_to_nat(1u);
if (v_isShared_5069_ == 0)
{
lean_ctor_set(v___x_5068_, 1, v___x_5071_);
lean_ctor_set(v___x_5068_, 0, v___x_5070_);
v___x_5073_ = v___x_5068_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5070_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v___x_5071_);
v___x_5073_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
lean_object* v___f_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___f_5074_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5074_, 0, v_toPure_5061_);
lean_closure_set(v___f_5074_, 1, v___x_5073_);
v___x_5075_ = lean_nat_add(v_idx_5066_, v___x_5071_);
lean_dec(v_idx_5066_);
v___x_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5076_, 0, v_namePrefix_5065_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = lean_apply_1(v_setNGen_5062_, v___x_5076_);
v___x_5078_ = lean_apply_4(v_toBind_5063_, lean_box(0), lean_box(0), v___x_5077_, v___f_5074_);
return v___x_5078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5081_, lean_object* v_inst_5082_){
_start:
{
lean_object* v_toApplicative_5083_; lean_object* v_toBind_5084_; lean_object* v_getNGen_5085_; lean_object* v_setNGen_5086_; lean_object* v_toPure_5087_; lean_object* v___f_5088_; lean_object* v___x_5089_; 
v_toApplicative_5083_ = lean_ctor_get(v_inst_5081_, 0);
lean_inc_ref(v_toApplicative_5083_);
v_toBind_5084_ = lean_ctor_get(v_inst_5081_, 1);
lean_inc_n(v_toBind_5084_, 2);
lean_dec_ref(v_inst_5081_);
v_getNGen_5085_ = lean_ctor_get(v_inst_5082_, 0);
lean_inc(v_getNGen_5085_);
v_setNGen_5086_ = lean_ctor_get(v_inst_5082_, 1);
lean_inc(v_setNGen_5086_);
lean_dec_ref(v_inst_5082_);
v_toPure_5087_ = lean_ctor_get(v_toApplicative_5083_, 1);
lean_inc(v_toPure_5087_);
lean_dec_ref(v_toApplicative_5083_);
v___f_5088_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5088_, 0, v_toPure_5087_);
lean_closure_set(v___f_5088_, 1, v_setNGen_5086_);
lean_closure_set(v___f_5088_, 2, v_toBind_5084_);
v___x_5089_ = lean_apply_4(v_toBind_5084_, lean_box(0), lean_box(0), v_getNGen_5085_, v___f_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5090_, lean_object* v_inst_5091_, lean_object* v_inst_5092_){
_start:
{
lean_object* v___x_5093_; 
v___x_5093_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5091_, v_inst_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5094_, lean_object* v_env_5095_, lean_object* v_modName_5096_, lean_object* v_d_5097_, lean_object* v_val_5098_, lean_object* v_act_5099_, lean_object* v_as_5100_, size_t v_sz_5101_, size_t v_i_5102_, lean_object* v_b_5103_){
_start:
{
uint8_t v___x_5105_; 
v___x_5105_ = lean_usize_dec_lt(v_i_5102_, v_sz_5101_);
if (v___x_5105_ == 0)
{
lean_dec_ref(v_act_5099_);
lean_dec(v_modName_5096_);
lean_dec_ref(v_env_5095_);
lean_dec_ref(v_cctx_5094_);
return v_b_5103_;
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5107_; size_t v___x_5108_; size_t v___x_5109_; 
v_a_5106_ = lean_array_uget_borrowed(v_as_5100_, v_i_5102_);
lean_inc(v_a_5106_);
lean_inc_ref(v_act_5099_);
lean_inc(v_modName_5096_);
lean_inc_ref(v_env_5095_);
lean_inc_ref(v_cctx_5094_);
v___x_5107_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5094_, v_env_5095_, v_modName_5096_, v_d_5097_, v_val_5098_, v_b_5103_, v_act_5099_, v_a_5106_);
v___x_5108_ = ((size_t)1ULL);
v___x_5109_ = lean_usize_add(v_i_5102_, v___x_5108_);
v_i_5102_ = v___x_5109_;
v_b_5103_ = v___x_5107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5111_, lean_object* v_env_5112_, lean_object* v_modName_5113_, lean_object* v_d_5114_, lean_object* v_val_5115_, lean_object* v_act_5116_, lean_object* v_as_5117_, lean_object* v_sz_5118_, lean_object* v_i_5119_, lean_object* v_b_5120_, lean_object* v___y_5121_){
_start:
{
size_t v_sz_boxed_5122_; size_t v_i_boxed_5123_; lean_object* v_res_5124_; 
v_sz_boxed_5122_ = lean_unbox_usize(v_sz_5118_);
lean_dec(v_sz_5118_);
v_i_boxed_5123_ = lean_unbox_usize(v_i_5119_);
lean_dec(v_i_5119_);
v_res_5124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5111_, v_env_5112_, v_modName_5113_, v_d_5114_, v_val_5115_, v_act_5116_, v_as_5117_, v_sz_boxed_5122_, v_i_boxed_5123_, v_b_5120_);
lean_dec_ref(v_as_5117_);
lean_dec(v_val_5115_);
lean_dec(v_d_5114_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5125_, lean_object* v_ngen_5126_, lean_object* v_env_5127_, lean_object* v_d_5128_, lean_object* v_act_5129_){
_start:
{
lean_object* v___x_5131_; lean_object* v___x_5132_; uint8_t v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v_mainModule_5136_; lean_object* v___x_5137_; size_t v_sz_5138_; size_t v___x_5139_; lean_object* v___x_5140_; 
v___x_5131_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5126_);
v___x_5132_ = lean_st_mk_ref(v___x_5131_);
v___x_5133_ = 1;
v___x_5134_ = l_Lean_Environment_getLocalConstantInfos(v_env_5127_, v___x_5133_);
v___x_5135_ = l_Lean_Environment_header(v_env_5127_);
v_mainModule_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_mainModule_5136_);
lean_dec_ref(v___x_5135_);
v___x_5137_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v_sz_5138_ = lean_array_size(v___x_5134_);
v___x_5139_ = ((size_t)0ULL);
v___x_5140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5125_, v_env_5127_, v_mainModule_5136_, v_d_5128_, v___x_5132_, v_act_5129_, v___x_5134_, v_sz_5138_, v___x_5139_, v___x_5137_);
lean_dec_ref(v___x_5134_);
lean_dec(v___x_5132_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5141_, lean_object* v_ngen_5142_, lean_object* v_env_5143_, lean_object* v_d_5144_, lean_object* v_act_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5141_, v_ngen_5142_, v_env_5143_, v_d_5144_, v_act_5145_);
lean_dec(v_d_5144_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5148_, lean_object* v_cctx_5149_, lean_object* v_ngen_5150_, lean_object* v_env_5151_, lean_object* v_d_5152_, lean_object* v_act_5153_){
_start:
{
lean_object* v___x_5155_; 
v___x_5155_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5149_, v_ngen_5150_, v_env_5151_, v_d_5152_, v_act_5153_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5156_, lean_object* v_cctx_5157_, lean_object* v_ngen_5158_, lean_object* v_env_5159_, lean_object* v_d_5160_, lean_object* v_act_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5156_, v_cctx_5157_, v_ngen_5158_, v_env_5159_, v_d_5160_, v_act_5161_);
lean_dec(v_d_5160_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5164_, lean_object* v_cctx_5165_, lean_object* v_env_5166_, lean_object* v_modName_5167_, lean_object* v_d_5168_, lean_object* v_val_5169_, lean_object* v_act_5170_, lean_object* v_as_5171_, size_t v_sz_5172_, size_t v_i_5173_, lean_object* v_b_5174_){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5165_, v_env_5166_, v_modName_5167_, v_d_5168_, v_val_5169_, v_act_5170_, v_as_5171_, v_sz_5172_, v_i_5173_, v_b_5174_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5177_, lean_object* v_cctx_5178_, lean_object* v_env_5179_, lean_object* v_modName_5180_, lean_object* v_d_5181_, lean_object* v_val_5182_, lean_object* v_act_5183_, lean_object* v_as_5184_, lean_object* v_sz_5185_, lean_object* v_i_5186_, lean_object* v_b_5187_, lean_object* v___y_5188_){
_start:
{
size_t v_sz_boxed_5189_; size_t v_i_boxed_5190_; lean_object* v_res_5191_; 
v_sz_boxed_5189_ = lean_unbox_usize(v_sz_5185_);
lean_dec(v_sz_5185_);
v_i_boxed_5190_ = lean_unbox_usize(v_i_5186_);
lean_dec(v_i_5186_);
v_res_5191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5177_, v_cctx_5178_, v_env_5179_, v_modName_5180_, v_d_5181_, v_val_5182_, v_act_5183_, v_as_5184_, v_sz_boxed_5189_, v_i_boxed_5190_, v_b_5187_);
lean_dec_ref(v_as_5184_);
lean_dec(v_val_5182_);
lean_dec(v_d_5181_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5192_, lean_object* v_x_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
if (lean_obj_tag(v_x_5193_) == 0)
{
lean_object* v___x_5199_; 
v___x_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5199_, 0, v_x_5192_);
return v___x_5199_;
}
else
{
lean_object* v_head_5200_; lean_object* v_tail_5201_; lean_object* v___x_5202_; 
v_head_5200_ = lean_ctor_get(v_x_5193_, 0);
lean_inc(v_head_5200_);
v_tail_5201_ = lean_ctor_get(v_x_5193_, 1);
lean_inc(v_tail_5201_);
lean_dec_ref_known(v_x_5193_, 2);
v___x_5202_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5192_, v_head_5200_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v_a_5203_; 
v_a_5203_ = lean_ctor_get(v___x_5202_, 0);
lean_inc(v_a_5203_);
lean_dec_ref_known(v___x_5202_, 1);
v_x_5192_ = v_a_5203_;
v_x_5193_ = v_tail_5201_;
goto _start;
}
else
{
lean_dec(v_tail_5201_);
return v___x_5202_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5205_, lean_object* v_x_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5205_, v_x_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5213_, lean_object* v_keys_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v___x_5220_; 
v___x_5220_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5213_, v_keys_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5221_, lean_object* v_keys_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5221_, v_keys_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5229_, lean_object* v_t_5230_, lean_object* v_keys_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_){
_start:
{
lean_object* v___x_5237_; 
v___x_5237_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5230_, v_keys_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5238_, lean_object* v_t_5239_, lean_object* v_keys_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5238_, v_t_5239_, v_keys_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_);
lean_dec(v_a_5244_);
lean_dec_ref(v_a_5243_);
lean_dec(v_a_5242_);
lean_dec_ref(v_a_5241_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5247_, lean_object* v_x_5248_, lean_object* v_x_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_){
_start:
{
lean_object* v___x_5255_; 
v___x_5255_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5248_, v_x_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5256_, lean_object* v_x_5257_, lean_object* v_x_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5256_, v_x_5257_, v_x_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_);
lean_dec(v___y_5262_);
lean_dec_ref(v___y_5261_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5265_, size_t v_sz_5266_, size_t v_i_5267_, lean_object* v_b_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
uint8_t v___x_5275_; 
v___x_5275_ = lean_usize_dec_lt(v_i_5267_, v_sz_5266_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; 
v___x_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5276_, 0, v_b_5268_);
return v___x_5276_;
}
else
{
lean_object* v_a_5277_; lean_object* v___x_5278_; 
v_a_5277_ = lean_array_uget_borrowed(v_as_5265_, v_i_5267_);
v___x_5278_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5277_, v_b_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5291_; 
v_a_5279_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5281_ = v___x_5278_;
v_isShared_5282_ = v_isSharedCheck_5291_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5278_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5291_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
if (lean_obj_tag(v_a_5279_) == 0)
{
lean_object* v_a_5283_; lean_object* v___x_5285_; 
v_a_5283_ = lean_ctor_get(v_a_5279_, 0);
lean_inc(v_a_5283_);
lean_dec_ref_known(v_a_5279_, 1);
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 0, v_a_5283_);
v___x_5285_ = v___x_5281_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5283_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
else
{
lean_object* v_a_5287_; size_t v___x_5288_; size_t v___x_5289_; 
lean_del_object(v___x_5281_);
v_a_5287_ = lean_ctor_get(v_a_5279_, 0);
lean_inc(v_a_5287_);
lean_dec_ref_known(v_a_5279_, 1);
v___x_5288_ = ((size_t)1ULL);
v___x_5289_ = lean_usize_add(v_i_5267_, v___x_5288_);
v_i_5267_ = v___x_5289_;
v_b_5268_ = v_a_5287_;
goto _start;
}
}
}
else
{
lean_object* v_a_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5299_; 
v_a_5292_ = lean_ctor_get(v___x_5278_, 0);
v_isSharedCheck_5299_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5294_ = v___x_5278_;
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_a_5292_);
lean_dec(v___x_5278_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5297_; 
if (v_isShared_5295_ == 0)
{
v___x_5297_ = v___x_5294_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_){
_start:
{
lean_object* v___x_5307_; uint8_t v___x_5308_; 
v___x_5307_ = lean_unsigned_to_nat(0u);
v___x_5308_ = lean_nat_dec_eq(v_next_5300_, v___x_5307_);
if (v___x_5308_ == 0)
{
lean_object* v___x_5309_; 
v___x_5309_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v_snd_5311_; lean_object* v_fst_5312_; lean_object* v_fst_5313_; lean_object* v_snd_5314_; lean_object* v___x_5315_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc(v_a_5310_);
lean_dec_ref_known(v___x_5309_, 1);
v_snd_5311_ = lean_ctor_get(v_a_5310_, 1);
lean_inc(v_snd_5311_);
v_fst_5312_ = lean_ctor_get(v_a_5310_, 0);
lean_inc(v_fst_5312_);
lean_dec(v_a_5310_);
v_fst_5313_ = lean_ctor_get(v_snd_5311_, 0);
lean_inc(v_fst_5313_);
v_snd_5314_ = lean_ctor_get(v_snd_5311_, 1);
lean_inc(v_snd_5314_);
lean_dec(v_snd_5311_);
v___x_5315_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5313_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; lean_object* v_buckets_5317_; lean_object* v___x_5318_; size_t v_sz_5319_; size_t v___x_5320_; lean_object* v___x_5321_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5316_);
lean_dec_ref_known(v___x_5315_, 1);
v_buckets_5317_ = lean_ctor_get(v_snd_5314_, 1);
v___x_5318_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5319_ = lean_array_size(v_buckets_5317_);
v___x_5320_ = ((size_t)0ULL);
v___x_5321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5317_, v_sz_5319_, v___x_5320_, v___x_5318_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5335_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5324_ = v___x_5321_;
v_isShared_5325_ = v_isSharedCheck_5335_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5321_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5335_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5333_; 
v___x_5326_ = lean_st_ref_take(v_a_5301_);
v___x_5327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5318_);
lean_ctor_set(v___x_5327_, 1, v_fst_5313_);
lean_ctor_set(v___x_5327_, 2, v_snd_5314_);
lean_ctor_set(v___x_5327_, 3, v___x_5318_);
v___x_5328_ = lean_array_set(v___x_5326_, v_next_5300_, v___x_5327_);
v___x_5329_ = lean_st_ref_set(v_a_5301_, v___x_5328_);
v___x_5330_ = l_Array_append___redArg(v_fst_5312_, v_a_5316_);
lean_dec(v_a_5316_);
v___x_5331_ = l_Array_append___redArg(v___x_5330_, v_a_5322_);
lean_dec(v_a_5322_);
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 0, v___x_5331_);
v___x_5333_ = v___x_5324_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5331_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
else
{
lean_dec(v_a_5316_);
lean_dec(v_snd_5314_);
lean_dec(v_fst_5313_);
lean_dec(v_fst_5312_);
return v___x_5321_;
}
}
else
{
lean_dec(v_snd_5314_);
lean_dec(v_fst_5313_);
lean_dec(v_fst_5312_);
return v___x_5315_;
}
}
else
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
v_a_5336_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5309_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5309_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
}
else
{
lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5344_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5344_);
return v___x_5345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
if (lean_obj_tag(v_a_5346_) == 0)
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5354_, 0, v_a_5347_);
v___x_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5354_);
return v___x_5355_;
}
else
{
lean_object* v_value_5356_; lean_object* v_tail_5357_; lean_object* v___x_5358_; 
v_value_5356_ = lean_ctor_get(v_a_5346_, 1);
v_tail_5357_ = lean_ctor_get(v_a_5346_, 2);
v___x_5358_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5356_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v___x_5360_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
lean_dec_ref_known(v___x_5358_, 1);
v___x_5360_ = l_Array_append___redArg(v_a_5347_, v_a_5359_);
lean_dec(v_a_5359_);
v_a_5346_ = v_tail_5357_;
v_a_5347_ = v___x_5360_;
goto _start;
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
lean_dec_ref(v_a_5347_);
v_a_5362_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5358_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5358_);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5370_, v_a_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
lean_dec(v___y_5376_);
lean_dec_ref(v___y_5375_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec(v_a_5370_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5379_, lean_object* v_sz_5380_, lean_object* v_i_5381_, lean_object* v_b_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
size_t v_sz_boxed_5389_; size_t v_i_boxed_5390_; lean_object* v_res_5391_; 
v_sz_boxed_5389_ = lean_unbox_usize(v_sz_5380_);
lean_dec(v_sz_5380_);
v_i_boxed_5390_ = lean_unbox_usize(v_i_5381_);
lean_dec(v_i_5381_);
v_res_5391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5379_, v_sz_boxed_5389_, v_i_boxed_5390_, v_b_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v_as_5379_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
lean_dec(v_a_5395_);
lean_dec_ref(v_a_5394_);
lean_dec(v_a_5393_);
lean_dec(v_next_5392_);
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5400_, lean_object* v_next_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_){
_start:
{
lean_object* v___x_5408_; 
v___x_5408_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
return v___x_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5409_, lean_object* v_next_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5409_, v_next_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_);
lean_dec(v_a_5415_);
lean_dec_ref(v_a_5414_);
lean_dec(v_a_5413_);
lean_dec_ref(v_a_5412_);
lean_dec(v_a_5411_);
lean_dec(v_next_5410_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_){
_start:
{
lean_object* v___x_5427_; 
v___x_5427_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5419_, v_a_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5428_, v_a_5429_, v_a_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
lean_dec(v___y_5435_);
lean_dec_ref(v___y_5434_);
lean_dec(v___y_5433_);
lean_dec_ref(v___y_5432_);
lean_dec(v___y_5431_);
lean_dec(v_a_5429_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5438_, lean_object* v_as_5439_, size_t v_sz_5440_, size_t v_i_5441_, lean_object* v_b_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v___x_5449_; 
v___x_5449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5439_, v_sz_5440_, v_i_5441_, v_b_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5450_, lean_object* v_as_5451_, lean_object* v_sz_5452_, lean_object* v_i_5453_, lean_object* v_b_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_){
_start:
{
size_t v_sz_boxed_5461_; size_t v_i_boxed_5462_; lean_object* v_res_5463_; 
v_sz_boxed_5461_ = lean_unbox_usize(v_sz_5452_);
lean_dec(v_sz_5452_);
v_i_boxed_5462_ = lean_unbox_usize(v_i_5453_);
lean_dec(v_i_5453_);
v_res_5463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5450_, v_as_5451_, v_sz_boxed_5461_, v_i_boxed_5462_, v_b_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v_as_5451_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5464_, lean_object* v_rest_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_){
_start:
{
lean_object* v___x_5472_; uint8_t v___x_5473_; 
v___x_5472_ = lean_unsigned_to_nat(0u);
v___x_5473_ = lean_nat_dec_eq(v_next_5464_, v___x_5472_);
if (v___x_5473_ == 0)
{
lean_object* v___x_5474_; 
v___x_5474_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5464_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v_a_5475_; lean_object* v_snd_5476_; 
v_a_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_a_5475_);
lean_dec_ref_known(v___x_5474_, 1);
v_snd_5476_ = lean_ctor_get(v_a_5475_, 1);
lean_inc(v_snd_5476_);
lean_dec(v_a_5475_);
if (lean_obj_tag(v_rest_5465_) == 0)
{
lean_object* v___x_5477_; 
lean_dec(v_snd_5476_);
v___x_5477_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5464_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_);
lean_dec(v_next_5464_);
return v___x_5477_;
}
else
{
lean_object* v_fst_5478_; lean_object* v_snd_5479_; lean_object* v_head_5480_; lean_object* v_tail_5481_; lean_object* v___x_5482_; uint8_t v___x_5483_; 
lean_dec(v_next_5464_);
v_fst_5478_ = lean_ctor_get(v_snd_5476_, 0);
lean_inc(v_fst_5478_);
v_snd_5479_ = lean_ctor_get(v_snd_5476_, 1);
lean_inc(v_snd_5479_);
lean_dec(v_snd_5476_);
v_head_5480_ = lean_ctor_get(v_rest_5465_, 0);
v_tail_5481_ = lean_ctor_get(v_rest_5465_, 1);
v___x_5482_ = lean_box(3);
v___x_5483_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5480_, v___x_5482_);
if (v___x_5483_ == 0)
{
lean_object* v___x_5484_; 
lean_dec(v_fst_5478_);
v___x_5484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5479_, v_head_5480_, v___x_5472_);
lean_dec(v_snd_5479_);
v_next_5464_ = v___x_5484_;
v_rest_5465_ = v_tail_5481_;
goto _start;
}
else
{
lean_dec(v_snd_5479_);
v_next_5464_ = v_fst_5478_;
v_rest_5465_ = v_tail_5481_;
goto _start;
}
}
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec(v_next_5464_);
v_a_5487_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5474_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5474_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
else
{
lean_object* v___x_5495_; lean_object* v___x_5496_; 
lean_dec(v_next_5464_);
v___x_5495_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5496_, 0, v___x_5495_);
return v___x_5496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5497_, lean_object* v_rest_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_){
_start:
{
lean_object* v_res_5505_; 
v_res_5505_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5497_, v_rest_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_);
lean_dec(v_a_5503_);
lean_dec_ref(v_a_5502_);
lean_dec(v_a_5501_);
lean_dec_ref(v_a_5500_);
lean_dec(v_a_5499_);
lean_dec(v_rest_5498_);
return v_res_5505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5506_, lean_object* v_next_5507_, lean_object* v_rest_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_){
_start:
{
lean_object* v___x_5515_; 
v___x_5515_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5507_, v_rest_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_);
return v___x_5515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5516_, lean_object* v_next_5517_, lean_object* v_rest_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_){
_start:
{
lean_object* v_res_5525_; 
v_res_5525_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5516_, v_next_5517_, v_rest_5518_, v_a_5519_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_);
lean_dec(v_a_5523_);
lean_dec_ref(v_a_5522_);
lean_dec(v_a_5521_);
lean_dec_ref(v_a_5520_);
lean_dec(v_a_5519_);
lean_dec(v_rest_5518_);
return v_res_5525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5526_, lean_object* v_path_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_){
_start:
{
if (lean_obj_tag(v_path_5527_) == 0)
{
lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; 
v___x_5533_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5533_);
lean_ctor_set(v___x_5534_, 1, v_t_5526_);
v___x_5535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5535_, 0, v___x_5534_);
return v___x_5535_;
}
else
{
lean_object* v_head_5536_; lean_object* v_tail_5537_; lean_object* v_roots_5538_; lean_object* v___x_5539_; lean_object* v_idx_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; 
v_head_5536_ = lean_ctor_get(v_path_5527_, 0);
lean_inc(v_head_5536_);
v_tail_5537_ = lean_ctor_get(v_path_5527_, 1);
lean_inc(v_tail_5537_);
lean_dec_ref_known(v_path_5527_, 2);
v_roots_5538_ = lean_ctor_get(v_t_5526_, 1);
v___x_5539_ = lean_unsigned_to_nat(0u);
v_idx_5540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5538_, v_head_5536_, v___x_5539_);
lean_dec(v_head_5536_);
v___x_5541_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5541_, 0, lean_box(0));
lean_closure_set(v___x_5541_, 1, v_idx_5540_);
lean_closure_set(v___x_5541_, 2, v_tail_5537_);
v___x_5542_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5526_, v___x_5541_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
return v___x_5542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5543_, lean_object* v_path_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_){
_start:
{
lean_object* v_res_5550_; 
v_res_5550_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5543_, v_path_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_);
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
return v_res_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5551_, lean_object* v_t_5552_, lean_object* v_path_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_){
_start:
{
lean_object* v___x_5559_; 
v___x_5559_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5552_, v_path_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
return v___x_5559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5560_, lean_object* v_t_5561_, lean_object* v_path_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_){
_start:
{
lean_object* v_res_5568_; 
v_res_5568_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5560_, v_t_5561_, v_path_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_);
lean_dec(v_a_5566_);
lean_dec_ref(v_a_5565_);
lean_dec(v_a_5564_);
lean_dec_ref(v_a_5563_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5569_, lean_object* v_b_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_){
_start:
{
if (lean_obj_tag(v_as_x27_5569_) == 0)
{
lean_object* v___x_5576_; 
v___x_5576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5576_, 0, v_b_5570_);
return v___x_5576_;
}
else
{
lean_object* v_head_5577_; lean_object* v_tail_5578_; lean_object* v_fst_5579_; lean_object* v_snd_5580_; lean_object* v___x_5581_; 
v_head_5577_ = lean_ctor_get(v_as_x27_5569_, 0);
v_tail_5578_ = lean_ctor_get(v_as_x27_5569_, 1);
v_fst_5579_ = lean_ctor_get(v_b_5570_, 0);
lean_inc(v_fst_5579_);
v_snd_5580_ = lean_ctor_get(v_b_5570_, 1);
lean_inc(v_snd_5580_);
lean_dec_ref(v_b_5570_);
lean_inc(v_head_5577_);
v___x_5581_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5580_, v_head_5577_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v_a_5582_; lean_object* v_fst_5583_; lean_object* v_snd_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5593_; 
v_a_5582_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_a_5582_);
lean_dec_ref_known(v___x_5581_, 1);
v_fst_5583_ = lean_ctor_get(v_a_5582_, 0);
v_snd_5584_ = lean_ctor_get(v_a_5582_, 1);
v_isSharedCheck_5593_ = !lean_is_exclusive(v_a_5582_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5586_ = v_a_5582_;
v_isShared_5587_ = v_isSharedCheck_5593_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_snd_5584_);
lean_inc(v_fst_5583_);
lean_dec(v_a_5582_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5593_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5588_; lean_object* v___x_5590_; 
v___x_5588_ = l_Array_append___redArg(v_fst_5579_, v_fst_5583_);
lean_dec(v_fst_5583_);
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 0, v___x_5588_);
v___x_5590_ = v___x_5586_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5588_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v_snd_5584_);
v___x_5590_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
v_as_x27_5569_ = v_tail_5578_;
v_b_5570_ = v___x_5590_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5579_);
return v___x_5581_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5594_, lean_object* v_b_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_){
_start:
{
lean_object* v_res_5601_; 
v_res_5601_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5594_, v_b_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_);
lean_dec(v___y_5599_);
lean_dec_ref(v___y_5598_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
lean_dec(v_as_x27_5594_);
return v_res_5601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5602_, lean_object* v_keys_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_){
_start:
{
lean_object* v_allExtracted_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
v_allExtracted_5609_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5610_, 0, v_allExtracted_5609_);
lean_ctor_set(v___x_5610_, 1, v_t_5602_);
v___x_5611_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5603_, v___x_5610_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5628_; 
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5614_ = v___x_5611_;
v_isShared_5615_ = v_isSharedCheck_5628_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5611_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5628_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v_fst_5616_; lean_object* v_snd_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5627_; 
v_fst_5616_ = lean_ctor_get(v_a_5612_, 0);
v_snd_5617_ = lean_ctor_get(v_a_5612_, 1);
v_isSharedCheck_5627_ = !lean_is_exclusive(v_a_5612_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5619_ = v_a_5612_;
v_isShared_5620_ = v_isSharedCheck_5627_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_snd_5617_);
lean_inc(v_fst_5616_);
lean_dec(v_a_5612_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5627_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5622_; 
if (v_isShared_5620_ == 0)
{
v___x_5622_ = v___x_5619_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_fst_5616_);
lean_ctor_set(v_reuseFailAlloc_5626_, 1, v_snd_5617_);
v___x_5622_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
lean_object* v___x_5624_; 
if (v_isShared_5615_ == 0)
{
lean_ctor_set(v___x_5614_, 0, v___x_5622_);
v___x_5624_ = v___x_5614_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v___x_5622_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
}
}
}
else
{
return v___x_5611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5629_, lean_object* v_keys_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5629_, v_keys_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
lean_dec(v_a_5632_);
lean_dec_ref(v_a_5631_);
lean_dec(v_keys_5630_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5637_, lean_object* v_t_5638_, lean_object* v_keys_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_){
_start:
{
lean_object* v___x_5645_; 
v___x_5645_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5638_, v_keys_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_);
return v___x_5645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5646_, lean_object* v_t_5647_, lean_object* v_keys_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5646_, v_t_5647_, v_keys_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_);
lean_dec(v_a_5652_);
lean_dec_ref(v_a_5651_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_keys_5648_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5655_, lean_object* v_as_5656_, lean_object* v_as_x27_5657_, lean_object* v_b_5658_, lean_object* v_a_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v___x_5665_; 
v___x_5665_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5657_, v_b_5658_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5666_, lean_object* v_as_5667_, lean_object* v_as_x27_5668_, lean_object* v_b_5669_, lean_object* v_a_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_){
_start:
{
lean_object* v_res_5676_; 
v_res_5676_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5666_, v_as_5667_, v_as_x27_5668_, v_b_5669_, v_a_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v_as_x27_5668_);
lean_dec(v_as_5667_);
return v_res_5676_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5678_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5679_ = l_Lean_stringToMessageData(v___x_5678_);
return v___x_5679_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; 
v___x_5681_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5682_ = l_Lean_stringToMessageData(v___x_5681_);
return v___x_5682_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5684_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5685_ = l_Lean_stringToMessageData(v___x_5684_);
return v___x_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5686_, lean_object* v_inst_5687_, lean_object* v_inst_5688_, lean_object* v_inst_5689_, lean_object* v_f_5690_){
_start:
{
lean_object* v_module_5691_; lean_object* v_const_5692_; lean_object* v_exception_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; 
v_module_5691_ = lean_ctor_get(v_f_5690_, 0);
lean_inc(v_module_5691_);
v_const_5692_ = lean_ctor_get(v_f_5690_, 1);
lean_inc(v_const_5692_);
v_exception_5693_ = lean_ctor_get(v_f_5690_, 2);
lean_inc_ref(v_exception_5693_);
lean_dec_ref(v_f_5690_);
v___x_5694_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5695_ = l_Lean_MessageData_ofName(v_const_5692_);
v___x_5696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5694_);
lean_ctor_set(v___x_5696_, 1, v___x_5695_);
v___x_5697_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = l_Lean_MessageData_ofName(v_module_5691_);
v___x_5700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5698_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5700_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = l_Lean_Exception_toMessageData(v_exception_5693_);
v___x_5704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5702_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = l_Lean_logError___redArg(v_inst_5686_, v_inst_5687_, v_inst_5688_, v_inst_5689_, v___x_5704_);
return v___x_5705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5706_, lean_object* v_inst_5707_, lean_object* v_inst_5708_, lean_object* v_inst_5709_, lean_object* v_inst_5710_, lean_object* v_f_5711_){
_start:
{
lean_object* v___x_5712_; 
v___x_5712_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5707_, v_inst_5708_, v_inst_5709_, v_inst_5710_, v_f_5711_);
return v___x_5712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_toApplicative_5713_, lean_object* v_tasks_5714_, lean_object* v_t_5715_){
_start:
{
lean_object* v_toPure_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; 
v_toPure_5716_ = lean_ctor_get(v_toApplicative_5713_, 1);
lean_inc(v_toPure_5716_);
lean_dec_ref(v_toApplicative_5713_);
v___x_5717_ = lean_array_push(v_tasks_5714_, v_t_5715_);
v___x_5718_ = lean_apply_2(v_toPure_5716_, lean_box(0), v___x_5717_);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5719_, lean_object* v_inst_5720_, lean_object* v_cctx_5721_, lean_object* v_env_5722_, lean_object* v_act_5723_, lean_object* v_constantsPerTask_5724_, lean_object* v_n_5725_, lean_object* v_ngen_5726_, lean_object* v_tasks_5727_, lean_object* v_start_5728_, lean_object* v_cnt_5729_, lean_object* v_idx_5730_){
_start:
{
lean_object* v___x_5731_; lean_object* v_moduleData_5732_; lean_object* v___x_5733_; uint8_t v___x_5734_; 
v___x_5731_ = l_Lean_Environment_header(v_env_5722_);
v_moduleData_5732_ = lean_ctor_get(v___x_5731_, 6);
lean_inc_ref(v_moduleData_5732_);
lean_dec_ref(v___x_5731_);
v___x_5733_ = lean_array_get_size(v_moduleData_5732_);
v___x_5734_ = lean_nat_dec_lt(v_idx_5730_, v___x_5733_);
if (v___x_5734_ == 0)
{
uint8_t v___x_5735_; 
lean_dec_ref(v_moduleData_5732_);
lean_dec(v_idx_5730_);
lean_dec(v_cnt_5729_);
lean_dec(v_constantsPerTask_5724_);
v___x_5735_ = lean_nat_dec_lt(v_start_5728_, v_n_5725_);
if (v___x_5735_ == 0)
{
lean_object* v_toApplicative_5736_; lean_object* v_toPure_5737_; lean_object* v___x_5738_; 
lean_dec(v_start_5728_);
lean_dec_ref(v_ngen_5726_);
lean_dec(v_n_5725_);
lean_dec_ref(v_act_5723_);
lean_dec_ref(v_env_5722_);
lean_dec_ref(v_cctx_5721_);
lean_dec(v_inst_5720_);
v_toApplicative_5736_ = lean_ctor_get(v_inst_5719_, 0);
lean_inc_ref(v_toApplicative_5736_);
lean_dec_ref(v_inst_5719_);
v_toPure_5737_ = lean_ctor_get(v_toApplicative_5736_, 1);
lean_inc(v_toPure_5737_);
lean_dec_ref(v_toApplicative_5736_);
v___x_5738_ = lean_apply_2(v_toPure_5737_, lean_box(0), v_tasks_5727_);
return v___x_5738_;
}
else
{
lean_object* v_namePrefix_5739_; lean_object* v_idx_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5757_; 
v_namePrefix_5739_ = lean_ctor_get(v_ngen_5726_, 0);
v_idx_5740_ = lean_ctor_get(v_ngen_5726_, 1);
v_isSharedCheck_5757_ = !lean_is_exclusive(v_ngen_5726_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5742_ = v_ngen_5726_;
v_isShared_5743_ = v_isSharedCheck_5757_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_idx_5740_);
lean_inc(v_namePrefix_5739_);
lean_dec(v_ngen_5726_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5757_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v_toApplicative_5744_; lean_object* v_toBind_5745_; lean_object* v___f_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5750_; 
v_toApplicative_5744_ = lean_ctor_get(v_inst_5719_, 0);
lean_inc_ref(v_toApplicative_5744_);
v_toBind_5745_ = lean_ctor_get(v_inst_5719_, 1);
lean_inc(v_toBind_5745_);
lean_dec_ref(v_inst_5719_);
v___f_5746_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5746_, 0, v_toApplicative_5744_);
lean_closure_set(v___f_5746_, 1, v_tasks_5727_);
v___x_5747_ = l_Lean_Name_num___override(v_namePrefix_5739_, v_idx_5740_);
v___x_5748_ = lean_unsigned_to_nat(1u);
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 1, v___x_5748_);
lean_ctor_set(v___x_5742_, 0, v___x_5747_);
v___x_5750_ = v___x_5742_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5747_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v___x_5748_);
v___x_5750_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; 
v___x_5751_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5751_, 0, lean_box(0));
lean_closure_set(v___x_5751_, 1, v_cctx_5721_);
lean_closure_set(v___x_5751_, 2, v___x_5750_);
lean_closure_set(v___x_5751_, 3, v_env_5722_);
lean_closure_set(v___x_5751_, 4, v_act_5723_);
lean_closure_set(v___x_5751_, 5, v_start_5728_);
lean_closure_set(v___x_5751_, 6, v_n_5725_);
v___x_5752_ = lean_unsigned_to_nat(0u);
v___x_5753_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5753_, 0, lean_box(0));
lean_closure_set(v___x_5753_, 1, v___x_5751_);
lean_closure_set(v___x_5753_, 2, v___x_5752_);
v___x_5754_ = lean_apply_2(v_inst_5720_, lean_box(0), v___x_5753_);
v___x_5755_ = lean_apply_4(v_toBind_5745_, lean_box(0), lean_box(0), v___x_5754_, v___f_5746_);
return v___x_5755_;
}
}
}
}
else
{
lean_object* v_mdata_5758_; lean_object* v_constants_5759_; lean_object* v___x_5760_; lean_object* v_cnt_5761_; uint8_t v___x_5762_; 
v_mdata_5758_ = lean_array_fget(v_moduleData_5732_, v_idx_5730_);
lean_dec_ref(v_moduleData_5732_);
v_constants_5759_ = lean_ctor_get(v_mdata_5758_, 2);
lean_inc_ref(v_constants_5759_);
lean_dec(v_mdata_5758_);
v___x_5760_ = lean_array_get_size(v_constants_5759_);
lean_dec_ref(v_constants_5759_);
v_cnt_5761_ = lean_nat_add(v_cnt_5729_, v___x_5760_);
lean_dec(v_cnt_5729_);
v___x_5762_ = lean_nat_dec_lt(v_constantsPerTask_5724_, v_cnt_5761_);
if (v___x_5762_ == 0)
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = lean_unsigned_to_nat(1u);
v___x_5764_ = lean_nat_add(v_idx_5730_, v___x_5763_);
lean_dec(v_idx_5730_);
v_cnt_5729_ = v_cnt_5761_;
v_idx_5730_ = v___x_5764_;
goto _start;
}
else
{
lean_object* v_namePrefix_5766_; lean_object* v_idx_5767_; lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5786_; 
lean_dec(v_cnt_5761_);
v_namePrefix_5766_ = lean_ctor_get(v_ngen_5726_, 0);
v_idx_5767_ = lean_ctor_get(v_ngen_5726_, 1);
v_isSharedCheck_5786_ = !lean_is_exclusive(v_ngen_5726_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5769_ = v_ngen_5726_;
v_isShared_5770_ = v_isSharedCheck_5786_;
goto v_resetjp_5768_;
}
else
{
lean_inc(v_idx_5767_);
lean_inc(v_namePrefix_5766_);
lean_dec(v_ngen_5726_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5786_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v_toBind_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5775_; 
v_toBind_5771_ = lean_ctor_get(v_inst_5719_, 1);
lean_inc(v_toBind_5771_);
lean_inc(v_idx_5767_);
lean_inc(v_namePrefix_5766_);
v___x_5772_ = l_Lean_Name_num___override(v_namePrefix_5766_, v_idx_5767_);
v___x_5773_ = lean_unsigned_to_nat(1u);
if (v_isShared_5770_ == 0)
{
lean_ctor_set(v___x_5769_, 1, v___x_5773_);
lean_ctor_set(v___x_5769_, 0, v___x_5772_);
v___x_5775_ = v___x_5769_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v___x_5772_);
lean_ctor_set(v_reuseFailAlloc_5785_, 1, v___x_5773_);
v___x_5775_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___f_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; 
v___x_5776_ = lean_nat_add(v_idx_5767_, v___x_5773_);
lean_dec(v_idx_5767_);
v___x_5777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5777_, 0, v_namePrefix_5766_);
lean_ctor_set(v___x_5777_, 1, v___x_5776_);
v___x_5778_ = lean_nat_add(v_idx_5730_, v___x_5773_);
lean_dec(v_idx_5730_);
lean_inc(v___x_5778_);
lean_inc_ref(v_act_5723_);
lean_inc_ref(v_env_5722_);
lean_inc_ref(v_cctx_5721_);
lean_inc(v_inst_5720_);
v___f_5779_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5779_, 0, v_tasks_5727_);
lean_closure_set(v___f_5779_, 1, v_inst_5719_);
lean_closure_set(v___f_5779_, 2, v_inst_5720_);
lean_closure_set(v___f_5779_, 3, v_cctx_5721_);
lean_closure_set(v___f_5779_, 4, v_env_5722_);
lean_closure_set(v___f_5779_, 5, v_act_5723_);
lean_closure_set(v___f_5779_, 6, v_constantsPerTask_5724_);
lean_closure_set(v___f_5779_, 7, v_n_5725_);
lean_closure_set(v___f_5779_, 8, v___x_5777_);
lean_closure_set(v___f_5779_, 9, v___x_5778_);
v___x_5780_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5780_, 0, lean_box(0));
lean_closure_set(v___x_5780_, 1, v_cctx_5721_);
lean_closure_set(v___x_5780_, 2, v___x_5775_);
lean_closure_set(v___x_5780_, 3, v_env_5722_);
lean_closure_set(v___x_5780_, 4, v_act_5723_);
lean_closure_set(v___x_5780_, 5, v_start_5728_);
lean_closure_set(v___x_5780_, 6, v___x_5778_);
v___x_5781_ = lean_unsigned_to_nat(0u);
v___x_5782_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5782_, 0, lean_box(0));
lean_closure_set(v___x_5782_, 1, v___x_5780_);
lean_closure_set(v___x_5782_, 2, v___x_5781_);
v___x_5783_ = lean_apply_2(v_inst_5720_, lean_box(0), v___x_5782_);
v___x_5784_ = lean_apply_4(v_toBind_5771_, lean_box(0), lean_box(0), v___x_5783_, v___f_5779_);
return v___x_5784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5787_, lean_object* v_inst_5788_, lean_object* v_inst_5789_, lean_object* v_cctx_5790_, lean_object* v_env_5791_, lean_object* v_act_5792_, lean_object* v_constantsPerTask_5793_, lean_object* v_n_5794_, lean_object* v___x_5795_, lean_object* v___x_5796_, lean_object* v_t_5797_){
_start:
{
lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
v___x_5798_ = lean_array_push(v_tasks_5787_, v_t_5797_);
v___x_5799_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5796_);
v___x_5800_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5788_, v_inst_5789_, v_cctx_5790_, v_env_5791_, v_act_5792_, v_constantsPerTask_5793_, v_n_5794_, v___x_5795_, v___x_5798_, v___x_5796_, v___x_5799_, v___x_5796_);
return v___x_5800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5801_, lean_object* v_00_u03b1_5802_, lean_object* v_inst_5803_, lean_object* v_inst_5804_, lean_object* v_cctx_5805_, lean_object* v_env_5806_, lean_object* v_act_5807_, lean_object* v_constantsPerTask_5808_, lean_object* v_n_5809_, lean_object* v_ngen_5810_, lean_object* v_tasks_5811_, lean_object* v_start_5812_, lean_object* v_cnt_5813_, lean_object* v_idx_5814_){
_start:
{
lean_object* v___x_5815_; 
v___x_5815_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5803_, v_inst_5804_, v_cctx_5805_, v_env_5806_, v_act_5807_, v_constantsPerTask_5808_, v_n_5809_, v_ngen_5810_, v_tasks_5811_, v_start_5812_, v_cnt_5813_, v_idx_5814_);
return v___x_5815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5816_, lean_object* v_h__1_5817_){
_start:
{
lean_object* v_fst_5818_; lean_object* v_snd_5819_; lean_object* v___x_5820_; 
v_fst_5818_ = lean_ctor_get(v_x_5816_, 0);
lean_inc(v_fst_5818_);
v_snd_5819_ = lean_ctor_get(v_x_5816_, 1);
lean_inc(v_snd_5819_);
lean_dec_ref(v_x_5816_);
v___x_5820_ = lean_apply_2(v_h__1_5817_, v_fst_5818_, v_snd_5819_);
return v___x_5820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5821_, lean_object* v_x_5822_, lean_object* v_h__1_5823_){
_start:
{
lean_object* v_fst_5824_; lean_object* v_snd_5825_; lean_object* v___x_5826_; 
v_fst_5824_ = lean_ctor_get(v_x_5822_, 0);
lean_inc(v_fst_5824_);
v_snd_5825_ = lean_ctor_get(v_x_5822_, 1);
lean_inc(v_snd_5825_);
lean_dec_ref(v_x_5822_);
v___x_5826_ = lean_apply_2(v_h__1_5823_, v_fst_5824_, v_snd_5825_);
return v___x_5826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5827_, lean_object* v_inst_5828_, lean_object* v_inst_5829_, lean_object* v_inst_5830_, lean_object* v_x_5831_, lean_object* v___y_5832_){
_start:
{
lean_object* v___x_5833_; 
v___x_5833_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5827_, v_inst_5828_, v_inst_5829_, v_inst_5830_, v___y_5832_);
return v___x_5833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5834_, lean_object* v_toPure_5835_, lean_object* v_____r_5836_){
_start:
{
lean_object* v_tree_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
v_tree_5837_ = lean_ctor_get(v_r_5834_, 0);
lean_inc_ref(v_tree_5837_);
lean_dec_ref(v_r_5834_);
v___x_5838_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5837_);
v___x_5839_ = lean_apply_2(v_toPure_5835_, lean_box(0), v___x_5838_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5840_, lean_object* v___x_5841_, lean_object* v_toPure_5842_, lean_object* v_toBind_5843_, lean_object* v_inst_5844_, lean_object* v___f_5845_, lean_object* v_tasks_5846_){
_start:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v_r_5852_; lean_object* v_errors_5853_; lean_object* v___f_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; uint8_t v___x_5857_; 
v___x_5847_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5840_);
v___x_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5848_, 0, v___x_5840_);
lean_ctor_set(v___x_5848_, 1, v___x_5847_);
v___x_5849_ = lean_mk_empty_array_with_capacity(v___x_5840_);
lean_inc_ref(v___x_5849_);
v___x_5850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5850_, 0, v___x_5848_);
lean_ctor_set(v___x_5850_, 1, v___x_5849_);
v___x_5851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5851_, 0, v___x_5850_);
lean_ctor_set(v___x_5851_, 1, v___x_5849_);
v_r_5852_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5841_, v___x_5851_, v_tasks_5846_);
v_errors_5853_ = lean_ctor_get(v_r_5852_, 1);
lean_inc_ref(v_errors_5853_);
lean_inc(v_toPure_5842_);
v___f_5854_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5854_, 0, v_r_5852_);
lean_closure_set(v___f_5854_, 1, v_toPure_5842_);
v___x_5855_ = lean_array_get_size(v_errors_5853_);
v___x_5856_ = lean_box(0);
v___x_5857_ = lean_nat_dec_lt(v___x_5840_, v___x_5855_);
lean_dec(v___x_5840_);
if (v___x_5857_ == 0)
{
lean_object* v___x_5858_; lean_object* v___x_5859_; 
lean_dec_ref(v_errors_5853_);
lean_dec(v___f_5845_);
lean_dec_ref(v_inst_5844_);
v___x_5858_ = lean_apply_2(v_toPure_5842_, lean_box(0), v___x_5856_);
v___x_5859_ = lean_apply_4(v_toBind_5843_, lean_box(0), lean_box(0), v___x_5858_, v___f_5854_);
return v___x_5859_;
}
else
{
uint8_t v___x_5860_; 
v___x_5860_ = lean_nat_dec_le(v___x_5855_, v___x_5855_);
if (v___x_5860_ == 0)
{
if (v___x_5857_ == 0)
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
lean_dec_ref(v_errors_5853_);
lean_dec(v___f_5845_);
lean_dec_ref(v_inst_5844_);
v___x_5861_ = lean_apply_2(v_toPure_5842_, lean_box(0), v___x_5856_);
v___x_5862_ = lean_apply_4(v_toBind_5843_, lean_box(0), lean_box(0), v___x_5861_, v___f_5854_);
return v___x_5862_;
}
else
{
size_t v___x_5863_; size_t v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; 
lean_dec(v_toPure_5842_);
v___x_5863_ = ((size_t)0ULL);
v___x_5864_ = lean_usize_of_nat(v___x_5855_);
v___x_5865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5844_, v___f_5845_, v_errors_5853_, v___x_5863_, v___x_5864_, v___x_5856_);
v___x_5866_ = lean_apply_4(v_toBind_5843_, lean_box(0), lean_box(0), v___x_5865_, v___f_5854_);
return v___x_5866_;
}
}
else
{
size_t v___x_5867_; size_t v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
lean_dec(v_toPure_5842_);
v___x_5867_ = ((size_t)0ULL);
v___x_5868_ = lean_usize_of_nat(v___x_5855_);
v___x_5869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5844_, v___f_5845_, v_errors_5853_, v___x_5867_, v___x_5868_, v___x_5856_);
v___x_5870_ = lean_apply_4(v_toBind_5843_, lean_box(0), lean_box(0), v___x_5869_, v___f_5854_);
return v___x_5870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5873_, lean_object* v_inst_5874_, lean_object* v_inst_5875_, lean_object* v_inst_5876_, lean_object* v_inst_5877_, lean_object* v_cctx_5878_, lean_object* v_ngen_5879_, lean_object* v_env_5880_, lean_object* v_act_5881_, lean_object* v_constantsPerTask_5882_){
_start:
{
lean_object* v___x_5883_; lean_object* v_moduleData_5884_; lean_object* v_toApplicative_5885_; lean_object* v_toBind_5886_; lean_object* v_n_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v_toPure_5891_; lean_object* v___f_5892_; lean_object* v___x_5893_; lean_object* v___f_5894_; lean_object* v___x_5895_; 
v___x_5883_ = l_Lean_Environment_header(v_env_5880_);
v_moduleData_5884_ = lean_ctor_get(v___x_5883_, 6);
lean_inc_ref(v_moduleData_5884_);
lean_dec_ref(v___x_5883_);
v_toApplicative_5885_ = lean_ctor_get(v_inst_5873_, 0);
v_toBind_5886_ = lean_ctor_get(v_inst_5873_, 1);
lean_inc_n(v_toBind_5886_, 2);
v_n_5887_ = lean_array_get_size(v_moduleData_5884_);
lean_dec_ref(v_moduleData_5884_);
v___x_5888_ = lean_unsigned_to_nat(0u);
v___x_5889_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5873_, 2);
v___x_5890_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5873_, v_inst_5877_, v_cctx_5878_, v_env_5880_, v_act_5881_, v_constantsPerTask_5882_, v_n_5887_, v_ngen_5879_, v___x_5889_, v___x_5888_, v___x_5888_, v___x_5888_);
v_toPure_5891_ = lean_ctor_get(v_toApplicative_5885_, 1);
lean_inc(v_toPure_5891_);
v___f_5892_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5892_, 0, v_inst_5873_);
lean_closure_set(v___f_5892_, 1, v_inst_5874_);
lean_closure_set(v___f_5892_, 2, v_inst_5875_);
lean_closure_set(v___f_5892_, 3, v_inst_5876_);
v___x_5893_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_5894_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5894_, 0, v___x_5888_);
lean_closure_set(v___f_5894_, 1, v___x_5893_);
lean_closure_set(v___f_5894_, 2, v_toPure_5891_);
lean_closure_set(v___f_5894_, 3, v_toBind_5886_);
lean_closure_set(v___f_5894_, 4, v_inst_5873_);
lean_closure_set(v___f_5894_, 5, v___f_5892_);
v___x_5895_ = lean_apply_4(v_toBind_5886_, lean_box(0), lean_box(0), v___x_5890_, v___f_5894_);
return v___x_5895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5896_, lean_object* v_00_u03b1_5897_, lean_object* v_inst_5898_, lean_object* v_inst_5899_, lean_object* v_inst_5900_, lean_object* v_inst_5901_, lean_object* v_inst_5902_, lean_object* v_cctx_5903_, lean_object* v_ngen_5904_, lean_object* v_env_5905_, lean_object* v_act_5906_, lean_object* v_constantsPerTask_5907_){
_start:
{
lean_object* v___x_5908_; 
v___x_5908_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5898_, v_inst_5899_, v_inst_5900_, v_inst_5901_, v_inst_5902_, v_cctx_5903_, v_ngen_5904_, v_env_5905_, v_act_5906_, v_constantsPerTask_5907_);
return v___x_5908_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5909_ = lean_box(0);
v___x_5910_ = lean_unsigned_to_nat(16u);
v___x_5911_ = lean_mk_array(v___x_5910_, v___x_5909_);
return v___x_5911_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5912_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5913_ = lean_unsigned_to_nat(0u);
v___x_5914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5913_);
lean_ctor_set(v___x_5914_, 1, v___x_5912_);
return v___x_5914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5915_){
_start:
{
lean_object* v_fileName_5916_; lean_object* v_fileMap_5917_; lean_object* v_options_5918_; lean_object* v_maxRecDepth_5919_; lean_object* v_ref_5920_; lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5935_; 
v_fileName_5916_ = lean_ctor_get(v_ctx_5915_, 0);
v_fileMap_5917_ = lean_ctor_get(v_ctx_5915_, 1);
v_options_5918_ = lean_ctor_get(v_ctx_5915_, 2);
v_maxRecDepth_5919_ = lean_ctor_get(v_ctx_5915_, 4);
v_ref_5920_ = lean_ctor_get(v_ctx_5915_, 5);
v_isSharedCheck_5935_ = !lean_is_exclusive(v_ctx_5915_);
if (v_isSharedCheck_5935_ == 0)
{
lean_object* v_unused_5936_; lean_object* v_unused_5937_; lean_object* v_unused_5938_; lean_object* v_unused_5939_; lean_object* v_unused_5940_; lean_object* v_unused_5941_; lean_object* v_unused_5942_; lean_object* v_unused_5943_; lean_object* v_unused_5944_; 
v_unused_5936_ = lean_ctor_get(v_ctx_5915_, 13);
lean_dec(v_unused_5936_);
v_unused_5937_ = lean_ctor_get(v_ctx_5915_, 12);
lean_dec(v_unused_5937_);
v_unused_5938_ = lean_ctor_get(v_ctx_5915_, 11);
lean_dec(v_unused_5938_);
v_unused_5939_ = lean_ctor_get(v_ctx_5915_, 10);
lean_dec(v_unused_5939_);
v_unused_5940_ = lean_ctor_get(v_ctx_5915_, 9);
lean_dec(v_unused_5940_);
v_unused_5941_ = lean_ctor_get(v_ctx_5915_, 8);
lean_dec(v_unused_5941_);
v_unused_5942_ = lean_ctor_get(v_ctx_5915_, 7);
lean_dec(v_unused_5942_);
v_unused_5943_ = lean_ctor_get(v_ctx_5915_, 6);
lean_dec(v_unused_5943_);
v_unused_5944_ = lean_ctor_get(v_ctx_5915_, 3);
lean_dec(v_unused_5944_);
v___x_5922_ = v_ctx_5915_;
v_isShared_5923_ = v_isSharedCheck_5935_;
goto v_resetjp_5921_;
}
else
{
lean_inc(v_ref_5920_);
lean_inc(v_maxRecDepth_5919_);
lean_inc(v_options_5918_);
lean_inc(v_fileMap_5917_);
lean_inc(v_fileName_5916_);
lean_dec(v_ctx_5915_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5935_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; uint8_t v___x_5928_; lean_object* v___x_5929_; uint8_t v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5933_; 
v___x_5924_ = lean_unsigned_to_nat(0u);
v___x_5925_ = lean_box(0);
v___x_5926_ = lean_box(0);
v___x_5927_ = l_Lean_firstFrontendMacroScope;
v___x_5928_ = l_Lean_getDiag(v_options_5918_);
v___x_5929_ = lean_box(0);
v___x_5930_ = 0;
v___x_5931_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 13, v___x_5931_);
lean_ctor_set(v___x_5922_, 12, v___x_5929_);
lean_ctor_set(v___x_5922_, 11, v___x_5927_);
lean_ctor_set(v___x_5922_, 10, v___x_5925_);
lean_ctor_set(v___x_5922_, 9, v___x_5924_);
lean_ctor_set(v___x_5922_, 8, v___x_5924_);
lean_ctor_set(v___x_5922_, 7, v___x_5926_);
lean_ctor_set(v___x_5922_, 6, v___x_5925_);
lean_ctor_set(v___x_5922_, 3, v___x_5924_);
v___x_5933_ = v___x_5922_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_fileName_5916_);
lean_ctor_set(v_reuseFailAlloc_5934_, 1, v_fileMap_5917_);
lean_ctor_set(v_reuseFailAlloc_5934_, 2, v_options_5918_);
lean_ctor_set(v_reuseFailAlloc_5934_, 3, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5934_, 4, v_maxRecDepth_5919_);
lean_ctor_set(v_reuseFailAlloc_5934_, 5, v_ref_5920_);
lean_ctor_set(v_reuseFailAlloc_5934_, 6, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5934_, 7, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5934_, 8, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5934_, 9, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5934_, 10, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5934_, 11, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_5934_, 12, v___x_5929_);
lean_ctor_set(v_reuseFailAlloc_5934_, 13, v___x_5931_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*14, v___x_5928_);
lean_ctor_set_uint8(v___x_5933_, sizeof(void*)*14 + 1, v___x_5930_);
return v___x_5933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5945_, lean_object* v_opts_5946_, lean_object* v_act_5947_, lean_object* v_decl_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; 
lean_inc(v___y_5952_);
lean_inc_ref(v___y_5951_);
lean_inc(v___y_5950_);
lean_inc_ref(v___y_5949_);
v___x_5954_ = lean_apply_4(v_act_5947_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
v___x_5955_ = l_Lean_profileitIOUnsafe___redArg(v_category_5945_, v_opts_5946_, v___x_5954_, v_decl_5948_);
return v___x_5955_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5956_, lean_object* v_opts_5957_, lean_object* v_act_5958_, lean_object* v_decl_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_){
_start:
{
lean_object* v_res_5965_; 
v_res_5965_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5956_, v_opts_5957_, v_act_5958_, v_decl_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_);
lean_dec(v___y_5963_);
lean_dec_ref(v___y_5962_);
lean_dec(v___y_5961_);
lean_dec_ref(v___y_5960_);
lean_dec_ref(v_opts_5957_);
lean_dec_ref(v_category_5956_);
return v_res_5965_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_5966_, lean_object* v_category_5967_, lean_object* v_opts_5968_, lean_object* v_act_5969_, lean_object* v_decl_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v___y_5974_){
_start:
{
lean_object* v___x_5976_; 
v___x_5976_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5967_, v_opts_5968_, v_act_5969_, v_decl_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_);
return v___x_5976_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_5977_, lean_object* v_category_5978_, lean_object* v_opts_5979_, lean_object* v_act_5980_, lean_object* v_decl_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_){
_start:
{
lean_object* v_res_5987_; 
v_res_5987_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_5977_, v_category_5978_, v_opts_5979_, v_act_5980_, v_decl_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
lean_dec(v___y_5983_);
lean_dec_ref(v___y_5982_);
lean_dec_ref(v_opts_5979_);
lean_dec_ref(v_category_5978_);
return v_res_5987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_5988_, lean_object* v_env_5989_, lean_object* v_act_5990_, lean_object* v_constantsPerTask_5991_, lean_object* v_n_5992_, lean_object* v_ngen_5993_, lean_object* v_tasks_5994_, lean_object* v_start_5995_, lean_object* v_cnt_5996_, lean_object* v_idx_5997_){
_start:
{
lean_object* v___x_5999_; lean_object* v_moduleData_6000_; lean_object* v___x_6001_; uint8_t v___x_6002_; 
v___x_5999_ = l_Lean_Environment_header(v_env_5989_);
v_moduleData_6000_ = lean_ctor_get(v___x_5999_, 6);
lean_inc_ref(v_moduleData_6000_);
lean_dec_ref(v___x_5999_);
v___x_6001_ = lean_array_get_size(v_moduleData_6000_);
v___x_6002_ = lean_nat_dec_lt(v_idx_5997_, v___x_6001_);
if (v___x_6002_ == 0)
{
uint8_t v___x_6003_; 
lean_dec_ref(v_moduleData_6000_);
lean_dec(v_idx_5997_);
lean_dec(v_cnt_5996_);
v___x_6003_ = lean_nat_dec_lt(v_start_5995_, v_n_5992_);
if (v___x_6003_ == 0)
{
lean_object* v___x_6004_; 
lean_dec(v_start_5995_);
lean_dec_ref(v_ngen_5993_);
lean_dec(v_n_5992_);
lean_dec_ref(v_act_5990_);
lean_dec_ref(v_env_5989_);
lean_dec_ref(v_cctx_5988_);
v___x_6004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6004_, 0, v_tasks_5994_);
return v___x_6004_;
}
else
{
lean_object* v_namePrefix_6005_; lean_object* v_idx_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6020_; 
v_namePrefix_6005_ = lean_ctor_get(v_ngen_5993_, 0);
v_idx_6006_ = lean_ctor_get(v_ngen_5993_, 1);
v_isSharedCheck_6020_ = !lean_is_exclusive(v_ngen_5993_);
if (v_isSharedCheck_6020_ == 0)
{
v___x_6008_ = v_ngen_5993_;
v_isShared_6009_ = v_isSharedCheck_6020_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_idx_6006_);
lean_inc(v_namePrefix_6005_);
lean_dec(v_ngen_5993_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6020_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6013_; 
v___x_6010_ = l_Lean_Name_num___override(v_namePrefix_6005_, v_idx_6006_);
v___x_6011_ = lean_unsigned_to_nat(1u);
if (v_isShared_6009_ == 0)
{
lean_ctor_set(v___x_6008_, 1, v___x_6011_);
lean_ctor_set(v___x_6008_, 0, v___x_6010_);
v___x_6013_ = v___x_6008_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6019_; 
v_reuseFailAlloc_6019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6019_, 0, v___x_6010_);
lean_ctor_set(v_reuseFailAlloc_6019_, 1, v___x_6011_);
v___x_6013_ = v_reuseFailAlloc_6019_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6014_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6014_, 0, lean_box(0));
lean_closure_set(v___x_6014_, 1, v_cctx_5988_);
lean_closure_set(v___x_6014_, 2, v___x_6013_);
lean_closure_set(v___x_6014_, 3, v_env_5989_);
lean_closure_set(v___x_6014_, 4, v_act_5990_);
lean_closure_set(v___x_6014_, 5, v_start_5995_);
lean_closure_set(v___x_6014_, 6, v_n_5992_);
v___x_6015_ = lean_unsigned_to_nat(0u);
v___x_6016_ = lean_io_as_task(v___x_6014_, v___x_6015_);
v___x_6017_ = lean_array_push(v_tasks_5994_, v___x_6016_);
v___x_6018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6017_);
return v___x_6018_;
}
}
}
}
else
{
lean_object* v_mdata_6021_; lean_object* v_constants_6022_; lean_object* v___x_6023_; lean_object* v_cnt_6024_; uint8_t v___x_6025_; 
v_mdata_6021_ = lean_array_fget(v_moduleData_6000_, v_idx_5997_);
lean_dec_ref(v_moduleData_6000_);
v_constants_6022_ = lean_ctor_get(v_mdata_6021_, 2);
lean_inc_ref(v_constants_6022_);
lean_dec(v_mdata_6021_);
v___x_6023_ = lean_array_get_size(v_constants_6022_);
lean_dec_ref(v_constants_6022_);
v_cnt_6024_ = lean_nat_add(v_cnt_5996_, v___x_6023_);
lean_dec(v_cnt_5996_);
v___x_6025_ = lean_nat_dec_lt(v_constantsPerTask_5991_, v_cnt_6024_);
if (v___x_6025_ == 0)
{
lean_object* v___x_6026_; lean_object* v___x_6027_; 
v___x_6026_ = lean_unsigned_to_nat(1u);
v___x_6027_ = lean_nat_add(v_idx_5997_, v___x_6026_);
lean_dec(v_idx_5997_);
v_cnt_5996_ = v_cnt_6024_;
v_idx_5997_ = v___x_6027_;
goto _start;
}
else
{
lean_object* v_namePrefix_6029_; lean_object* v_idx_6030_; lean_object* v___x_6032_; uint8_t v_isShared_6033_; uint8_t v_isSharedCheck_6047_; 
lean_dec(v_cnt_6024_);
v_namePrefix_6029_ = lean_ctor_get(v_ngen_5993_, 0);
v_idx_6030_ = lean_ctor_get(v_ngen_5993_, 1);
v_isSharedCheck_6047_ = !lean_is_exclusive(v_ngen_5993_);
if (v_isSharedCheck_6047_ == 0)
{
v___x_6032_ = v_ngen_5993_;
v_isShared_6033_ = v_isSharedCheck_6047_;
goto v_resetjp_6031_;
}
else
{
lean_inc(v_idx_6030_);
lean_inc(v_namePrefix_6029_);
lean_dec(v_ngen_5993_);
v___x_6032_ = lean_box(0);
v_isShared_6033_ = v_isSharedCheck_6047_;
goto v_resetjp_6031_;
}
v_resetjp_6031_:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6037_; 
lean_inc(v_idx_6030_);
lean_inc(v_namePrefix_6029_);
v___x_6034_ = l_Lean_Name_num___override(v_namePrefix_6029_, v_idx_6030_);
v___x_6035_ = lean_unsigned_to_nat(1u);
if (v_isShared_6033_ == 0)
{
lean_ctor_set(v___x_6032_, 1, v___x_6035_);
lean_ctor_set(v___x_6032_, 0, v___x_6034_);
v___x_6037_ = v___x_6032_;
goto v_reusejp_6036_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v___x_6034_);
lean_ctor_set(v_reuseFailAlloc_6046_, 1, v___x_6035_);
v___x_6037_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6036_;
}
v_reusejp_6036_:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6038_ = lean_nat_add(v_idx_5997_, v___x_6035_);
lean_dec(v_idx_5997_);
lean_inc_n(v___x_6038_, 2);
lean_inc_ref(v_act_5990_);
lean_inc_ref(v_env_5989_);
lean_inc_ref(v_cctx_5988_);
v___x_6039_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6039_, 0, lean_box(0));
lean_closure_set(v___x_6039_, 1, v_cctx_5988_);
lean_closure_set(v___x_6039_, 2, v___x_6037_);
lean_closure_set(v___x_6039_, 3, v_env_5989_);
lean_closure_set(v___x_6039_, 4, v_act_5990_);
lean_closure_set(v___x_6039_, 5, v_start_5995_);
lean_closure_set(v___x_6039_, 6, v___x_6038_);
v___x_6040_ = lean_unsigned_to_nat(0u);
v___x_6041_ = lean_io_as_task(v___x_6039_, v___x_6040_);
v___x_6042_ = lean_nat_add(v_idx_6030_, v___x_6035_);
lean_dec(v_idx_6030_);
v___x_6043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6043_, 0, v_namePrefix_6029_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = lean_array_push(v_tasks_5994_, v___x_6041_);
v_ngen_5993_ = v___x_6043_;
v_tasks_5994_ = v___x_6044_;
v_start_5995_ = v___x_6038_;
v_cnt_5996_ = v___x_6040_;
v_idx_5997_ = v___x_6038_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6048_, lean_object* v_env_6049_, lean_object* v_act_6050_, lean_object* v_constantsPerTask_6051_, lean_object* v_n_6052_, lean_object* v_ngen_6053_, lean_object* v_tasks_6054_, lean_object* v_start_6055_, lean_object* v_cnt_6056_, lean_object* v_idx_6057_, lean_object* v___y_6058_){
_start:
{
lean_object* v_res_6059_; 
v_res_6059_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6048_, v_env_6049_, v_act_6050_, v_constantsPerTask_6051_, v_n_6052_, v_ngen_6053_, v_tasks_6054_, v_start_6055_, v_cnt_6056_, v_idx_6057_);
lean_dec(v_constantsPerTask_6051_);
return v_res_6059_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v___y_6068_, uint8_t v_suppressElabErrors_6069_, lean_object* v_x_6070_){
_start:
{
if (lean_obj_tag(v_x_6070_) == 1)
{
lean_object* v_pre_6071_; 
v_pre_6071_ = lean_ctor_get(v_x_6070_, 0);
switch(lean_obj_tag(v_pre_6071_))
{
case 1:
{
lean_object* v_pre_6072_; 
v_pre_6072_ = lean_ctor_get(v_pre_6071_, 0);
switch(lean_obj_tag(v_pre_6072_))
{
case 0:
{
lean_object* v_str_6073_; lean_object* v_str_6074_; lean_object* v___x_6075_; uint8_t v___x_6076_; 
v_str_6073_ = lean_ctor_get(v_x_6070_, 1);
v_str_6074_ = lean_ctor_get(v_pre_6071_, 1);
v___x_6075_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6076_ = lean_string_dec_eq(v_str_6074_, v___x_6075_);
if (v___x_6076_ == 0)
{
lean_object* v___x_6077_; uint8_t v___x_6078_; 
v___x_6077_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6078_ = lean_string_dec_eq(v_str_6074_, v___x_6077_);
if (v___x_6078_ == 0)
{
return v___y_6068_;
}
else
{
lean_object* v___x_6079_; uint8_t v___x_6080_; 
v___x_6079_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6080_ = lean_string_dec_eq(v_str_6073_, v___x_6079_);
if (v___x_6080_ == 0)
{
return v___y_6068_;
}
else
{
return v_suppressElabErrors_6069_;
}
}
}
else
{
lean_object* v___x_6081_; uint8_t v___x_6082_; 
v___x_6081_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6082_ = lean_string_dec_eq(v_str_6073_, v___x_6081_);
if (v___x_6082_ == 0)
{
return v___y_6068_;
}
else
{
return v_suppressElabErrors_6069_;
}
}
}
case 1:
{
lean_object* v_pre_6083_; 
v_pre_6083_ = lean_ctor_get(v_pre_6072_, 0);
if (lean_obj_tag(v_pre_6083_) == 0)
{
lean_object* v_str_6084_; lean_object* v_str_6085_; lean_object* v_str_6086_; lean_object* v___x_6087_; uint8_t v___x_6088_; 
v_str_6084_ = lean_ctor_get(v_x_6070_, 1);
v_str_6085_ = lean_ctor_get(v_pre_6071_, 1);
v_str_6086_ = lean_ctor_get(v_pre_6072_, 1);
v___x_6087_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6088_ = lean_string_dec_eq(v_str_6086_, v___x_6087_);
if (v___x_6088_ == 0)
{
return v___y_6068_;
}
else
{
lean_object* v___x_6089_; uint8_t v___x_6090_; 
v___x_6089_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6090_ = lean_string_dec_eq(v_str_6085_, v___x_6089_);
if (v___x_6090_ == 0)
{
return v___y_6068_;
}
else
{
lean_object* v___x_6091_; uint8_t v___x_6092_; 
v___x_6091_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6092_ = lean_string_dec_eq(v_str_6084_, v___x_6091_);
if (v___x_6092_ == 0)
{
return v___y_6068_;
}
else
{
return v_suppressElabErrors_6069_;
}
}
}
}
else
{
return v___y_6068_;
}
}
default: 
{
return v___y_6068_;
}
}
}
case 0:
{
lean_object* v_str_6093_; lean_object* v___x_6094_; uint8_t v___x_6095_; 
v_str_6093_ = lean_ctor_get(v_x_6070_, 1);
v___x_6094_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6095_ = lean_string_dec_eq(v_str_6093_, v___x_6094_);
if (v___x_6095_ == 0)
{
return v___y_6068_;
}
else
{
return v_suppressElabErrors_6069_;
}
}
default: 
{
return v___y_6068_;
}
}
}
else
{
return v___y_6068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v___y_6096_, lean_object* v_suppressElabErrors_6097_, lean_object* v_x_6098_){
_start:
{
uint8_t v___y_7861__boxed_6099_; uint8_t v_suppressElabErrors_boxed_6100_; uint8_t v_res_6101_; lean_object* v_r_6102_; 
v___y_7861__boxed_6099_ = lean_unbox(v___y_6096_);
v_suppressElabErrors_boxed_6100_ = lean_unbox(v_suppressElabErrors_6097_);
v_res_6101_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v___y_7861__boxed_6099_, v_suppressElabErrors_boxed_6100_, v_x_6098_);
lean_dec(v_x_6098_);
v_r_6102_ = lean_box(v_res_6101_);
return v_r_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6104_, lean_object* v_msgData_6105_, uint8_t v_severity_6106_, uint8_t v_isSilent_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_){
_start:
{
uint8_t v___y_6114_; lean_object* v___y_6115_; uint8_t v___y_6116_; lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; lean_object* v___y_6121_; lean_object* v___y_6122_; lean_object* v___y_6150_; uint8_t v___y_6151_; uint8_t v___y_6152_; uint8_t v___y_6153_; lean_object* v___y_6154_; lean_object* v___y_6155_; lean_object* v___y_6156_; lean_object* v___y_6157_; lean_object* v___y_6175_; lean_object* v___y_6176_; uint8_t v___y_6177_; uint8_t v___y_6178_; lean_object* v___y_6179_; uint8_t v___y_6180_; lean_object* v___y_6181_; lean_object* v___y_6182_; lean_object* v___y_6186_; uint8_t v___y_6187_; uint8_t v___y_6188_; lean_object* v___y_6189_; lean_object* v___y_6190_; lean_object* v___y_6191_; uint8_t v___y_6192_; uint8_t v___x_6197_; lean_object* v___y_6199_; uint8_t v___y_6200_; lean_object* v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6203_; uint8_t v___y_6204_; uint8_t v___y_6205_; uint8_t v___y_6207_; uint8_t v___x_6222_; 
v___x_6197_ = 2;
v___x_6222_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6106_, v___x_6197_);
if (v___x_6222_ == 0)
{
v___y_6207_ = v___x_6222_;
goto v___jp_6206_;
}
else
{
uint8_t v___x_6223_; 
lean_inc_ref(v_msgData_6105_);
v___x_6223_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6105_);
v___y_6207_ = v___x_6223_;
goto v___jp_6206_;
}
v___jp_6113_:
{
lean_object* v___x_6123_; lean_object* v_currNamespace_6124_; lean_object* v_openDecls_6125_; lean_object* v_env_6126_; lean_object* v_nextMacroScope_6127_; lean_object* v_ngen_6128_; lean_object* v_auxDeclNGen_6129_; lean_object* v_traceState_6130_; lean_object* v_cache_6131_; lean_object* v_messages_6132_; lean_object* v_infoState_6133_; lean_object* v_snapshotTasks_6134_; lean_object* v___x_6136_; uint8_t v_isShared_6137_; uint8_t v_isSharedCheck_6148_; 
v___x_6123_ = lean_st_ref_take(v___y_6122_);
v_currNamespace_6124_ = lean_ctor_get(v___y_6121_, 6);
v_openDecls_6125_ = lean_ctor_get(v___y_6121_, 7);
v_env_6126_ = lean_ctor_get(v___x_6123_, 0);
v_nextMacroScope_6127_ = lean_ctor_get(v___x_6123_, 1);
v_ngen_6128_ = lean_ctor_get(v___x_6123_, 2);
v_auxDeclNGen_6129_ = lean_ctor_get(v___x_6123_, 3);
v_traceState_6130_ = lean_ctor_get(v___x_6123_, 4);
v_cache_6131_ = lean_ctor_get(v___x_6123_, 5);
v_messages_6132_ = lean_ctor_get(v___x_6123_, 6);
v_infoState_6133_ = lean_ctor_get(v___x_6123_, 7);
v_snapshotTasks_6134_ = lean_ctor_get(v___x_6123_, 8);
v_isSharedCheck_6148_ = !lean_is_exclusive(v___x_6123_);
if (v_isSharedCheck_6148_ == 0)
{
v___x_6136_ = v___x_6123_;
v_isShared_6137_ = v_isSharedCheck_6148_;
goto v_resetjp_6135_;
}
else
{
lean_inc(v_snapshotTasks_6134_);
lean_inc(v_infoState_6133_);
lean_inc(v_messages_6132_);
lean_inc(v_cache_6131_);
lean_inc(v_traceState_6130_);
lean_inc(v_auxDeclNGen_6129_);
lean_inc(v_ngen_6128_);
lean_inc(v_nextMacroScope_6127_);
lean_inc(v_env_6126_);
lean_dec(v___x_6123_);
v___x_6136_ = lean_box(0);
v_isShared_6137_ = v_isSharedCheck_6148_;
goto v_resetjp_6135_;
}
v_resetjp_6135_:
{
lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6143_; 
lean_inc(v_openDecls_6125_);
lean_inc(v_currNamespace_6124_);
v___x_6138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6138_, 0, v_currNamespace_6124_);
lean_ctor_set(v___x_6138_, 1, v_openDecls_6125_);
v___x_6139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
lean_ctor_set(v___x_6139_, 1, v___y_6117_);
lean_inc_ref(v___y_6115_);
lean_inc_ref(v___y_6119_);
v___x_6140_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6140_, 0, v___y_6119_);
lean_ctor_set(v___x_6140_, 1, v___y_6120_);
lean_ctor_set(v___x_6140_, 2, v___y_6118_);
lean_ctor_set(v___x_6140_, 3, v___y_6115_);
lean_ctor_set(v___x_6140_, 4, v___x_6139_);
lean_ctor_set_uint8(v___x_6140_, sizeof(void*)*5, v___y_6116_);
lean_ctor_set_uint8(v___x_6140_, sizeof(void*)*5 + 1, v___y_6114_);
lean_ctor_set_uint8(v___x_6140_, sizeof(void*)*5 + 2, v_isSilent_6107_);
v___x_6141_ = l_Lean_MessageLog_add(v___x_6140_, v_messages_6132_);
if (v_isShared_6137_ == 0)
{
lean_ctor_set(v___x_6136_, 6, v___x_6141_);
v___x_6143_ = v___x_6136_;
goto v_reusejp_6142_;
}
else
{
lean_object* v_reuseFailAlloc_6147_; 
v_reuseFailAlloc_6147_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6147_, 0, v_env_6126_);
lean_ctor_set(v_reuseFailAlloc_6147_, 1, v_nextMacroScope_6127_);
lean_ctor_set(v_reuseFailAlloc_6147_, 2, v_ngen_6128_);
lean_ctor_set(v_reuseFailAlloc_6147_, 3, v_auxDeclNGen_6129_);
lean_ctor_set(v_reuseFailAlloc_6147_, 4, v_traceState_6130_);
lean_ctor_set(v_reuseFailAlloc_6147_, 5, v_cache_6131_);
lean_ctor_set(v_reuseFailAlloc_6147_, 6, v___x_6141_);
lean_ctor_set(v_reuseFailAlloc_6147_, 7, v_infoState_6133_);
lean_ctor_set(v_reuseFailAlloc_6147_, 8, v_snapshotTasks_6134_);
v___x_6143_ = v_reuseFailAlloc_6147_;
goto v_reusejp_6142_;
}
v_reusejp_6142_:
{
lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; 
v___x_6144_ = lean_st_ref_set(v___y_6122_, v___x_6143_);
v___x_6145_ = lean_box(0);
v___x_6146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6145_);
return v___x_6146_;
}
}
}
v___jp_6149_:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v_a_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6173_; 
v___x_6158_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6105_);
v___x_6159_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6158_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_);
v_a_6160_ = lean_ctor_get(v___x_6159_, 0);
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6159_);
if (v_isSharedCheck_6173_ == 0)
{
v___x_6162_ = v___x_6159_;
v_isShared_6163_ = v_isSharedCheck_6173_;
goto v_resetjp_6161_;
}
else
{
lean_inc(v_a_6160_);
lean_dec(v___x_6159_);
v___x_6162_ = lean_box(0);
v_isShared_6163_ = v_isSharedCheck_6173_;
goto v_resetjp_6161_;
}
v_resetjp_6161_:
{
lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; 
lean_inc_ref_n(v___y_6154_, 2);
v___x_6164_ = l_Lean_FileMap_toPosition(v___y_6154_, v___y_6155_);
lean_dec(v___y_6155_);
v___x_6165_ = l_Lean_FileMap_toPosition(v___y_6154_, v___y_6157_);
lean_dec(v___y_6157_);
v___x_6166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
v___x_6167_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6153_ == 0)
{
lean_del_object(v___x_6162_);
lean_dec_ref(v___y_6150_);
v___y_6114_ = v___y_6151_;
v___y_6115_ = v___x_6167_;
v___y_6116_ = v___y_6152_;
v___y_6117_ = v_a_6160_;
v___y_6118_ = v___x_6166_;
v___y_6119_ = v___y_6156_;
v___y_6120_ = v___x_6164_;
v___y_6121_ = v___y_6110_;
v___y_6122_ = v___y_6111_;
goto v___jp_6113_;
}
else
{
uint8_t v___x_6168_; 
lean_inc(v_a_6160_);
v___x_6168_ = l_Lean_MessageData_hasTag(v___y_6150_, v_a_6160_);
if (v___x_6168_ == 0)
{
lean_object* v___x_6169_; lean_object* v___x_6171_; 
lean_dec_ref_known(v___x_6166_, 1);
lean_dec_ref(v___x_6164_);
lean_dec(v_a_6160_);
v___x_6169_ = lean_box(0);
if (v_isShared_6163_ == 0)
{
lean_ctor_set(v___x_6162_, 0, v___x_6169_);
v___x_6171_ = v___x_6162_;
goto v_reusejp_6170_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v___x_6169_);
v___x_6171_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6170_;
}
v_reusejp_6170_:
{
return v___x_6171_;
}
}
else
{
lean_del_object(v___x_6162_);
v___y_6114_ = v___y_6151_;
v___y_6115_ = v___x_6167_;
v___y_6116_ = v___y_6152_;
v___y_6117_ = v_a_6160_;
v___y_6118_ = v___x_6166_;
v___y_6119_ = v___y_6156_;
v___y_6120_ = v___x_6164_;
v___y_6121_ = v___y_6110_;
v___y_6122_ = v___y_6111_;
goto v___jp_6113_;
}
}
}
}
v___jp_6174_:
{
lean_object* v___x_6183_; 
v___x_6183_ = l_Lean_Syntax_getTailPos_x3f(v___y_6176_, v___y_6178_);
lean_dec(v___y_6176_);
if (lean_obj_tag(v___x_6183_) == 0)
{
lean_inc(v___y_6182_);
v___y_6150_ = v___y_6175_;
v___y_6151_ = v___y_6177_;
v___y_6152_ = v___y_6178_;
v___y_6153_ = v___y_6180_;
v___y_6154_ = v___y_6179_;
v___y_6155_ = v___y_6182_;
v___y_6156_ = v___y_6181_;
v___y_6157_ = v___y_6182_;
goto v___jp_6149_;
}
else
{
lean_object* v_val_6184_; 
v_val_6184_ = lean_ctor_get(v___x_6183_, 0);
lean_inc(v_val_6184_);
lean_dec_ref_known(v___x_6183_, 1);
v___y_6150_ = v___y_6175_;
v___y_6151_ = v___y_6177_;
v___y_6152_ = v___y_6178_;
v___y_6153_ = v___y_6180_;
v___y_6154_ = v___y_6179_;
v___y_6155_ = v___y_6182_;
v___y_6156_ = v___y_6181_;
v___y_6157_ = v_val_6184_;
goto v___jp_6149_;
}
}
v___jp_6185_:
{
lean_object* v_ref_6193_; lean_object* v___x_6194_; 
v_ref_6193_ = l_Lean_replaceRef(v_ref_6104_, v___y_6190_);
v___x_6194_ = l_Lean_Syntax_getPos_x3f(v_ref_6193_, v___y_6187_);
if (lean_obj_tag(v___x_6194_) == 0)
{
lean_object* v___x_6195_; 
v___x_6195_ = lean_unsigned_to_nat(0u);
v___y_6175_ = v___y_6186_;
v___y_6176_ = v_ref_6193_;
v___y_6177_ = v___y_6192_;
v___y_6178_ = v___y_6187_;
v___y_6179_ = v___y_6189_;
v___y_6180_ = v___y_6188_;
v___y_6181_ = v___y_6191_;
v___y_6182_ = v___x_6195_;
goto v___jp_6174_;
}
else
{
lean_object* v_val_6196_; 
v_val_6196_ = lean_ctor_get(v___x_6194_, 0);
lean_inc(v_val_6196_);
lean_dec_ref_known(v___x_6194_, 1);
v___y_6175_ = v___y_6186_;
v___y_6176_ = v_ref_6193_;
v___y_6177_ = v___y_6192_;
v___y_6178_ = v___y_6187_;
v___y_6179_ = v___y_6189_;
v___y_6180_ = v___y_6188_;
v___y_6181_ = v___y_6191_;
v___y_6182_ = v_val_6196_;
goto v___jp_6174_;
}
}
v___jp_6198_:
{
if (v___y_6205_ == 0)
{
v___y_6186_ = v___y_6201_;
v___y_6187_ = v___y_6204_;
v___y_6188_ = v___y_6200_;
v___y_6189_ = v___y_6199_;
v___y_6190_ = v___y_6202_;
v___y_6191_ = v___y_6203_;
v___y_6192_ = v_severity_6106_;
goto v___jp_6185_;
}
else
{
v___y_6186_ = v___y_6201_;
v___y_6187_ = v___y_6204_;
v___y_6188_ = v___y_6200_;
v___y_6189_ = v___y_6199_;
v___y_6190_ = v___y_6202_;
v___y_6191_ = v___y_6203_;
v___y_6192_ = v___x_6197_;
goto v___jp_6185_;
}
}
v___jp_6206_:
{
if (v___y_6207_ == 0)
{
lean_object* v_fileName_6208_; lean_object* v_fileMap_6209_; lean_object* v_options_6210_; lean_object* v_ref_6211_; uint8_t v_suppressElabErrors_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___f_6215_; uint8_t v___x_6216_; uint8_t v___x_6217_; 
v_fileName_6208_ = lean_ctor_get(v___y_6110_, 0);
v_fileMap_6209_ = lean_ctor_get(v___y_6110_, 1);
v_options_6210_ = lean_ctor_get(v___y_6110_, 2);
v_ref_6211_ = lean_ctor_get(v___y_6110_, 5);
v_suppressElabErrors_6212_ = lean_ctor_get_uint8(v___y_6110_, sizeof(void*)*14 + 1);
v___x_6213_ = lean_box(v___y_6207_);
v___x_6214_ = lean_box(v_suppressElabErrors_6212_);
v___f_6215_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6215_, 0, v___x_6213_);
lean_closure_set(v___f_6215_, 1, v___x_6214_);
v___x_6216_ = 1;
v___x_6217_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6106_, v___x_6216_);
if (v___x_6217_ == 0)
{
v___y_6199_ = v_fileMap_6209_;
v___y_6200_ = v_suppressElabErrors_6212_;
v___y_6201_ = v___f_6215_;
v___y_6202_ = v_ref_6211_;
v___y_6203_ = v_fileName_6208_;
v___y_6204_ = v___y_6207_;
v___y_6205_ = v___x_6217_;
goto v___jp_6198_;
}
else
{
lean_object* v___x_6218_; uint8_t v___x_6219_; 
v___x_6218_ = l_Lean_warningAsError;
v___x_6219_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6210_, v___x_6218_);
v___y_6199_ = v_fileMap_6209_;
v___y_6200_ = v_suppressElabErrors_6212_;
v___y_6201_ = v___f_6215_;
v___y_6202_ = v_ref_6211_;
v___y_6203_ = v_fileName_6208_;
v___y_6204_ = v___y_6207_;
v___y_6205_ = v___x_6219_;
goto v___jp_6198_;
}
}
else
{
lean_object* v___x_6220_; lean_object* v___x_6221_; 
lean_dec_ref(v_msgData_6105_);
v___x_6220_ = lean_box(0);
v___x_6221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6220_);
return v___x_6221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6224_, lean_object* v_msgData_6225_, lean_object* v_severity_6226_, lean_object* v_isSilent_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_){
_start:
{
uint8_t v_severity_boxed_6233_; uint8_t v_isSilent_boxed_6234_; lean_object* v_res_6235_; 
v_severity_boxed_6233_ = lean_unbox(v_severity_6226_);
v_isSilent_boxed_6234_ = lean_unbox(v_isSilent_6227_);
v_res_6235_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6224_, v_msgData_6225_, v_severity_boxed_6233_, v_isSilent_boxed_6234_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_);
lean_dec(v___y_6231_);
lean_dec_ref(v___y_6230_);
lean_dec(v___y_6229_);
lean_dec_ref(v___y_6228_);
lean_dec(v_ref_6224_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6236_, uint8_t v_severity_6237_, uint8_t v_isSilent_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_){
_start:
{
lean_object* v_ref_6244_; lean_object* v___x_6245_; 
v_ref_6244_ = lean_ctor_get(v___y_6241_, 5);
v___x_6245_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6244_, v_msgData_6236_, v_severity_6237_, v_isSilent_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_);
return v___x_6245_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6246_, lean_object* v_severity_6247_, lean_object* v_isSilent_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_){
_start:
{
uint8_t v_severity_boxed_6254_; uint8_t v_isSilent_boxed_6255_; lean_object* v_res_6256_; 
v_severity_boxed_6254_ = lean_unbox(v_severity_6247_);
v_isSilent_boxed_6255_ = lean_unbox(v_isSilent_6248_);
v_res_6256_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6246_, v_severity_boxed_6254_, v_isSilent_boxed_6255_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_);
lean_dec(v___y_6252_);
lean_dec_ref(v___y_6251_);
lean_dec(v___y_6250_);
lean_dec_ref(v___y_6249_);
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_){
_start:
{
uint8_t v___x_6263_; uint8_t v___x_6264_; lean_object* v___x_6265_; 
v___x_6263_ = 2;
v___x_6264_ = 0;
v___x_6265_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6257_, v___x_6263_, v___x_6264_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
return v___x_6265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_){
_start:
{
lean_object* v_res_6272_; 
v_res_6272_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
return v_res_6272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_){
_start:
{
lean_object* v_module_6279_; lean_object* v_const_6280_; lean_object* v_exception_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; 
v_module_6279_ = lean_ctor_get(v_f_6273_, 0);
lean_inc(v_module_6279_);
v_const_6280_ = lean_ctor_get(v_f_6273_, 1);
lean_inc(v_const_6280_);
v_exception_6281_ = lean_ctor_get(v_f_6273_, 2);
lean_inc_ref(v_exception_6281_);
lean_dec_ref(v_f_6273_);
v___x_6282_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6283_ = l_Lean_MessageData_ofName(v_const_6280_);
v___x_6284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6284_, 0, v___x_6282_);
lean_ctor_set(v___x_6284_, 1, v___x_6283_);
v___x_6285_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6286_, 0, v___x_6284_);
lean_ctor_set(v___x_6286_, 1, v___x_6285_);
v___x_6287_ = l_Lean_MessageData_ofName(v_module_6279_);
v___x_6288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6288_, 0, v___x_6286_);
lean_ctor_set(v___x_6288_, 1, v___x_6287_);
v___x_6289_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6290_, 0, v___x_6288_);
lean_ctor_set(v___x_6290_, 1, v___x_6289_);
v___x_6291_ = l_Lean_Exception_toMessageData(v_exception_6281_);
v___x_6292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6292_, 0, v___x_6290_);
lean_ctor_set(v___x_6292_, 1, v___x_6291_);
v___x_6293_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6292_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_);
return v___x_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_){
_start:
{
lean_object* v_res_6300_; 
v_res_6300_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_);
lean_dec(v___y_6298_);
lean_dec_ref(v___y_6297_);
lean_dec(v___y_6296_);
lean_dec_ref(v___y_6295_);
return v_res_6300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6301_, size_t v_i_6302_, size_t v_stop_6303_, lean_object* v_b_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_){
_start:
{
uint8_t v___x_6310_; 
v___x_6310_ = lean_usize_dec_eq(v_i_6302_, v_stop_6303_);
if (v___x_6310_ == 0)
{
lean_object* v___x_6311_; lean_object* v___x_6312_; 
v___x_6311_ = lean_array_uget_borrowed(v_as_6301_, v_i_6302_);
lean_inc(v___x_6311_);
v___x_6312_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6311_, v___y_6305_, v___y_6306_, v___y_6307_, v___y_6308_);
if (lean_obj_tag(v___x_6312_) == 0)
{
lean_object* v_a_6313_; size_t v___x_6314_; size_t v___x_6315_; 
v_a_6313_ = lean_ctor_get(v___x_6312_, 0);
lean_inc(v_a_6313_);
lean_dec_ref_known(v___x_6312_, 1);
v___x_6314_ = ((size_t)1ULL);
v___x_6315_ = lean_usize_add(v_i_6302_, v___x_6314_);
v_i_6302_ = v___x_6315_;
v_b_6304_ = v_a_6313_;
goto _start;
}
else
{
return v___x_6312_;
}
}
else
{
lean_object* v___x_6317_; 
v___x_6317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6317_, 0, v_b_6304_);
return v___x_6317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6318_, lean_object* v_i_6319_, lean_object* v_stop_6320_, lean_object* v_b_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_){
_start:
{
size_t v_i_boxed_6327_; size_t v_stop_boxed_6328_; lean_object* v_res_6329_; 
v_i_boxed_6327_ = lean_unbox_usize(v_i_6319_);
lean_dec(v_i_6319_);
v_stop_boxed_6328_ = lean_unbox_usize(v_stop_6320_);
lean_dec(v_stop_6320_);
v_res_6329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6318_, v_i_boxed_6327_, v_stop_boxed_6328_, v_b_6321_, v___y_6322_, v___y_6323_, v___y_6324_, v___y_6325_);
lean_dec(v___y_6325_);
lean_dec_ref(v___y_6324_);
lean_dec(v___y_6323_);
lean_dec_ref(v___y_6322_);
lean_dec_ref(v_as_6318_);
return v_res_6329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6330_, size_t v_i_6331_, size_t v_stop_6332_, lean_object* v_b_6333_){
_start:
{
uint8_t v___x_6334_; 
v___x_6334_ = lean_usize_dec_eq(v_i_6331_, v_stop_6332_);
if (v___x_6334_ == 0)
{
lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; size_t v___x_6338_; size_t v___x_6339_; 
v___x_6335_ = lean_array_uget_borrowed(v_as_6330_, v_i_6331_);
lean_inc(v___x_6335_);
v___x_6336_ = lean_task_get_own(v___x_6335_);
v___x_6337_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6333_, v___x_6336_);
v___x_6338_ = ((size_t)1ULL);
v___x_6339_ = lean_usize_add(v_i_6331_, v___x_6338_);
v_i_6331_ = v___x_6339_;
v_b_6333_ = v___x_6337_;
goto _start;
}
else
{
return v_b_6333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6341_, lean_object* v_i_6342_, lean_object* v_stop_6343_, lean_object* v_b_6344_){
_start:
{
size_t v_i_boxed_6345_; size_t v_stop_boxed_6346_; lean_object* v_res_6347_; 
v_i_boxed_6345_ = lean_unbox_usize(v_i_6342_);
lean_dec(v_i_6342_);
v_stop_boxed_6346_ = lean_unbox_usize(v_stop_6343_);
lean_dec(v_stop_6343_);
v_res_6347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6341_, v_i_boxed_6345_, v_stop_boxed_6346_, v_b_6344_);
lean_dec_ref(v_as_6341_);
return v_res_6347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6348_, lean_object* v_tasks_6349_){
_start:
{
lean_object* v___x_6350_; lean_object* v___x_6351_; uint8_t v___x_6352_; 
v___x_6350_ = lean_unsigned_to_nat(0u);
v___x_6351_ = lean_array_get_size(v_tasks_6349_);
v___x_6352_ = lean_nat_dec_lt(v___x_6350_, v___x_6351_);
if (v___x_6352_ == 0)
{
return v_z_6348_;
}
else
{
uint8_t v___x_6353_; 
v___x_6353_ = lean_nat_dec_le(v___x_6351_, v___x_6351_);
if (v___x_6353_ == 0)
{
if (v___x_6352_ == 0)
{
return v_z_6348_;
}
else
{
size_t v___x_6354_; size_t v___x_6355_; lean_object* v___x_6356_; 
v___x_6354_ = ((size_t)0ULL);
v___x_6355_ = lean_usize_of_nat(v___x_6351_);
v___x_6356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6349_, v___x_6354_, v___x_6355_, v_z_6348_);
return v___x_6356_;
}
}
else
{
size_t v___x_6357_; size_t v___x_6358_; lean_object* v___x_6359_; 
v___x_6357_ = ((size_t)0ULL);
v___x_6358_ = lean_usize_of_nat(v___x_6351_);
v___x_6359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6349_, v___x_6357_, v___x_6358_, v_z_6348_);
return v___x_6359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6360_, lean_object* v_tasks_6361_){
_start:
{
lean_object* v_res_6362_; 
v_res_6362_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6360_, v_tasks_6361_);
lean_dec_ref(v_tasks_6361_);
return v_res_6362_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; 
v___x_6363_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6364_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6365_, 0, v___x_6364_);
lean_ctor_set(v___x_6365_, 1, v___x_6363_);
return v___x_6365_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; 
v___x_6366_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6367_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6368_, 0, v___x_6367_);
lean_ctor_set(v___x_6368_, 1, v___x_6366_);
return v___x_6368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6369_, lean_object* v_ngen_6370_, lean_object* v_env_6371_, lean_object* v_act_6372_, lean_object* v_constantsPerTask_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_){
_start:
{
lean_object* v___x_6379_; lean_object* v_moduleData_6380_; lean_object* v_n_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v_a_6385_; lean_object* v___x_6387_; uint8_t v_isShared_6388_; uint8_t v_isSharedCheck_6427_; 
v___x_6379_ = l_Lean_Environment_header(v_env_6371_);
v_moduleData_6380_ = lean_ctor_get(v___x_6379_, 6);
lean_inc_ref(v_moduleData_6380_);
lean_dec_ref(v___x_6379_);
v_n_6381_ = lean_array_get_size(v_moduleData_6380_);
lean_dec_ref(v_moduleData_6380_);
v___x_6382_ = lean_unsigned_to_nat(0u);
v___x_6383_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6384_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6369_, v_env_6371_, v_act_6372_, v_constantsPerTask_6373_, v_n_6381_, v_ngen_6370_, v___x_6383_, v___x_6382_, v___x_6382_, v___x_6382_);
v_a_6385_ = lean_ctor_get(v___x_6384_, 0);
v_isSharedCheck_6427_ = !lean_is_exclusive(v___x_6384_);
if (v_isSharedCheck_6427_ == 0)
{
v___x_6387_ = v___x_6384_;
v_isShared_6388_ = v_isSharedCheck_6427_;
goto v_resetjp_6386_;
}
else
{
lean_inc(v_a_6385_);
lean_dec(v___x_6384_);
v___x_6387_ = lean_box(0);
v_isShared_6388_ = v_isSharedCheck_6427_;
goto v_resetjp_6386_;
}
v_resetjp_6386_:
{
lean_object* v___x_6389_; lean_object* v_r_6390_; lean_object* v_tree_6397_; lean_object* v_errors_6398_; lean_object* v___x_6399_; uint8_t v___x_6400_; 
v___x_6389_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6390_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6389_, v_a_6385_);
lean_dec(v_a_6385_);
v_tree_6397_ = lean_ctor_get(v_r_6390_, 0);
lean_inc_ref(v_tree_6397_);
v_errors_6398_ = lean_ctor_get(v_r_6390_, 1);
lean_inc_ref(v_errors_6398_);
v___x_6399_ = lean_array_get_size(v_errors_6398_);
v___x_6400_ = lean_nat_dec_lt(v___x_6382_, v___x_6399_);
if (v___x_6400_ == 0)
{
lean_object* v___x_6401_; lean_object* v___x_6402_; 
lean_dec_ref(v_errors_6398_);
lean_dec_ref(v_r_6390_);
lean_del_object(v___x_6387_);
v___x_6401_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6397_);
v___x_6402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6402_, 0, v___x_6401_);
return v___x_6402_;
}
else
{
lean_object* v___x_6403_; uint8_t v___x_6404_; 
lean_dec_ref(v_tree_6397_);
v___x_6403_ = lean_box(0);
v___x_6404_ = lean_nat_dec_le(v___x_6399_, v___x_6399_);
if (v___x_6404_ == 0)
{
if (v___x_6400_ == 0)
{
lean_dec_ref(v_errors_6398_);
goto v___jp_6391_;
}
else
{
size_t v___x_6405_; size_t v___x_6406_; lean_object* v___x_6407_; 
v___x_6405_ = ((size_t)0ULL);
v___x_6406_ = lean_usize_of_nat(v___x_6399_);
v___x_6407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6398_, v___x_6405_, v___x_6406_, v___x_6403_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_);
lean_dec_ref(v_errors_6398_);
if (lean_obj_tag(v___x_6407_) == 0)
{
lean_dec_ref_known(v___x_6407_, 1);
goto v___jp_6391_;
}
else
{
lean_object* v_a_6408_; lean_object* v___x_6410_; uint8_t v_isShared_6411_; uint8_t v_isSharedCheck_6415_; 
lean_dec_ref(v_r_6390_);
lean_del_object(v___x_6387_);
v_a_6408_ = lean_ctor_get(v___x_6407_, 0);
v_isSharedCheck_6415_ = !lean_is_exclusive(v___x_6407_);
if (v_isSharedCheck_6415_ == 0)
{
v___x_6410_ = v___x_6407_;
v_isShared_6411_ = v_isSharedCheck_6415_;
goto v_resetjp_6409_;
}
else
{
lean_inc(v_a_6408_);
lean_dec(v___x_6407_);
v___x_6410_ = lean_box(0);
v_isShared_6411_ = v_isSharedCheck_6415_;
goto v_resetjp_6409_;
}
v_resetjp_6409_:
{
lean_object* v___x_6413_; 
if (v_isShared_6411_ == 0)
{
v___x_6413_ = v___x_6410_;
goto v_reusejp_6412_;
}
else
{
lean_object* v_reuseFailAlloc_6414_; 
v_reuseFailAlloc_6414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_a_6408_);
v___x_6413_ = v_reuseFailAlloc_6414_;
goto v_reusejp_6412_;
}
v_reusejp_6412_:
{
return v___x_6413_;
}
}
}
}
}
else
{
size_t v___x_6416_; size_t v___x_6417_; lean_object* v___x_6418_; 
v___x_6416_ = ((size_t)0ULL);
v___x_6417_ = lean_usize_of_nat(v___x_6399_);
v___x_6418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6398_, v___x_6416_, v___x_6417_, v___x_6403_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_);
lean_dec_ref(v_errors_6398_);
if (lean_obj_tag(v___x_6418_) == 0)
{
lean_dec_ref_known(v___x_6418_, 1);
goto v___jp_6391_;
}
else
{
lean_object* v_a_6419_; lean_object* v___x_6421_; uint8_t v_isShared_6422_; uint8_t v_isSharedCheck_6426_; 
lean_dec_ref(v_r_6390_);
lean_del_object(v___x_6387_);
v_a_6419_ = lean_ctor_get(v___x_6418_, 0);
v_isSharedCheck_6426_ = !lean_is_exclusive(v___x_6418_);
if (v_isSharedCheck_6426_ == 0)
{
v___x_6421_ = v___x_6418_;
v_isShared_6422_ = v_isSharedCheck_6426_;
goto v_resetjp_6420_;
}
else
{
lean_inc(v_a_6419_);
lean_dec(v___x_6418_);
v___x_6421_ = lean_box(0);
v_isShared_6422_ = v_isSharedCheck_6426_;
goto v_resetjp_6420_;
}
v_resetjp_6420_:
{
lean_object* v___x_6424_; 
if (v_isShared_6422_ == 0)
{
v___x_6424_ = v___x_6421_;
goto v_reusejp_6423_;
}
else
{
lean_object* v_reuseFailAlloc_6425_; 
v_reuseFailAlloc_6425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6425_, 0, v_a_6419_);
v___x_6424_ = v_reuseFailAlloc_6425_;
goto v_reusejp_6423_;
}
v_reusejp_6423_:
{
return v___x_6424_;
}
}
}
}
}
v___jp_6391_:
{
lean_object* v_tree_6392_; lean_object* v___x_6393_; lean_object* v___x_6395_; 
v_tree_6392_ = lean_ctor_get(v_r_6390_, 0);
lean_inc_ref(v_tree_6392_);
lean_dec_ref(v_r_6390_);
v___x_6393_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6392_);
if (v_isShared_6388_ == 0)
{
lean_ctor_set(v___x_6387_, 0, v___x_6393_);
v___x_6395_ = v___x_6387_;
goto v_reusejp_6394_;
}
else
{
lean_object* v_reuseFailAlloc_6396_; 
v_reuseFailAlloc_6396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6396_, 0, v___x_6393_);
v___x_6395_ = v_reuseFailAlloc_6396_;
goto v_reusejp_6394_;
}
v_reusejp_6394_:
{
return v___x_6395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6428_, lean_object* v_ngen_6429_, lean_object* v_env_6430_, lean_object* v_act_6431_, lean_object* v_constantsPerTask_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_){
_start:
{
lean_object* v_res_6438_; 
v_res_6438_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6428_, v_ngen_6429_, v_env_6430_, v_act_6431_, v_constantsPerTask_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_);
lean_dec(v___y_6436_);
lean_dec_ref(v___y_6435_);
lean_dec(v___y_6434_);
lean_dec_ref(v___y_6433_);
lean_dec(v_constantsPerTask_6432_);
return v_res_6438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6439_, lean_object* v___x_6440_, lean_object* v_addEntry_6441_, lean_object* v_constantsPerTask_6442_, lean_object* v_droppedEntriesRef_6443_, lean_object* v_droppedKeys_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_){
_start:
{
lean_object* v___x_6450_; lean_object* v_env_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; 
v___x_6450_ = lean_st_ref_get(v___y_6448_);
v_env_6451_ = lean_ctor_get(v___x_6450_, 0);
lean_inc_ref(v_env_6451_);
lean_dec(v___x_6450_);
lean_inc_ref(v_a_6439_);
v___x_6452_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6439_);
v___x_6453_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6452_, v___x_6440_, v_env_6451_, v_addEntry_6441_, v_constantsPerTask_6442_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
if (lean_obj_tag(v___x_6453_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6443_) == 1)
{
lean_object* v_a_6454_; lean_object* v_val_6455_; lean_object* v___x_6457_; uint8_t v_isShared_6458_; uint8_t v_isSharedCheck_6488_; 
v_a_6454_ = lean_ctor_get(v___x_6453_, 0);
lean_inc(v_a_6454_);
lean_dec_ref_known(v___x_6453_, 1);
v_val_6455_ = lean_ctor_get(v_droppedEntriesRef_6443_, 0);
v_isSharedCheck_6488_ = !lean_is_exclusive(v_droppedEntriesRef_6443_);
if (v_isSharedCheck_6488_ == 0)
{
v___x_6457_ = v_droppedEntriesRef_6443_;
v_isShared_6458_ = v_isSharedCheck_6488_;
goto v_resetjp_6456_;
}
else
{
lean_inc(v_val_6455_);
lean_dec(v_droppedEntriesRef_6443_);
v___x_6457_ = lean_box(0);
v_isShared_6458_ = v_isSharedCheck_6488_;
goto v_resetjp_6456_;
}
v_resetjp_6456_:
{
lean_object* v___x_6459_; 
v___x_6459_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6454_, v_droppedKeys_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
lean_dec(v_droppedKeys_6444_);
if (lean_obj_tag(v___x_6459_) == 0)
{
lean_object* v_a_6460_; lean_object* v___x_6462_; uint8_t v_isShared_6463_; uint8_t v_isSharedCheck_6479_; 
v_a_6460_ = lean_ctor_get(v___x_6459_, 0);
v_isSharedCheck_6479_ = !lean_is_exclusive(v___x_6459_);
if (v_isSharedCheck_6479_ == 0)
{
v___x_6462_ = v___x_6459_;
v_isShared_6463_ = v_isSharedCheck_6479_;
goto v_resetjp_6461_;
}
else
{
lean_inc(v_a_6460_);
lean_dec(v___x_6459_);
v___x_6462_ = lean_box(0);
v_isShared_6463_ = v_isSharedCheck_6479_;
goto v_resetjp_6461_;
}
v_resetjp_6461_:
{
lean_object* v_fst_6464_; lean_object* v_snd_6465_; lean_object* v___x_6466_; lean_object* v___y_6468_; 
v_fst_6464_ = lean_ctor_get(v_a_6460_, 0);
lean_inc(v_fst_6464_);
v_snd_6465_ = lean_ctor_get(v_a_6460_, 1);
lean_inc(v_snd_6465_);
lean_dec(v_a_6460_);
v___x_6466_ = lean_st_ref_get(v_val_6455_);
if (lean_obj_tag(v___x_6466_) == 0)
{
lean_object* v___x_6477_; 
v___x_6477_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6468_ = v___x_6477_;
goto v___jp_6467_;
}
else
{
lean_object* v_val_6478_; 
v_val_6478_ = lean_ctor_get(v___x_6466_, 0);
lean_inc(v_val_6478_);
lean_dec_ref_known(v___x_6466_, 1);
v___y_6468_ = v_val_6478_;
goto v___jp_6467_;
}
v___jp_6467_:
{
lean_object* v___x_6469_; lean_object* v___x_6471_; 
v___x_6469_ = l_Array_append___redArg(v___y_6468_, v_fst_6464_);
lean_dec(v_fst_6464_);
if (v_isShared_6458_ == 0)
{
lean_ctor_set(v___x_6457_, 0, v___x_6469_);
v___x_6471_ = v___x_6457_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6476_; 
v_reuseFailAlloc_6476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6476_, 0, v___x_6469_);
v___x_6471_ = v_reuseFailAlloc_6476_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
lean_object* v___x_6472_; lean_object* v___x_6474_; 
v___x_6472_ = lean_st_ref_set(v_val_6455_, v___x_6471_);
lean_dec(v_val_6455_);
if (v_isShared_6463_ == 0)
{
lean_ctor_set(v___x_6462_, 0, v_snd_6465_);
v___x_6474_ = v___x_6462_;
goto v_reusejp_6473_;
}
else
{
lean_object* v_reuseFailAlloc_6475_; 
v_reuseFailAlloc_6475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6475_, 0, v_snd_6465_);
v___x_6474_ = v_reuseFailAlloc_6475_;
goto v_reusejp_6473_;
}
v_reusejp_6473_:
{
return v___x_6474_;
}
}
}
}
}
else
{
lean_object* v_a_6480_; lean_object* v___x_6482_; uint8_t v_isShared_6483_; uint8_t v_isSharedCheck_6487_; 
lean_del_object(v___x_6457_);
lean_dec(v_val_6455_);
v_a_6480_ = lean_ctor_get(v___x_6459_, 0);
v_isSharedCheck_6487_ = !lean_is_exclusive(v___x_6459_);
if (v_isSharedCheck_6487_ == 0)
{
v___x_6482_ = v___x_6459_;
v_isShared_6483_ = v_isSharedCheck_6487_;
goto v_resetjp_6481_;
}
else
{
lean_inc(v_a_6480_);
lean_dec(v___x_6459_);
v___x_6482_ = lean_box(0);
v_isShared_6483_ = v_isSharedCheck_6487_;
goto v_resetjp_6481_;
}
v_resetjp_6481_:
{
lean_object* v___x_6485_; 
if (v_isShared_6483_ == 0)
{
v___x_6485_ = v___x_6482_;
goto v_reusejp_6484_;
}
else
{
lean_object* v_reuseFailAlloc_6486_; 
v_reuseFailAlloc_6486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6486_, 0, v_a_6480_);
v___x_6485_ = v_reuseFailAlloc_6486_;
goto v_reusejp_6484_;
}
v_reusejp_6484_:
{
return v___x_6485_;
}
}
}
}
}
else
{
lean_object* v_a_6489_; lean_object* v___x_6490_; 
lean_dec(v_droppedEntriesRef_6443_);
v_a_6489_ = lean_ctor_get(v___x_6453_, 0);
lean_inc(v_a_6489_);
lean_dec_ref_known(v___x_6453_, 1);
v___x_6490_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6489_, v_droppedKeys_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
return v___x_6490_;
}
}
else
{
lean_dec(v_droppedKeys_6444_);
lean_dec(v_droppedEntriesRef_6443_);
return v___x_6453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6491_, lean_object* v___x_6492_, lean_object* v_addEntry_6493_, lean_object* v_constantsPerTask_6494_, lean_object* v_droppedEntriesRef_6495_, lean_object* v_droppedKeys_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_){
_start:
{
lean_object* v_res_6502_; 
v_res_6502_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6491_, v___x_6492_, v_addEntry_6493_, v_constantsPerTask_6494_, v_droppedEntriesRef_6495_, v_droppedKeys_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_);
lean_dec(v___y_6500_);
lean_dec_ref(v___y_6499_);
lean_dec(v___y_6498_);
lean_dec_ref(v___y_6497_);
lean_dec(v_constantsPerTask_6494_);
lean_dec_ref(v_a_6491_);
return v_res_6502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6504_, lean_object* v_addEntry_6505_, lean_object* v_droppedKeys_6506_, lean_object* v_constantsPerTask_6507_, lean_object* v_droppedEntriesRef_6508_, lean_object* v_ty_6509_, lean_object* v_a_6510_, lean_object* v_a_6511_, lean_object* v_a_6512_, lean_object* v_a_6513_){
_start:
{
lean_object* v_a_6516_; lean_object* v___x_6538_; lean_object* v_ngen_6539_; lean_object* v_namePrefix_6540_; lean_object* v_idx_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6586_; 
v___x_6538_ = lean_st_ref_get(v_a_6513_);
v_ngen_6539_ = lean_ctor_get(v___x_6538_, 2);
lean_inc_ref(v_ngen_6539_);
lean_dec(v___x_6538_);
v_namePrefix_6540_ = lean_ctor_get(v_ngen_6539_, 0);
v_idx_6541_ = lean_ctor_get(v_ngen_6539_, 1);
v_isSharedCheck_6586_ = !lean_is_exclusive(v_ngen_6539_);
if (v_isSharedCheck_6586_ == 0)
{
v___x_6543_ = v_ngen_6539_;
v_isShared_6544_ = v_isSharedCheck_6586_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_idx_6541_);
lean_inc(v_namePrefix_6540_);
lean_dec(v_ngen_6539_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6586_;
goto v_resetjp_6542_;
}
v___jp_6515_:
{
lean_object* v___x_6517_; 
v___x_6517_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6516_, v_ty_6509_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
if (lean_obj_tag(v___x_6517_) == 0)
{
lean_object* v_a_6518_; lean_object* v___x_6520_; uint8_t v_isShared_6521_; uint8_t v_isSharedCheck_6529_; 
v_a_6518_ = lean_ctor_get(v___x_6517_, 0);
v_isSharedCheck_6529_ = !lean_is_exclusive(v___x_6517_);
if (v_isSharedCheck_6529_ == 0)
{
v___x_6520_ = v___x_6517_;
v_isShared_6521_ = v_isSharedCheck_6529_;
goto v_resetjp_6519_;
}
else
{
lean_inc(v_a_6518_);
lean_dec(v___x_6517_);
v___x_6520_ = lean_box(0);
v_isShared_6521_ = v_isSharedCheck_6529_;
goto v_resetjp_6519_;
}
v_resetjp_6519_:
{
lean_object* v_fst_6522_; lean_object* v_snd_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6527_; 
v_fst_6522_ = lean_ctor_get(v_a_6518_, 0);
lean_inc(v_fst_6522_);
v_snd_6523_ = lean_ctor_get(v_a_6518_, 1);
lean_inc(v_snd_6523_);
lean_dec(v_a_6518_);
v___x_6524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6524_, 0, v_snd_6523_);
v___x_6525_ = lean_st_ref_set(v_ref_6504_, v___x_6524_);
if (v_isShared_6521_ == 0)
{
lean_ctor_set(v___x_6520_, 0, v_fst_6522_);
v___x_6527_ = v___x_6520_;
goto v_reusejp_6526_;
}
else
{
lean_object* v_reuseFailAlloc_6528_; 
v_reuseFailAlloc_6528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_fst_6522_);
v___x_6527_ = v_reuseFailAlloc_6528_;
goto v_reusejp_6526_;
}
v_reusejp_6526_:
{
return v___x_6527_;
}
}
}
else
{
lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6537_; 
v_a_6530_ = lean_ctor_get(v___x_6517_, 0);
v_isSharedCheck_6537_ = !lean_is_exclusive(v___x_6517_);
if (v_isSharedCheck_6537_ == 0)
{
v___x_6532_ = v___x_6517_;
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_dec(v___x_6517_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6537_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v___x_6535_; 
if (v_isShared_6533_ == 0)
{
v___x_6535_ = v___x_6532_;
goto v_reusejp_6534_;
}
else
{
lean_object* v_reuseFailAlloc_6536_; 
v_reuseFailAlloc_6536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_a_6530_);
v___x_6535_ = v_reuseFailAlloc_6536_;
goto v_reusejp_6534_;
}
v_reusejp_6534_:
{
return v___x_6535_;
}
}
}
}
v_resetjp_6542_:
{
lean_object* v___x_6545_; lean_object* v_env_6546_; lean_object* v_nextMacroScope_6547_; lean_object* v_auxDeclNGen_6548_; lean_object* v_traceState_6549_; lean_object* v_cache_6550_; lean_object* v_messages_6551_; lean_object* v_infoState_6552_; lean_object* v_snapshotTasks_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6584_; 
v___x_6545_ = lean_st_ref_take(v_a_6513_);
v_env_6546_ = lean_ctor_get(v___x_6545_, 0);
v_nextMacroScope_6547_ = lean_ctor_get(v___x_6545_, 1);
v_auxDeclNGen_6548_ = lean_ctor_get(v___x_6545_, 3);
v_traceState_6549_ = lean_ctor_get(v___x_6545_, 4);
v_cache_6550_ = lean_ctor_get(v___x_6545_, 5);
v_messages_6551_ = lean_ctor_get(v___x_6545_, 6);
v_infoState_6552_ = lean_ctor_get(v___x_6545_, 7);
v_snapshotTasks_6553_ = lean_ctor_get(v___x_6545_, 8);
v_isSharedCheck_6584_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6584_ == 0)
{
lean_object* v_unused_6585_; 
v_unused_6585_ = lean_ctor_get(v___x_6545_, 2);
lean_dec(v_unused_6585_);
v___x_6555_ = v___x_6545_;
v_isShared_6556_ = v_isSharedCheck_6584_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_snapshotTasks_6553_);
lean_inc(v_infoState_6552_);
lean_inc(v_messages_6551_);
lean_inc(v_cache_6550_);
lean_inc(v_traceState_6549_);
lean_inc(v_auxDeclNGen_6548_);
lean_inc(v_nextMacroScope_6547_);
lean_inc(v_env_6546_);
lean_dec(v___x_6545_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6584_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6561_; 
lean_inc(v_idx_6541_);
lean_inc(v_namePrefix_6540_);
v___x_6557_ = l_Lean_Name_num___override(v_namePrefix_6540_, v_idx_6541_);
v___x_6558_ = lean_unsigned_to_nat(1u);
v___x_6559_ = lean_nat_add(v_idx_6541_, v___x_6558_);
lean_dec(v_idx_6541_);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 1, v___x_6559_);
v___x_6561_ = v___x_6543_;
goto v_reusejp_6560_;
}
else
{
lean_object* v_reuseFailAlloc_6583_; 
v_reuseFailAlloc_6583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_namePrefix_6540_);
lean_ctor_set(v_reuseFailAlloc_6583_, 1, v___x_6559_);
v___x_6561_ = v_reuseFailAlloc_6583_;
goto v_reusejp_6560_;
}
v_reusejp_6560_:
{
lean_object* v___x_6563_; 
if (v_isShared_6556_ == 0)
{
lean_ctor_set(v___x_6555_, 2, v___x_6561_);
v___x_6563_ = v___x_6555_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6582_; 
v_reuseFailAlloc_6582_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6582_, 0, v_env_6546_);
lean_ctor_set(v_reuseFailAlloc_6582_, 1, v_nextMacroScope_6547_);
lean_ctor_set(v_reuseFailAlloc_6582_, 2, v___x_6561_);
lean_ctor_set(v_reuseFailAlloc_6582_, 3, v_auxDeclNGen_6548_);
lean_ctor_set(v_reuseFailAlloc_6582_, 4, v_traceState_6549_);
lean_ctor_set(v_reuseFailAlloc_6582_, 5, v_cache_6550_);
lean_ctor_set(v_reuseFailAlloc_6582_, 6, v_messages_6551_);
lean_ctor_set(v_reuseFailAlloc_6582_, 7, v_infoState_6552_);
lean_ctor_set(v_reuseFailAlloc_6582_, 8, v_snapshotTasks_6553_);
v___x_6563_ = v_reuseFailAlloc_6582_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
lean_object* v___x_6564_; lean_object* v___x_6565_; 
v___x_6564_ = lean_st_ref_set(v_a_6513_, v___x_6563_);
v___x_6565_ = lean_st_ref_get(v_ref_6504_);
if (lean_obj_tag(v___x_6565_) == 0)
{
lean_object* v_options_6566_; lean_object* v___x_6567_; lean_object* v___f_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; 
v_options_6566_ = lean_ctor_get(v_a_6512_, 2);
v___x_6567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6567_, 0, v___x_6557_);
lean_ctor_set(v___x_6567_, 1, v___x_6558_);
lean_inc_ref(v_a_6512_);
v___f_6568_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6568_, 0, v_a_6512_);
lean_closure_set(v___f_6568_, 1, v___x_6567_);
lean_closure_set(v___f_6568_, 2, v_addEntry_6505_);
lean_closure_set(v___f_6568_, 3, v_constantsPerTask_6507_);
lean_closure_set(v___f_6568_, 4, v_droppedEntriesRef_6508_);
lean_closure_set(v___f_6568_, 5, v_droppedKeys_6506_);
v___x_6569_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6570_ = lean_box(0);
v___x_6571_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6569_, v_options_6566_, v___f_6568_, v___x_6570_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
if (lean_obj_tag(v___x_6571_) == 0)
{
lean_object* v_a_6572_; 
v_a_6572_ = lean_ctor_get(v___x_6571_, 0);
lean_inc(v_a_6572_);
lean_dec_ref_known(v___x_6571_, 1);
v_a_6516_ = v_a_6572_;
goto v___jp_6515_;
}
else
{
lean_object* v_a_6573_; lean_object* v___x_6575_; uint8_t v_isShared_6576_; uint8_t v_isSharedCheck_6580_; 
lean_dec_ref(v_ty_6509_);
v_a_6573_ = lean_ctor_get(v___x_6571_, 0);
v_isSharedCheck_6580_ = !lean_is_exclusive(v___x_6571_);
if (v_isSharedCheck_6580_ == 0)
{
v___x_6575_ = v___x_6571_;
v_isShared_6576_ = v_isSharedCheck_6580_;
goto v_resetjp_6574_;
}
else
{
lean_inc(v_a_6573_);
lean_dec(v___x_6571_);
v___x_6575_ = lean_box(0);
v_isShared_6576_ = v_isSharedCheck_6580_;
goto v_resetjp_6574_;
}
v_resetjp_6574_:
{
lean_object* v___x_6578_; 
if (v_isShared_6576_ == 0)
{
v___x_6578_ = v___x_6575_;
goto v_reusejp_6577_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_a_6573_);
v___x_6578_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6577_;
}
v_reusejp_6577_:
{
return v___x_6578_;
}
}
}
}
else
{
lean_object* v_val_6581_; 
lean_dec(v___x_6557_);
lean_dec(v_droppedEntriesRef_6508_);
lean_dec(v_constantsPerTask_6507_);
lean_dec(v_droppedKeys_6506_);
lean_dec_ref(v_addEntry_6505_);
v_val_6581_ = lean_ctor_get(v___x_6565_, 0);
lean_inc(v_val_6581_);
lean_dec_ref_known(v___x_6565_, 1);
v_a_6516_ = v_val_6581_;
goto v___jp_6515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6587_, lean_object* v_addEntry_6588_, lean_object* v_droppedKeys_6589_, lean_object* v_constantsPerTask_6590_, lean_object* v_droppedEntriesRef_6591_, lean_object* v_ty_6592_, lean_object* v_a_6593_, lean_object* v_a_6594_, lean_object* v_a_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_){
_start:
{
lean_object* v_res_6598_; 
v_res_6598_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6587_, v_addEntry_6588_, v_droppedKeys_6589_, v_constantsPerTask_6590_, v_droppedEntriesRef_6591_, v_ty_6592_, v_a_6593_, v_a_6594_, v_a_6595_, v_a_6596_);
lean_dec(v_a_6596_);
lean_dec_ref(v_a_6595_);
lean_dec(v_a_6594_);
lean_dec_ref(v_a_6593_);
lean_dec(v_ref_6587_);
return v_res_6598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6599_, lean_object* v_ref_6600_, lean_object* v_addEntry_6601_, lean_object* v_droppedKeys_6602_, lean_object* v_constantsPerTask_6603_, lean_object* v_droppedEntriesRef_6604_, lean_object* v_ty_6605_, lean_object* v_a_6606_, lean_object* v_a_6607_, lean_object* v_a_6608_, lean_object* v_a_6609_){
_start:
{
lean_object* v___x_6611_; 
v___x_6611_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6600_, v_addEntry_6601_, v_droppedKeys_6602_, v_constantsPerTask_6603_, v_droppedEntriesRef_6604_, v_ty_6605_, v_a_6606_, v_a_6607_, v_a_6608_, v_a_6609_);
return v___x_6611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6612_, lean_object* v_ref_6613_, lean_object* v_addEntry_6614_, lean_object* v_droppedKeys_6615_, lean_object* v_constantsPerTask_6616_, lean_object* v_droppedEntriesRef_6617_, lean_object* v_ty_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_){
_start:
{
lean_object* v_res_6624_; 
v_res_6624_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6612_, v_ref_6613_, v_addEntry_6614_, v_droppedKeys_6615_, v_constantsPerTask_6616_, v_droppedEntriesRef_6617_, v_ty_6618_, v_a_6619_, v_a_6620_, v_a_6621_, v_a_6622_);
lean_dec(v_a_6622_);
lean_dec_ref(v_a_6621_);
lean_dec(v_a_6620_);
lean_dec_ref(v_a_6619_);
lean_dec(v_ref_6613_);
return v_res_6624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6625_, lean_object* v_cctx_6626_, lean_object* v_ngen_6627_, lean_object* v_env_6628_, lean_object* v_act_6629_, lean_object* v_constantsPerTask_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_){
_start:
{
lean_object* v___x_6636_; 
v___x_6636_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6626_, v_ngen_6627_, v_env_6628_, v_act_6629_, v_constantsPerTask_6630_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_);
return v___x_6636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6637_, lean_object* v_cctx_6638_, lean_object* v_ngen_6639_, lean_object* v_env_6640_, lean_object* v_act_6641_, lean_object* v_constantsPerTask_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_, lean_object* v___y_6646_, lean_object* v___y_6647_){
_start:
{
lean_object* v_res_6648_; 
v_res_6648_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6637_, v_cctx_6638_, v_ngen_6639_, v_env_6640_, v_act_6641_, v_constantsPerTask_6642_, v___y_6643_, v___y_6644_, v___y_6645_, v___y_6646_);
lean_dec(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec(v_constantsPerTask_6642_);
return v_res_6648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6649_, lean_object* v_cctx_6650_, lean_object* v_env_6651_, lean_object* v_act_6652_, lean_object* v_constantsPerTask_6653_, lean_object* v_n_6654_, lean_object* v_ngen_6655_, lean_object* v_tasks_6656_, lean_object* v_start_6657_, lean_object* v_cnt_6658_, lean_object* v_idx_6659_, lean_object* v___y_6660_, lean_object* v___y_6661_, lean_object* v___y_6662_, lean_object* v___y_6663_){
_start:
{
lean_object* v___x_6665_; 
v___x_6665_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6650_, v_env_6651_, v_act_6652_, v_constantsPerTask_6653_, v_n_6654_, v_ngen_6655_, v_tasks_6656_, v_start_6657_, v_cnt_6658_, v_idx_6659_);
return v___x_6665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6666_, lean_object* v_cctx_6667_, lean_object* v_env_6668_, lean_object* v_act_6669_, lean_object* v_constantsPerTask_6670_, lean_object* v_n_6671_, lean_object* v_ngen_6672_, lean_object* v_tasks_6673_, lean_object* v_start_6674_, lean_object* v_cnt_6675_, lean_object* v_idx_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_, lean_object* v___y_6681_){
_start:
{
lean_object* v_res_6682_; 
v_res_6682_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6666_, v_cctx_6667_, v_env_6668_, v_act_6669_, v_constantsPerTask_6670_, v_n_6671_, v_ngen_6672_, v_tasks_6673_, v_start_6674_, v_cnt_6675_, v_idx_6676_, v___y_6677_, v___y_6678_, v___y_6679_, v___y_6680_);
lean_dec(v___y_6680_);
lean_dec_ref(v___y_6679_);
lean_dec(v___y_6678_);
lean_dec_ref(v___y_6677_);
lean_dec(v_constantsPerTask_6670_);
return v_res_6682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6683_, lean_object* v_z_6684_, lean_object* v_tasks_6685_){
_start:
{
lean_object* v___x_6686_; 
v___x_6686_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6684_, v_tasks_6685_);
return v___x_6686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6687_, lean_object* v_z_6688_, lean_object* v_tasks_6689_){
_start:
{
lean_object* v_res_6690_; 
v_res_6690_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6687_, v_z_6688_, v_tasks_6689_);
lean_dec_ref(v_tasks_6689_);
return v_res_6690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6691_, lean_object* v_as_6692_, size_t v_i_6693_, size_t v_stop_6694_, lean_object* v_b_6695_){
_start:
{
lean_object* v___x_6696_; 
v___x_6696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6692_, v_i_6693_, v_stop_6694_, v_b_6695_);
return v___x_6696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6697_, lean_object* v_as_6698_, lean_object* v_i_6699_, lean_object* v_stop_6700_, lean_object* v_b_6701_){
_start:
{
size_t v_i_boxed_6702_; size_t v_stop_boxed_6703_; lean_object* v_res_6704_; 
v_i_boxed_6702_ = lean_unbox_usize(v_i_6699_);
lean_dec(v_i_6699_);
v_stop_boxed_6703_ = lean_unbox_usize(v_stop_6700_);
lean_dec(v_stop_6700_);
v_res_6704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6697_, v_as_6698_, v_i_boxed_6702_, v_stop_boxed_6703_, v_b_6701_);
lean_dec_ref(v_as_6698_);
return v_res_6704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6705_){
_start:
{
lean_object* v___x_6707_; lean_object* v_ngen_6708_; lean_object* v_namePrefix_6709_; lean_object* v_idx_6710_; lean_object* v___x_6712_; uint8_t v_isShared_6713_; uint8_t v_isSharedCheck_6740_; 
v___x_6707_ = lean_st_ref_get(v___y_6705_);
v_ngen_6708_ = lean_ctor_get(v___x_6707_, 2);
lean_inc_ref(v_ngen_6708_);
lean_dec(v___x_6707_);
v_namePrefix_6709_ = lean_ctor_get(v_ngen_6708_, 0);
v_idx_6710_ = lean_ctor_get(v_ngen_6708_, 1);
v_isSharedCheck_6740_ = !lean_is_exclusive(v_ngen_6708_);
if (v_isSharedCheck_6740_ == 0)
{
v___x_6712_ = v_ngen_6708_;
v_isShared_6713_ = v_isSharedCheck_6740_;
goto v_resetjp_6711_;
}
else
{
lean_inc(v_idx_6710_);
lean_inc(v_namePrefix_6709_);
lean_dec(v_ngen_6708_);
v___x_6712_ = lean_box(0);
v_isShared_6713_ = v_isSharedCheck_6740_;
goto v_resetjp_6711_;
}
v_resetjp_6711_:
{
lean_object* v___x_6714_; lean_object* v_env_6715_; lean_object* v_nextMacroScope_6716_; lean_object* v_auxDeclNGen_6717_; lean_object* v_traceState_6718_; lean_object* v_cache_6719_; lean_object* v_messages_6720_; lean_object* v_infoState_6721_; lean_object* v_snapshotTasks_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6738_; 
v___x_6714_ = lean_st_ref_take(v___y_6705_);
v_env_6715_ = lean_ctor_get(v___x_6714_, 0);
v_nextMacroScope_6716_ = lean_ctor_get(v___x_6714_, 1);
v_auxDeclNGen_6717_ = lean_ctor_get(v___x_6714_, 3);
v_traceState_6718_ = lean_ctor_get(v___x_6714_, 4);
v_cache_6719_ = lean_ctor_get(v___x_6714_, 5);
v_messages_6720_ = lean_ctor_get(v___x_6714_, 6);
v_infoState_6721_ = lean_ctor_get(v___x_6714_, 7);
v_snapshotTasks_6722_ = lean_ctor_get(v___x_6714_, 8);
v_isSharedCheck_6738_ = !lean_is_exclusive(v___x_6714_);
if (v_isSharedCheck_6738_ == 0)
{
lean_object* v_unused_6739_; 
v_unused_6739_ = lean_ctor_get(v___x_6714_, 2);
lean_dec(v_unused_6739_);
v___x_6724_ = v___x_6714_;
v_isShared_6725_ = v_isSharedCheck_6738_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_snapshotTasks_6722_);
lean_inc(v_infoState_6721_);
lean_inc(v_messages_6720_);
lean_inc(v_cache_6719_);
lean_inc(v_traceState_6718_);
lean_inc(v_auxDeclNGen_6717_);
lean_inc(v_nextMacroScope_6716_);
lean_inc(v_env_6715_);
lean_dec(v___x_6714_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6738_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; lean_object* v___x_6730_; 
lean_inc(v_idx_6710_);
lean_inc(v_namePrefix_6709_);
v___x_6726_ = l_Lean_Name_num___override(v_namePrefix_6709_, v_idx_6710_);
v___x_6727_ = lean_unsigned_to_nat(1u);
v___x_6728_ = lean_nat_add(v_idx_6710_, v___x_6727_);
lean_dec(v_idx_6710_);
if (v_isShared_6713_ == 0)
{
lean_ctor_set(v___x_6712_, 1, v___x_6728_);
v___x_6730_ = v___x_6712_;
goto v_reusejp_6729_;
}
else
{
lean_object* v_reuseFailAlloc_6737_; 
v_reuseFailAlloc_6737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6737_, 0, v_namePrefix_6709_);
lean_ctor_set(v_reuseFailAlloc_6737_, 1, v___x_6728_);
v___x_6730_ = v_reuseFailAlloc_6737_;
goto v_reusejp_6729_;
}
v_reusejp_6729_:
{
lean_object* v___x_6732_; 
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 2, v___x_6730_);
v___x_6732_ = v___x_6724_;
goto v_reusejp_6731_;
}
else
{
lean_object* v_reuseFailAlloc_6736_; 
v_reuseFailAlloc_6736_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6736_, 0, v_env_6715_);
lean_ctor_set(v_reuseFailAlloc_6736_, 1, v_nextMacroScope_6716_);
lean_ctor_set(v_reuseFailAlloc_6736_, 2, v___x_6730_);
lean_ctor_set(v_reuseFailAlloc_6736_, 3, v_auxDeclNGen_6717_);
lean_ctor_set(v_reuseFailAlloc_6736_, 4, v_traceState_6718_);
lean_ctor_set(v_reuseFailAlloc_6736_, 5, v_cache_6719_);
lean_ctor_set(v_reuseFailAlloc_6736_, 6, v_messages_6720_);
lean_ctor_set(v_reuseFailAlloc_6736_, 7, v_infoState_6721_);
lean_ctor_set(v_reuseFailAlloc_6736_, 8, v_snapshotTasks_6722_);
v___x_6732_ = v_reuseFailAlloc_6736_;
goto v_reusejp_6731_;
}
v_reusejp_6731_:
{
lean_object* v___x_6733_; lean_object* v___x_6734_; lean_object* v___x_6735_; 
v___x_6733_ = lean_st_ref_set(v___y_6705_, v___x_6732_);
v___x_6734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6734_, 0, v___x_6726_);
lean_ctor_set(v___x_6734_, 1, v___x_6727_);
v___x_6735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6735_, 0, v___x_6734_);
return v___x_6735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6741_, lean_object* v___y_6742_){
_start:
{
lean_object* v_res_6743_; 
v_res_6743_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6741_);
lean_dec(v___y_6741_);
return v_res_6743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6744_, lean_object* v___y_6745_){
_start:
{
lean_object* v___x_6747_; 
v___x_6747_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6745_);
return v___x_6747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_){
_start:
{
lean_object* v_res_6751_; 
v_res_6751_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6748_, v___y_6749_);
lean_dec(v___y_6749_);
lean_dec_ref(v___y_6748_);
return v_res_6751_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; 
v___x_6752_ = lean_unsigned_to_nat(32u);
v___x_6753_ = lean_mk_empty_array_with_capacity(v___x_6752_);
v___x_6754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6754_, 0, v___x_6753_);
return v___x_6754_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; 
v___x_6755_ = ((size_t)5ULL);
v___x_6756_ = lean_unsigned_to_nat(0u);
v___x_6757_ = lean_unsigned_to_nat(32u);
v___x_6758_ = lean_mk_empty_array_with_capacity(v___x_6757_);
v___x_6759_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6760_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6760_, 0, v___x_6759_);
lean_ctor_set(v___x_6760_, 1, v___x_6758_);
lean_ctor_set(v___x_6760_, 2, v___x_6756_);
lean_ctor_set(v___x_6760_, 3, v___x_6756_);
lean_ctor_set_usize(v___x_6760_, 4, v___x_6755_);
return v___x_6760_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; 
v___x_6761_ = lean_box(1);
v___x_6762_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6763_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6764_, 0, v___x_6763_);
lean_ctor_set(v___x_6764_, 1, v___x_6762_);
lean_ctor_set(v___x_6764_, 2, v___x_6761_);
return v___x_6764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_){
_start:
{
lean_object* v___x_6769_; lean_object* v_env_6770_; lean_object* v_options_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; 
v___x_6769_ = lean_st_ref_get(v___y_6767_);
v_env_6770_ = lean_ctor_get(v___x_6769_, 0);
lean_inc_ref(v_env_6770_);
lean_dec(v___x_6769_);
v_options_6771_ = lean_ctor_get(v___y_6766_, 2);
v___x_6772_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6773_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6771_);
v___x_6774_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6774_, 0, v_env_6770_);
lean_ctor_set(v___x_6774_, 1, v___x_6772_);
lean_ctor_set(v___x_6774_, 2, v___x_6773_);
lean_ctor_set(v___x_6774_, 3, v_options_6771_);
v___x_6775_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6775_, 0, v___x_6774_);
lean_ctor_set(v___x_6775_, 1, v_msgData_6765_);
v___x_6776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6776_, 0, v___x_6775_);
return v___x_6776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_){
_start:
{
lean_object* v_res_6781_; 
v_res_6781_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6777_, v___y_6778_, v___y_6779_);
lean_dec(v___y_6779_);
lean_dec_ref(v___y_6778_);
return v_res_6781_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6782_, lean_object* v_msgData_6783_, uint8_t v_severity_6784_, uint8_t v_isSilent_6785_, lean_object* v___y_6786_, lean_object* v___y_6787_){
_start:
{
lean_object* v___y_6790_; lean_object* v___y_6791_; lean_object* v___y_6792_; uint8_t v___y_6793_; lean_object* v___y_6794_; lean_object* v___y_6795_; uint8_t v___y_6796_; lean_object* v___y_6797_; lean_object* v___y_6798_; lean_object* v___y_6826_; lean_object* v___y_6827_; uint8_t v___y_6828_; uint8_t v___y_6829_; lean_object* v___y_6830_; lean_object* v___y_6831_; uint8_t v___y_6832_; lean_object* v___y_6833_; lean_object* v___y_6851_; uint8_t v___y_6852_; lean_object* v___y_6853_; uint8_t v___y_6854_; lean_object* v___y_6855_; lean_object* v___y_6856_; uint8_t v___y_6857_; lean_object* v___y_6858_; lean_object* v___y_6862_; uint8_t v___y_6863_; uint8_t v___y_6864_; lean_object* v___y_6865_; lean_object* v___y_6866_; lean_object* v___y_6867_; uint8_t v___y_6868_; uint8_t v___x_6873_; uint8_t v___y_6875_; lean_object* v___y_6876_; lean_object* v___y_6877_; lean_object* v___y_6878_; lean_object* v___y_6879_; uint8_t v___y_6880_; uint8_t v___y_6881_; uint8_t v___y_6883_; uint8_t v___x_6898_; 
v___x_6873_ = 2;
v___x_6898_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6784_, v___x_6873_);
if (v___x_6898_ == 0)
{
v___y_6883_ = v___x_6898_;
goto v___jp_6882_;
}
else
{
uint8_t v___x_6899_; 
lean_inc_ref(v_msgData_6783_);
v___x_6899_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6783_);
v___y_6883_ = v___x_6899_;
goto v___jp_6882_;
}
v___jp_6789_:
{
lean_object* v___x_6799_; lean_object* v_currNamespace_6800_; lean_object* v_openDecls_6801_; lean_object* v_env_6802_; lean_object* v_nextMacroScope_6803_; lean_object* v_ngen_6804_; lean_object* v_auxDeclNGen_6805_; lean_object* v_traceState_6806_; lean_object* v_cache_6807_; lean_object* v_messages_6808_; lean_object* v_infoState_6809_; lean_object* v_snapshotTasks_6810_; lean_object* v___x_6812_; uint8_t v_isShared_6813_; uint8_t v_isSharedCheck_6824_; 
v___x_6799_ = lean_st_ref_take(v___y_6798_);
v_currNamespace_6800_ = lean_ctor_get(v___y_6797_, 6);
v_openDecls_6801_ = lean_ctor_get(v___y_6797_, 7);
v_env_6802_ = lean_ctor_get(v___x_6799_, 0);
v_nextMacroScope_6803_ = lean_ctor_get(v___x_6799_, 1);
v_ngen_6804_ = lean_ctor_get(v___x_6799_, 2);
v_auxDeclNGen_6805_ = lean_ctor_get(v___x_6799_, 3);
v_traceState_6806_ = lean_ctor_get(v___x_6799_, 4);
v_cache_6807_ = lean_ctor_get(v___x_6799_, 5);
v_messages_6808_ = lean_ctor_get(v___x_6799_, 6);
v_infoState_6809_ = lean_ctor_get(v___x_6799_, 7);
v_snapshotTasks_6810_ = lean_ctor_get(v___x_6799_, 8);
v_isSharedCheck_6824_ = !lean_is_exclusive(v___x_6799_);
if (v_isSharedCheck_6824_ == 0)
{
v___x_6812_ = v___x_6799_;
v_isShared_6813_ = v_isSharedCheck_6824_;
goto v_resetjp_6811_;
}
else
{
lean_inc(v_snapshotTasks_6810_);
lean_inc(v_infoState_6809_);
lean_inc(v_messages_6808_);
lean_inc(v_cache_6807_);
lean_inc(v_traceState_6806_);
lean_inc(v_auxDeclNGen_6805_);
lean_inc(v_ngen_6804_);
lean_inc(v_nextMacroScope_6803_);
lean_inc(v_env_6802_);
lean_dec(v___x_6799_);
v___x_6812_ = lean_box(0);
v_isShared_6813_ = v_isSharedCheck_6824_;
goto v_resetjp_6811_;
}
v_resetjp_6811_:
{
lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; lean_object* v___x_6817_; lean_object* v___x_6819_; 
lean_inc(v_openDecls_6801_);
lean_inc(v_currNamespace_6800_);
v___x_6814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6814_, 0, v_currNamespace_6800_);
lean_ctor_set(v___x_6814_, 1, v_openDecls_6801_);
v___x_6815_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6815_, 0, v___x_6814_);
lean_ctor_set(v___x_6815_, 1, v___y_6790_);
lean_inc_ref(v___y_6792_);
lean_inc_ref(v___y_6795_);
v___x_6816_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6816_, 0, v___y_6795_);
lean_ctor_set(v___x_6816_, 1, v___y_6794_);
lean_ctor_set(v___x_6816_, 2, v___y_6791_);
lean_ctor_set(v___x_6816_, 3, v___y_6792_);
lean_ctor_set(v___x_6816_, 4, v___x_6815_);
lean_ctor_set_uint8(v___x_6816_, sizeof(void*)*5, v___y_6793_);
lean_ctor_set_uint8(v___x_6816_, sizeof(void*)*5 + 1, v___y_6796_);
lean_ctor_set_uint8(v___x_6816_, sizeof(void*)*5 + 2, v_isSilent_6785_);
v___x_6817_ = l_Lean_MessageLog_add(v___x_6816_, v_messages_6808_);
if (v_isShared_6813_ == 0)
{
lean_ctor_set(v___x_6812_, 6, v___x_6817_);
v___x_6819_ = v___x_6812_;
goto v_reusejp_6818_;
}
else
{
lean_object* v_reuseFailAlloc_6823_; 
v_reuseFailAlloc_6823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6823_, 0, v_env_6802_);
lean_ctor_set(v_reuseFailAlloc_6823_, 1, v_nextMacroScope_6803_);
lean_ctor_set(v_reuseFailAlloc_6823_, 2, v_ngen_6804_);
lean_ctor_set(v_reuseFailAlloc_6823_, 3, v_auxDeclNGen_6805_);
lean_ctor_set(v_reuseFailAlloc_6823_, 4, v_traceState_6806_);
lean_ctor_set(v_reuseFailAlloc_6823_, 5, v_cache_6807_);
lean_ctor_set(v_reuseFailAlloc_6823_, 6, v___x_6817_);
lean_ctor_set(v_reuseFailAlloc_6823_, 7, v_infoState_6809_);
lean_ctor_set(v_reuseFailAlloc_6823_, 8, v_snapshotTasks_6810_);
v___x_6819_ = v_reuseFailAlloc_6823_;
goto v_reusejp_6818_;
}
v_reusejp_6818_:
{
lean_object* v___x_6820_; lean_object* v___x_6821_; lean_object* v___x_6822_; 
v___x_6820_ = lean_st_ref_set(v___y_6798_, v___x_6819_);
v___x_6821_ = lean_box(0);
v___x_6822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6822_, 0, v___x_6821_);
return v___x_6822_;
}
}
}
v___jp_6825_:
{
lean_object* v___x_6834_; lean_object* v___x_6835_; lean_object* v_a_6836_; lean_object* v___x_6838_; uint8_t v_isShared_6839_; uint8_t v_isSharedCheck_6849_; 
v___x_6834_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6783_);
v___x_6835_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6834_, v___y_6786_, v___y_6787_);
v_a_6836_ = lean_ctor_get(v___x_6835_, 0);
v_isSharedCheck_6849_ = !lean_is_exclusive(v___x_6835_);
if (v_isSharedCheck_6849_ == 0)
{
v___x_6838_ = v___x_6835_;
v_isShared_6839_ = v_isSharedCheck_6849_;
goto v_resetjp_6837_;
}
else
{
lean_inc(v_a_6836_);
lean_dec(v___x_6835_);
v___x_6838_ = lean_box(0);
v_isShared_6839_ = v_isSharedCheck_6849_;
goto v_resetjp_6837_;
}
v_resetjp_6837_:
{
lean_object* v___x_6840_; lean_object* v___x_6841_; lean_object* v___x_6842_; lean_object* v___x_6843_; 
lean_inc_ref_n(v___y_6830_, 2);
v___x_6840_ = l_Lean_FileMap_toPosition(v___y_6830_, v___y_6827_);
lean_dec(v___y_6827_);
v___x_6841_ = l_Lean_FileMap_toPosition(v___y_6830_, v___y_6833_);
lean_dec(v___y_6833_);
v___x_6842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6842_, 0, v___x_6841_);
v___x_6843_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6828_ == 0)
{
lean_del_object(v___x_6838_);
lean_dec_ref(v___y_6826_);
v___y_6790_ = v_a_6836_;
v___y_6791_ = v___x_6842_;
v___y_6792_ = v___x_6843_;
v___y_6793_ = v___y_6829_;
v___y_6794_ = v___x_6840_;
v___y_6795_ = v___y_6831_;
v___y_6796_ = v___y_6832_;
v___y_6797_ = v___y_6786_;
v___y_6798_ = v___y_6787_;
goto v___jp_6789_;
}
else
{
uint8_t v___x_6844_; 
lean_inc(v_a_6836_);
v___x_6844_ = l_Lean_MessageData_hasTag(v___y_6826_, v_a_6836_);
if (v___x_6844_ == 0)
{
lean_object* v___x_6845_; lean_object* v___x_6847_; 
lean_dec_ref_known(v___x_6842_, 1);
lean_dec_ref(v___x_6840_);
lean_dec(v_a_6836_);
v___x_6845_ = lean_box(0);
if (v_isShared_6839_ == 0)
{
lean_ctor_set(v___x_6838_, 0, v___x_6845_);
v___x_6847_ = v___x_6838_;
goto v_reusejp_6846_;
}
else
{
lean_object* v_reuseFailAlloc_6848_; 
v_reuseFailAlloc_6848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6848_, 0, v___x_6845_);
v___x_6847_ = v_reuseFailAlloc_6848_;
goto v_reusejp_6846_;
}
v_reusejp_6846_:
{
return v___x_6847_;
}
}
else
{
lean_del_object(v___x_6838_);
v___y_6790_ = v_a_6836_;
v___y_6791_ = v___x_6842_;
v___y_6792_ = v___x_6843_;
v___y_6793_ = v___y_6829_;
v___y_6794_ = v___x_6840_;
v___y_6795_ = v___y_6831_;
v___y_6796_ = v___y_6832_;
v___y_6797_ = v___y_6786_;
v___y_6798_ = v___y_6787_;
goto v___jp_6789_;
}
}
}
}
v___jp_6850_:
{
lean_object* v___x_6859_; 
v___x_6859_ = l_Lean_Syntax_getTailPos_x3f(v___y_6853_, v___y_6854_);
lean_dec(v___y_6853_);
if (lean_obj_tag(v___x_6859_) == 0)
{
lean_inc(v___y_6858_);
v___y_6826_ = v___y_6851_;
v___y_6827_ = v___y_6858_;
v___y_6828_ = v___y_6852_;
v___y_6829_ = v___y_6854_;
v___y_6830_ = v___y_6855_;
v___y_6831_ = v___y_6856_;
v___y_6832_ = v___y_6857_;
v___y_6833_ = v___y_6858_;
goto v___jp_6825_;
}
else
{
lean_object* v_val_6860_; 
v_val_6860_ = lean_ctor_get(v___x_6859_, 0);
lean_inc(v_val_6860_);
lean_dec_ref_known(v___x_6859_, 1);
v___y_6826_ = v___y_6851_;
v___y_6827_ = v___y_6858_;
v___y_6828_ = v___y_6852_;
v___y_6829_ = v___y_6854_;
v___y_6830_ = v___y_6855_;
v___y_6831_ = v___y_6856_;
v___y_6832_ = v___y_6857_;
v___y_6833_ = v_val_6860_;
goto v___jp_6825_;
}
}
v___jp_6861_:
{
lean_object* v_ref_6869_; lean_object* v___x_6870_; 
v_ref_6869_ = l_Lean_replaceRef(v_ref_6782_, v___y_6865_);
v___x_6870_ = l_Lean_Syntax_getPos_x3f(v_ref_6869_, v___y_6864_);
if (lean_obj_tag(v___x_6870_) == 0)
{
lean_object* v___x_6871_; 
v___x_6871_ = lean_unsigned_to_nat(0u);
v___y_6851_ = v___y_6862_;
v___y_6852_ = v___y_6863_;
v___y_6853_ = v_ref_6869_;
v___y_6854_ = v___y_6864_;
v___y_6855_ = v___y_6866_;
v___y_6856_ = v___y_6867_;
v___y_6857_ = v___y_6868_;
v___y_6858_ = v___x_6871_;
goto v___jp_6850_;
}
else
{
lean_object* v_val_6872_; 
v_val_6872_ = lean_ctor_get(v___x_6870_, 0);
lean_inc(v_val_6872_);
lean_dec_ref_known(v___x_6870_, 1);
v___y_6851_ = v___y_6862_;
v___y_6852_ = v___y_6863_;
v___y_6853_ = v_ref_6869_;
v___y_6854_ = v___y_6864_;
v___y_6855_ = v___y_6866_;
v___y_6856_ = v___y_6867_;
v___y_6857_ = v___y_6868_;
v___y_6858_ = v_val_6872_;
goto v___jp_6850_;
}
}
v___jp_6874_:
{
if (v___y_6881_ == 0)
{
v___y_6862_ = v___y_6879_;
v___y_6863_ = v___y_6875_;
v___y_6864_ = v___y_6880_;
v___y_6865_ = v___y_6876_;
v___y_6866_ = v___y_6877_;
v___y_6867_ = v___y_6878_;
v___y_6868_ = v_severity_6784_;
goto v___jp_6861_;
}
else
{
v___y_6862_ = v___y_6879_;
v___y_6863_ = v___y_6875_;
v___y_6864_ = v___y_6880_;
v___y_6865_ = v___y_6876_;
v___y_6866_ = v___y_6877_;
v___y_6867_ = v___y_6878_;
v___y_6868_ = v___x_6873_;
goto v___jp_6861_;
}
}
v___jp_6882_:
{
if (v___y_6883_ == 0)
{
lean_object* v_fileName_6884_; lean_object* v_fileMap_6885_; lean_object* v_options_6886_; lean_object* v_ref_6887_; uint8_t v_suppressElabErrors_6888_; lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v___f_6891_; uint8_t v___x_6892_; uint8_t v___x_6893_; 
v_fileName_6884_ = lean_ctor_get(v___y_6786_, 0);
v_fileMap_6885_ = lean_ctor_get(v___y_6786_, 1);
v_options_6886_ = lean_ctor_get(v___y_6786_, 2);
v_ref_6887_ = lean_ctor_get(v___y_6786_, 5);
v_suppressElabErrors_6888_ = lean_ctor_get_uint8(v___y_6786_, sizeof(void*)*14 + 1);
v___x_6889_ = lean_box(v___y_6883_);
v___x_6890_ = lean_box(v_suppressElabErrors_6888_);
v___f_6891_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6891_, 0, v___x_6889_);
lean_closure_set(v___f_6891_, 1, v___x_6890_);
v___x_6892_ = 1;
v___x_6893_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6784_, v___x_6892_);
if (v___x_6893_ == 0)
{
v___y_6875_ = v_suppressElabErrors_6888_;
v___y_6876_ = v_ref_6887_;
v___y_6877_ = v_fileMap_6885_;
v___y_6878_ = v_fileName_6884_;
v___y_6879_ = v___f_6891_;
v___y_6880_ = v___y_6883_;
v___y_6881_ = v___x_6893_;
goto v___jp_6874_;
}
else
{
lean_object* v___x_6894_; uint8_t v___x_6895_; 
v___x_6894_ = l_Lean_warningAsError;
v___x_6895_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6886_, v___x_6894_);
v___y_6875_ = v_suppressElabErrors_6888_;
v___y_6876_ = v_ref_6887_;
v___y_6877_ = v_fileMap_6885_;
v___y_6878_ = v_fileName_6884_;
v___y_6879_ = v___f_6891_;
v___y_6880_ = v___y_6883_;
v___y_6881_ = v___x_6895_;
goto v___jp_6874_;
}
}
else
{
lean_object* v___x_6896_; lean_object* v___x_6897_; 
lean_dec_ref(v_msgData_6783_);
v___x_6896_ = lean_box(0);
v___x_6897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6897_, 0, v___x_6896_);
return v___x_6897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6900_, lean_object* v_msgData_6901_, lean_object* v_severity_6902_, lean_object* v_isSilent_6903_, lean_object* v___y_6904_, lean_object* v___y_6905_, lean_object* v___y_6906_){
_start:
{
uint8_t v_severity_boxed_6907_; uint8_t v_isSilent_boxed_6908_; lean_object* v_res_6909_; 
v_severity_boxed_6907_ = lean_unbox(v_severity_6902_);
v_isSilent_boxed_6908_ = lean_unbox(v_isSilent_6903_);
v_res_6909_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6900_, v_msgData_6901_, v_severity_boxed_6907_, v_isSilent_boxed_6908_, v___y_6904_, v___y_6905_);
lean_dec(v___y_6905_);
lean_dec_ref(v___y_6904_);
lean_dec(v_ref_6900_);
return v_res_6909_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6910_, uint8_t v_severity_6911_, uint8_t v_isSilent_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_){
_start:
{
lean_object* v_ref_6916_; lean_object* v___x_6917_; 
v_ref_6916_ = lean_ctor_get(v___y_6913_, 5);
v___x_6917_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6916_, v_msgData_6910_, v_severity_6911_, v_isSilent_6912_, v___y_6913_, v___y_6914_);
return v___x_6917_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6918_, lean_object* v_severity_6919_, lean_object* v_isSilent_6920_, lean_object* v___y_6921_, lean_object* v___y_6922_, lean_object* v___y_6923_){
_start:
{
uint8_t v_severity_boxed_6924_; uint8_t v_isSilent_boxed_6925_; lean_object* v_res_6926_; 
v_severity_boxed_6924_ = lean_unbox(v_severity_6919_);
v_isSilent_boxed_6925_ = lean_unbox(v_isSilent_6920_);
v_res_6926_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6918_, v_severity_boxed_6924_, v_isSilent_boxed_6925_, v___y_6921_, v___y_6922_);
lean_dec(v___y_6922_);
lean_dec_ref(v___y_6921_);
return v_res_6926_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6927_, lean_object* v___y_6928_, lean_object* v___y_6929_){
_start:
{
uint8_t v___x_6931_; uint8_t v___x_6932_; lean_object* v___x_6933_; 
v___x_6931_ = 2;
v___x_6932_ = 0;
v___x_6933_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6927_, v___x_6931_, v___x_6932_, v___y_6928_, v___y_6929_);
return v___x_6933_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6934_, lean_object* v___y_6935_, lean_object* v___y_6936_, lean_object* v___y_6937_){
_start:
{
lean_object* v_res_6938_; 
v_res_6938_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6934_, v___y_6935_, v___y_6936_);
lean_dec(v___y_6936_);
lean_dec_ref(v___y_6935_);
return v_res_6938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6939_, lean_object* v___y_6940_, lean_object* v___y_6941_){
_start:
{
lean_object* v_module_6943_; lean_object* v_const_6944_; lean_object* v_exception_6945_; lean_object* v___x_6946_; lean_object* v___x_6947_; lean_object* v___x_6948_; lean_object* v___x_6949_; lean_object* v___x_6950_; lean_object* v___x_6951_; lean_object* v___x_6952_; lean_object* v___x_6953_; lean_object* v___x_6954_; lean_object* v___x_6955_; lean_object* v___x_6956_; lean_object* v___x_6957_; 
v_module_6943_ = lean_ctor_get(v_f_6939_, 0);
lean_inc(v_module_6943_);
v_const_6944_ = lean_ctor_get(v_f_6939_, 1);
lean_inc(v_const_6944_);
v_exception_6945_ = lean_ctor_get(v_f_6939_, 2);
lean_inc_ref(v_exception_6945_);
lean_dec_ref(v_f_6939_);
v___x_6946_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6947_ = l_Lean_MessageData_ofName(v_const_6944_);
v___x_6948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6948_, 0, v___x_6946_);
lean_ctor_set(v___x_6948_, 1, v___x_6947_);
v___x_6949_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6950_, 0, v___x_6948_);
lean_ctor_set(v___x_6950_, 1, v___x_6949_);
v___x_6951_ = l_Lean_MessageData_ofName(v_module_6943_);
v___x_6952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6952_, 0, v___x_6950_);
lean_ctor_set(v___x_6952_, 1, v___x_6951_);
v___x_6953_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6954_, 0, v___x_6952_);
lean_ctor_set(v___x_6954_, 1, v___x_6953_);
v___x_6955_ = l_Lean_Exception_toMessageData(v_exception_6945_);
v___x_6956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6956_, 0, v___x_6954_);
lean_ctor_set(v___x_6956_, 1, v___x_6955_);
v___x_6957_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6956_, v___y_6940_, v___y_6941_);
return v___x_6957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6958_, lean_object* v___y_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_){
_start:
{
lean_object* v_res_6962_; 
v_res_6962_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6958_, v___y_6959_, v___y_6960_);
lean_dec(v___y_6960_);
lean_dec_ref(v___y_6959_);
return v_res_6962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_6963_, size_t v_i_6964_, size_t v_stop_6965_, lean_object* v_b_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_){
_start:
{
uint8_t v___x_6970_; 
v___x_6970_ = lean_usize_dec_eq(v_i_6964_, v_stop_6965_);
if (v___x_6970_ == 0)
{
lean_object* v___x_6971_; lean_object* v___x_6972_; 
v___x_6971_ = lean_array_uget_borrowed(v_as_6963_, v_i_6964_);
lean_inc(v___x_6971_);
v___x_6972_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_6971_, v___y_6967_, v___y_6968_);
if (lean_obj_tag(v___x_6972_) == 0)
{
lean_object* v_a_6973_; size_t v___x_6974_; size_t v___x_6975_; 
v_a_6973_ = lean_ctor_get(v___x_6972_, 0);
lean_inc(v_a_6973_);
lean_dec_ref_known(v___x_6972_, 1);
v___x_6974_ = ((size_t)1ULL);
v___x_6975_ = lean_usize_add(v_i_6964_, v___x_6974_);
v_i_6964_ = v___x_6975_;
v_b_6966_ = v_a_6973_;
goto _start;
}
else
{
return v___x_6972_;
}
}
else
{
lean_object* v___x_6977_; 
v___x_6977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6977_, 0, v_b_6966_);
return v___x_6977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_6978_, lean_object* v_i_6979_, lean_object* v_stop_6980_, lean_object* v_b_6981_, lean_object* v___y_6982_, lean_object* v___y_6983_, lean_object* v___y_6984_){
_start:
{
size_t v_i_boxed_6985_; size_t v_stop_boxed_6986_; lean_object* v_res_6987_; 
v_i_boxed_6985_ = lean_unbox_usize(v_i_6979_);
lean_dec(v_i_6979_);
v_stop_boxed_6986_ = lean_unbox_usize(v_stop_6980_);
lean_dec(v_stop_6980_);
v_res_6987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_6978_, v_i_boxed_6985_, v_stop_boxed_6986_, v_b_6981_, v___y_6982_, v___y_6983_);
lean_dec(v___y_6983_);
lean_dec_ref(v___y_6982_);
lean_dec_ref(v_as_6978_);
return v_res_6987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_6988_, lean_object* v_a_6989_, lean_object* v_a_6990_){
_start:
{
lean_object* v___x_6992_; lean_object* v___x_6993_; lean_object* v_a_6994_; lean_object* v___x_6996_; uint8_t v_isShared_6997_; uint8_t v_isSharedCheck_7028_; 
v___x_6992_ = lean_st_ref_get(v_a_6990_);
v___x_6993_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_6990_);
v_a_6994_ = lean_ctor_get(v___x_6993_, 0);
v_isSharedCheck_7028_ = !lean_is_exclusive(v___x_6993_);
if (v_isSharedCheck_7028_ == 0)
{
v___x_6996_ = v___x_6993_;
v_isShared_6997_ = v_isSharedCheck_7028_;
goto v_resetjp_6995_;
}
else
{
lean_inc(v_a_6994_);
lean_dec(v___x_6993_);
v___x_6996_ = lean_box(0);
v_isShared_6997_ = v_isSharedCheck_7028_;
goto v_resetjp_6995_;
}
v_resetjp_6995_:
{
lean_object* v___x_6998_; lean_object* v_env_6999_; lean_object* v___x_7000_; lean_object* v___y_7007_; lean_object* v___x_7016_; lean_object* v___x_7017_; lean_object* v___x_7018_; uint8_t v___x_7019_; 
v___x_6998_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_6999_ = lean_ctor_get(v___x_6992_, 0);
lean_inc_ref(v_env_6999_);
lean_dec(v___x_6992_);
lean_inc_ref(v_a_6989_);
v___x_7000_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_6989_, v_a_6994_, v_env_6999_, v___x_6998_, v_entriesForConst_6988_);
v___x_7016_ = lean_st_ref_get(v___x_6998_);
lean_dec(v___x_6998_);
v___x_7017_ = lean_unsigned_to_nat(0u);
v___x_7018_ = lean_array_get_size(v___x_7016_);
v___x_7019_ = lean_nat_dec_lt(v___x_7017_, v___x_7018_);
if (v___x_7019_ == 0)
{
lean_dec(v___x_7016_);
goto v___jp_7001_;
}
else
{
lean_object* v___x_7020_; uint8_t v___x_7021_; 
v___x_7020_ = lean_box(0);
v___x_7021_ = lean_nat_dec_le(v___x_7018_, v___x_7018_);
if (v___x_7021_ == 0)
{
if (v___x_7019_ == 0)
{
lean_dec(v___x_7016_);
goto v___jp_7001_;
}
else
{
size_t v___x_7022_; size_t v___x_7023_; lean_object* v___x_7024_; 
v___x_7022_ = ((size_t)0ULL);
v___x_7023_ = lean_usize_of_nat(v___x_7018_);
v___x_7024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7016_, v___x_7022_, v___x_7023_, v___x_7020_, v_a_6989_, v_a_6990_);
lean_dec(v___x_7016_);
v___y_7007_ = v___x_7024_;
goto v___jp_7006_;
}
}
else
{
size_t v___x_7025_; size_t v___x_7026_; lean_object* v___x_7027_; 
v___x_7025_ = ((size_t)0ULL);
v___x_7026_ = lean_usize_of_nat(v___x_7018_);
v___x_7027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7016_, v___x_7025_, v___x_7026_, v___x_7020_, v_a_6989_, v_a_6990_);
lean_dec(v___x_7016_);
v___y_7007_ = v___x_7027_;
goto v___jp_7006_;
}
}
v___jp_7001_:
{
lean_object* v___x_7002_; lean_object* v___x_7004_; 
v___x_7002_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7000_);
if (v_isShared_6997_ == 0)
{
lean_ctor_set(v___x_6996_, 0, v___x_7002_);
v___x_7004_ = v___x_6996_;
goto v_reusejp_7003_;
}
else
{
lean_object* v_reuseFailAlloc_7005_; 
v_reuseFailAlloc_7005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7005_, 0, v___x_7002_);
v___x_7004_ = v_reuseFailAlloc_7005_;
goto v_reusejp_7003_;
}
v_reusejp_7003_:
{
return v___x_7004_;
}
}
v___jp_7006_:
{
if (lean_obj_tag(v___y_7007_) == 0)
{
lean_dec_ref_known(v___y_7007_, 1);
goto v___jp_7001_;
}
else
{
lean_object* v_a_7008_; lean_object* v___x_7010_; uint8_t v_isShared_7011_; uint8_t v_isSharedCheck_7015_; 
lean_dec_ref(v___x_7000_);
lean_del_object(v___x_6996_);
v_a_7008_ = lean_ctor_get(v___y_7007_, 0);
v_isSharedCheck_7015_ = !lean_is_exclusive(v___y_7007_);
if (v_isSharedCheck_7015_ == 0)
{
v___x_7010_ = v___y_7007_;
v_isShared_7011_ = v_isSharedCheck_7015_;
goto v_resetjp_7009_;
}
else
{
lean_inc(v_a_7008_);
lean_dec(v___y_7007_);
v___x_7010_ = lean_box(0);
v_isShared_7011_ = v_isSharedCheck_7015_;
goto v_resetjp_7009_;
}
v_resetjp_7009_:
{
lean_object* v___x_7013_; 
if (v_isShared_7011_ == 0)
{
v___x_7013_ = v___x_7010_;
goto v_reusejp_7012_;
}
else
{
lean_object* v_reuseFailAlloc_7014_; 
v_reuseFailAlloc_7014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7014_, 0, v_a_7008_);
v___x_7013_ = v_reuseFailAlloc_7014_;
goto v_reusejp_7012_;
}
v_reusejp_7012_:
{
return v___x_7013_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7029_, lean_object* v_a_7030_, lean_object* v_a_7031_, lean_object* v_a_7032_){
_start:
{
lean_object* v_res_7033_; 
v_res_7033_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7029_, v_a_7030_, v_a_7031_);
lean_dec(v_a_7031_);
lean_dec_ref(v_a_7030_);
return v_res_7033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7034_, lean_object* v_entriesForConst_7035_, lean_object* v_a_7036_, lean_object* v_a_7037_){
_start:
{
lean_object* v___x_7039_; 
v___x_7039_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7035_, v_a_7036_, v_a_7037_);
return v___x_7039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7040_, lean_object* v_entriesForConst_7041_, lean_object* v_a_7042_, lean_object* v_a_7043_, lean_object* v_a_7044_){
_start:
{
lean_object* v_res_7045_; 
v_res_7045_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7040_, v_entriesForConst_7041_, v_a_7042_, v_a_7043_);
lean_dec(v_a_7043_);
lean_dec_ref(v_a_7042_);
return v_res_7045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7046_, lean_object* v_droppedEntriesRef_7047_, lean_object* v_droppedKeys_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_, lean_object* v___y_7051_, lean_object* v___y_7052_){
_start:
{
lean_object* v_t_7055_; lean_object* v___x_7058_; 
v___x_7058_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7046_, v___y_7051_, v___y_7052_);
if (lean_obj_tag(v___x_7058_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7047_) == 1)
{
lean_object* v_a_7059_; lean_object* v_val_7060_; lean_object* v___x_7062_; uint8_t v_isShared_7063_; uint8_t v_isSharedCheck_7086_; 
v_a_7059_ = lean_ctor_get(v___x_7058_, 0);
lean_inc(v_a_7059_);
lean_dec_ref_known(v___x_7058_, 1);
v_val_7060_ = lean_ctor_get(v_droppedEntriesRef_7047_, 0);
v_isSharedCheck_7086_ = !lean_is_exclusive(v_droppedEntriesRef_7047_);
if (v_isSharedCheck_7086_ == 0)
{
v___x_7062_ = v_droppedEntriesRef_7047_;
v_isShared_7063_ = v_isSharedCheck_7086_;
goto v_resetjp_7061_;
}
else
{
lean_inc(v_val_7060_);
lean_dec(v_droppedEntriesRef_7047_);
v___x_7062_ = lean_box(0);
v_isShared_7063_ = v_isSharedCheck_7086_;
goto v_resetjp_7061_;
}
v_resetjp_7061_:
{
lean_object* v___x_7064_; 
v___x_7064_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7059_, v_droppedKeys_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_);
lean_dec(v_droppedKeys_7048_);
if (lean_obj_tag(v___x_7064_) == 0)
{
lean_object* v_a_7065_; lean_object* v_fst_7066_; lean_object* v_snd_7067_; lean_object* v___x_7068_; lean_object* v___y_7070_; 
v_a_7065_ = lean_ctor_get(v___x_7064_, 0);
lean_inc(v_a_7065_);
lean_dec_ref_known(v___x_7064_, 1);
v_fst_7066_ = lean_ctor_get(v_a_7065_, 0);
lean_inc(v_fst_7066_);
v_snd_7067_ = lean_ctor_get(v_a_7065_, 1);
lean_inc(v_snd_7067_);
lean_dec(v_a_7065_);
v___x_7068_ = lean_st_ref_get(v_val_7060_);
if (lean_obj_tag(v___x_7068_) == 0)
{
lean_object* v___x_7076_; 
v___x_7076_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7070_ = v___x_7076_;
goto v___jp_7069_;
}
else
{
lean_object* v_val_7077_; 
v_val_7077_ = lean_ctor_get(v___x_7068_, 0);
lean_inc(v_val_7077_);
lean_dec_ref_known(v___x_7068_, 1);
v___y_7070_ = v_val_7077_;
goto v___jp_7069_;
}
v___jp_7069_:
{
lean_object* v___x_7071_; lean_object* v___x_7073_; 
v___x_7071_ = l_Array_append___redArg(v___y_7070_, v_fst_7066_);
lean_dec(v_fst_7066_);
if (v_isShared_7063_ == 0)
{
lean_ctor_set(v___x_7062_, 0, v___x_7071_);
v___x_7073_ = v___x_7062_;
goto v_reusejp_7072_;
}
else
{
lean_object* v_reuseFailAlloc_7075_; 
v_reuseFailAlloc_7075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7075_, 0, v___x_7071_);
v___x_7073_ = v_reuseFailAlloc_7075_;
goto v_reusejp_7072_;
}
v_reusejp_7072_:
{
lean_object* v___x_7074_; 
v___x_7074_ = lean_st_ref_set(v_val_7060_, v___x_7073_);
lean_dec(v_val_7060_);
v_t_7055_ = v_snd_7067_;
goto v___jp_7054_;
}
}
}
else
{
lean_object* v_a_7078_; lean_object* v___x_7080_; uint8_t v_isShared_7081_; uint8_t v_isSharedCheck_7085_; 
lean_del_object(v___x_7062_);
lean_dec(v_val_7060_);
v_a_7078_ = lean_ctor_get(v___x_7064_, 0);
v_isSharedCheck_7085_ = !lean_is_exclusive(v___x_7064_);
if (v_isSharedCheck_7085_ == 0)
{
v___x_7080_ = v___x_7064_;
v_isShared_7081_ = v_isSharedCheck_7085_;
goto v_resetjp_7079_;
}
else
{
lean_inc(v_a_7078_);
lean_dec(v___x_7064_);
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
else
{
lean_object* v_a_7087_; lean_object* v___x_7088_; 
lean_dec(v_droppedEntriesRef_7047_);
v_a_7087_ = lean_ctor_get(v___x_7058_, 0);
lean_inc(v_a_7087_);
lean_dec_ref_known(v___x_7058_, 1);
v___x_7088_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7087_, v_droppedKeys_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_);
if (lean_obj_tag(v___x_7088_) == 0)
{
lean_object* v_a_7089_; 
v_a_7089_ = lean_ctor_get(v___x_7088_, 0);
lean_inc(v_a_7089_);
lean_dec_ref_known(v___x_7088_, 1);
v_t_7055_ = v_a_7089_;
goto v___jp_7054_;
}
else
{
lean_object* v_a_7090_; lean_object* v___x_7092_; uint8_t v_isShared_7093_; uint8_t v_isSharedCheck_7097_; 
v_a_7090_ = lean_ctor_get(v___x_7088_, 0);
v_isSharedCheck_7097_ = !lean_is_exclusive(v___x_7088_);
if (v_isSharedCheck_7097_ == 0)
{
v___x_7092_ = v___x_7088_;
v_isShared_7093_ = v_isSharedCheck_7097_;
goto v_resetjp_7091_;
}
else
{
lean_inc(v_a_7090_);
lean_dec(v___x_7088_);
v___x_7092_ = lean_box(0);
v_isShared_7093_ = v_isSharedCheck_7097_;
goto v_resetjp_7091_;
}
v_resetjp_7091_:
{
lean_object* v___x_7095_; 
if (v_isShared_7093_ == 0)
{
v___x_7095_ = v___x_7092_;
goto v_reusejp_7094_;
}
else
{
lean_object* v_reuseFailAlloc_7096_; 
v_reuseFailAlloc_7096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7096_, 0, v_a_7090_);
v___x_7095_ = v_reuseFailAlloc_7096_;
goto v_reusejp_7094_;
}
v_reusejp_7094_:
{
return v___x_7095_;
}
}
}
}
}
else
{
lean_object* v_a_7098_; lean_object* v___x_7100_; uint8_t v_isShared_7101_; uint8_t v_isSharedCheck_7105_; 
lean_dec(v_droppedKeys_7048_);
lean_dec(v_droppedEntriesRef_7047_);
v_a_7098_ = lean_ctor_get(v___x_7058_, 0);
v_isSharedCheck_7105_ = !lean_is_exclusive(v___x_7058_);
if (v_isSharedCheck_7105_ == 0)
{
v___x_7100_ = v___x_7058_;
v_isShared_7101_ = v_isSharedCheck_7105_;
goto v_resetjp_7099_;
}
else
{
lean_inc(v_a_7098_);
lean_dec(v___x_7058_);
v___x_7100_ = lean_box(0);
v_isShared_7101_ = v_isSharedCheck_7105_;
goto v_resetjp_7099_;
}
v_resetjp_7099_:
{
lean_object* v___x_7103_; 
if (v_isShared_7101_ == 0)
{
v___x_7103_ = v___x_7100_;
goto v_reusejp_7102_;
}
else
{
lean_object* v_reuseFailAlloc_7104_; 
v_reuseFailAlloc_7104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7104_, 0, v_a_7098_);
v___x_7103_ = v_reuseFailAlloc_7104_;
goto v_reusejp_7102_;
}
v_reusejp_7102_:
{
return v___x_7103_;
}
}
}
v___jp_7054_:
{
lean_object* v___x_7056_; lean_object* v___x_7057_; 
v___x_7056_ = lean_st_mk_ref(v_t_7055_);
v___x_7057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7057_, 0, v___x_7056_);
return v___x_7057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7106_, lean_object* v_droppedEntriesRef_7107_, lean_object* v_droppedKeys_7108_, lean_object* v___y_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_, lean_object* v___y_7112_, lean_object* v___y_7113_){
_start:
{
lean_object* v_res_7114_; 
v_res_7114_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7106_, v_droppedEntriesRef_7107_, v_droppedKeys_7108_, v___y_7109_, v___y_7110_, v___y_7111_, v___y_7112_);
lean_dec(v___y_7112_);
lean_dec_ref(v___y_7111_);
lean_dec(v___y_7110_);
lean_dec_ref(v___y_7109_);
return v_res_7114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7116_, lean_object* v_droppedKeys_7117_, lean_object* v_droppedEntriesRef_7118_, lean_object* v_a_7119_, lean_object* v_a_7120_, lean_object* v_a_7121_, lean_object* v_a_7122_){
_start:
{
lean_object* v_options_7124_; lean_object* v___f_7125_; lean_object* v___x_7126_; lean_object* v___x_7127_; lean_object* v___x_7128_; 
v_options_7124_ = lean_ctor_get(v_a_7121_, 2);
v___f_7125_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7125_, 0, v_entriesForConst_7116_);
lean_closure_set(v___f_7125_, 1, v_droppedEntriesRef_7118_);
lean_closure_set(v___f_7125_, 2, v_droppedKeys_7117_);
v___x_7126_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7127_ = lean_box(0);
v___x_7128_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7126_, v_options_7124_, v___f_7125_, v___x_7127_, v_a_7119_, v_a_7120_, v_a_7121_, v_a_7122_);
return v___x_7128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7129_, lean_object* v_droppedKeys_7130_, lean_object* v_droppedEntriesRef_7131_, lean_object* v_a_7132_, lean_object* v_a_7133_, lean_object* v_a_7134_, lean_object* v_a_7135_, lean_object* v_a_7136_){
_start:
{
lean_object* v_res_7137_; 
v_res_7137_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7129_, v_droppedKeys_7130_, v_droppedEntriesRef_7131_, v_a_7132_, v_a_7133_, v_a_7134_, v_a_7135_);
lean_dec(v_a_7135_);
lean_dec_ref(v_a_7134_);
lean_dec(v_a_7133_);
lean_dec_ref(v_a_7132_);
return v_res_7137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7138_, lean_object* v_entriesForConst_7139_, lean_object* v_droppedKeys_7140_, lean_object* v_droppedEntriesRef_7141_, lean_object* v_a_7142_, lean_object* v_a_7143_, lean_object* v_a_7144_, lean_object* v_a_7145_){
_start:
{
lean_object* v___x_7147_; 
v___x_7147_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7139_, v_droppedKeys_7140_, v_droppedEntriesRef_7141_, v_a_7142_, v_a_7143_, v_a_7144_, v_a_7145_);
return v___x_7147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7148_, lean_object* v_entriesForConst_7149_, lean_object* v_droppedKeys_7150_, lean_object* v_droppedEntriesRef_7151_, lean_object* v_a_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_, lean_object* v_a_7155_, lean_object* v_a_7156_){
_start:
{
lean_object* v_res_7157_; 
v_res_7157_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7148_, v_entriesForConst_7149_, v_droppedKeys_7150_, v_droppedEntriesRef_7151_, v_a_7152_, v_a_7153_, v_a_7154_, v_a_7155_);
lean_dec(v_a_7155_);
lean_dec_ref(v_a_7154_);
lean_dec(v_a_7153_);
lean_dec_ref(v_a_7152_);
return v_res_7157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7158_, lean_object* v_ty_7159_, lean_object* v___y_7160_, lean_object* v___y_7161_, lean_object* v___y_7162_, lean_object* v___y_7163_){
_start:
{
lean_object* v___x_7165_; lean_object* v___x_7166_; 
v___x_7165_ = lean_st_ref_get(v_moduleRef_7158_);
v___x_7166_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7165_, v_ty_7159_, v___y_7160_, v___y_7161_, v___y_7162_, v___y_7163_);
if (lean_obj_tag(v___x_7166_) == 0)
{
lean_object* v_a_7167_; lean_object* v___x_7169_; uint8_t v_isShared_7170_; uint8_t v_isSharedCheck_7177_; 
v_a_7167_ = lean_ctor_get(v___x_7166_, 0);
v_isSharedCheck_7177_ = !lean_is_exclusive(v___x_7166_);
if (v_isSharedCheck_7177_ == 0)
{
v___x_7169_ = v___x_7166_;
v_isShared_7170_ = v_isSharedCheck_7177_;
goto v_resetjp_7168_;
}
else
{
lean_inc(v_a_7167_);
lean_dec(v___x_7166_);
v___x_7169_ = lean_box(0);
v_isShared_7170_ = v_isSharedCheck_7177_;
goto v_resetjp_7168_;
}
v_resetjp_7168_:
{
lean_object* v_fst_7171_; lean_object* v_snd_7172_; lean_object* v___x_7173_; lean_object* v___x_7175_; 
v_fst_7171_ = lean_ctor_get(v_a_7167_, 0);
lean_inc(v_fst_7171_);
v_snd_7172_ = lean_ctor_get(v_a_7167_, 1);
lean_inc(v_snd_7172_);
lean_dec(v_a_7167_);
v___x_7173_ = lean_st_ref_set(v_moduleRef_7158_, v_snd_7172_);
if (v_isShared_7170_ == 0)
{
lean_ctor_set(v___x_7169_, 0, v_fst_7171_);
v___x_7175_ = v___x_7169_;
goto v_reusejp_7174_;
}
else
{
lean_object* v_reuseFailAlloc_7176_; 
v_reuseFailAlloc_7176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7176_, 0, v_fst_7171_);
v___x_7175_ = v_reuseFailAlloc_7176_;
goto v_reusejp_7174_;
}
v_reusejp_7174_:
{
return v___x_7175_;
}
}
}
else
{
lean_object* v_a_7178_; lean_object* v___x_7180_; uint8_t v_isShared_7181_; uint8_t v_isSharedCheck_7185_; 
v_a_7178_ = lean_ctor_get(v___x_7166_, 0);
v_isSharedCheck_7185_ = !lean_is_exclusive(v___x_7166_);
if (v_isSharedCheck_7185_ == 0)
{
v___x_7180_ = v___x_7166_;
v_isShared_7181_ = v_isSharedCheck_7185_;
goto v_resetjp_7179_;
}
else
{
lean_inc(v_a_7178_);
lean_dec(v___x_7166_);
v___x_7180_ = lean_box(0);
v_isShared_7181_ = v_isSharedCheck_7185_;
goto v_resetjp_7179_;
}
v_resetjp_7179_:
{
lean_object* v___x_7183_; 
if (v_isShared_7181_ == 0)
{
v___x_7183_ = v___x_7180_;
goto v_reusejp_7182_;
}
else
{
lean_object* v_reuseFailAlloc_7184_; 
v_reuseFailAlloc_7184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7184_, 0, v_a_7178_);
v___x_7183_ = v_reuseFailAlloc_7184_;
goto v_reusejp_7182_;
}
v_reusejp_7182_:
{
return v___x_7183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7186_, lean_object* v_ty_7187_, lean_object* v___y_7188_, lean_object* v___y_7189_, lean_object* v___y_7190_, lean_object* v___y_7191_, lean_object* v___y_7192_){
_start:
{
lean_object* v_res_7193_; 
v_res_7193_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7186_, v_ty_7187_, v___y_7188_, v___y_7189_, v___y_7190_, v___y_7191_);
lean_dec(v___y_7191_);
lean_dec_ref(v___y_7190_);
lean_dec(v___y_7189_);
lean_dec_ref(v___y_7188_);
lean_dec(v_moduleRef_7186_);
return v_res_7193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7195_, lean_object* v_ty_7196_, lean_object* v_a_7197_, lean_object* v_a_7198_, lean_object* v_a_7199_, lean_object* v_a_7200_){
_start:
{
lean_object* v_options_7202_; lean_object* v___f_7203_; lean_object* v___x_7204_; lean_object* v___x_7205_; lean_object* v___x_7206_; 
v_options_7202_ = lean_ctor_get(v_a_7199_, 2);
v___f_7203_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7203_, 0, v_moduleRef_7195_);
lean_closure_set(v___f_7203_, 1, v_ty_7196_);
v___x_7204_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7205_ = lean_box(0);
v___x_7206_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7204_, v_options_7202_, v___f_7203_, v___x_7205_, v_a_7197_, v_a_7198_, v_a_7199_, v_a_7200_);
return v___x_7206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7207_, lean_object* v_ty_7208_, lean_object* v_a_7209_, lean_object* v_a_7210_, lean_object* v_a_7211_, lean_object* v_a_7212_, lean_object* v_a_7213_){
_start:
{
lean_object* v_res_7214_; 
v_res_7214_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7207_, v_ty_7208_, v_a_7209_, v_a_7210_, v_a_7211_, v_a_7212_);
lean_dec(v_a_7212_);
lean_dec_ref(v_a_7211_);
lean_dec(v_a_7210_);
lean_dec_ref(v_a_7209_);
return v_res_7214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7215_, lean_object* v_moduleRef_7216_, lean_object* v_ty_7217_, lean_object* v_a_7218_, lean_object* v_a_7219_, lean_object* v_a_7220_, lean_object* v_a_7221_){
_start:
{
lean_object* v___x_7223_; 
v___x_7223_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7216_, v_ty_7217_, v_a_7218_, v_a_7219_, v_a_7220_, v_a_7221_);
return v___x_7223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7224_, lean_object* v_moduleRef_7225_, lean_object* v_ty_7226_, lean_object* v_a_7227_, lean_object* v_a_7228_, lean_object* v_a_7229_, lean_object* v_a_7230_, lean_object* v_a_7231_){
_start:
{
lean_object* v_res_7232_; 
v_res_7232_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7224_, v_moduleRef_7225_, v_ty_7226_, v_a_7227_, v_a_7228_, v_a_7229_, v_a_7230_);
lean_dec(v_a_7230_);
lean_dec_ref(v_a_7229_);
lean_dec(v_a_7228_);
lean_dec_ref(v_a_7227_);
return v_res_7232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7233_, lean_object* v_j_7234_, size_t v_sz_7235_, size_t v_i_7236_, lean_object* v_bs_7237_){
_start:
{
uint8_t v___x_7238_; 
v___x_7238_ = lean_usize_dec_lt(v_i_7236_, v_sz_7235_);
if (v___x_7238_ == 0)
{
lean_dec(v_j_7234_);
lean_dec(v_adjustResult_7233_);
return v_bs_7237_;
}
else
{
lean_object* v_v_7239_; lean_object* v___x_7240_; lean_object* v_bs_x27_7241_; lean_object* v___x_7242_; size_t v___x_7243_; size_t v___x_7244_; lean_object* v___x_7245_; 
v_v_7239_ = lean_array_uget(v_bs_7237_, v_i_7236_);
v___x_7240_ = lean_unsigned_to_nat(0u);
v_bs_x27_7241_ = lean_array_uset(v_bs_7237_, v_i_7236_, v___x_7240_);
lean_inc(v_adjustResult_7233_);
lean_inc(v_j_7234_);
v___x_7242_ = lean_apply_2(v_adjustResult_7233_, v_j_7234_, v_v_7239_);
v___x_7243_ = ((size_t)1ULL);
v___x_7244_ = lean_usize_add(v_i_7236_, v___x_7243_);
v___x_7245_ = lean_array_uset(v_bs_x27_7241_, v_i_7236_, v___x_7242_);
v_i_7236_ = v___x_7244_;
v_bs_7237_ = v___x_7245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7247_, lean_object* v_j_7248_, lean_object* v_sz_7249_, lean_object* v_i_7250_, lean_object* v_bs_7251_){
_start:
{
size_t v_sz_boxed_7252_; size_t v_i_boxed_7253_; lean_object* v_res_7254_; 
v_sz_boxed_7252_ = lean_unbox_usize(v_sz_7249_);
lean_dec(v_sz_7249_);
v_i_boxed_7253_ = lean_unbox_usize(v_i_7250_);
lean_dec(v_i_7250_);
v_res_7254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7247_, v_j_7248_, v_sz_boxed_7252_, v_i_boxed_7253_, v_bs_7251_);
return v_res_7254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7255_, lean_object* v_j_7256_, lean_object* v_as_7257_, size_t v_i_7258_, size_t v_stop_7259_, lean_object* v_b_7260_){
_start:
{
uint8_t v___x_7261_; 
v___x_7261_ = lean_usize_dec_eq(v_i_7258_, v_stop_7259_);
if (v___x_7261_ == 0)
{
lean_object* v___x_7262_; size_t v_sz_7263_; size_t v___x_7264_; lean_object* v___x_7265_; lean_object* v___x_7266_; size_t v___x_7267_; size_t v___x_7268_; 
v___x_7262_ = lean_array_uget_borrowed(v_as_7257_, v_i_7258_);
v_sz_7263_ = lean_array_size(v___x_7262_);
v___x_7264_ = ((size_t)0ULL);
lean_inc(v___x_7262_);
lean_inc(v_j_7256_);
lean_inc(v_adjustResult_7255_);
v___x_7265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7255_, v_j_7256_, v_sz_7263_, v___x_7264_, v___x_7262_);
v___x_7266_ = l_Array_append___redArg(v_b_7260_, v___x_7265_);
lean_dec_ref(v___x_7265_);
v___x_7267_ = ((size_t)1ULL);
v___x_7268_ = lean_usize_add(v_i_7258_, v___x_7267_);
v_i_7258_ = v___x_7268_;
v_b_7260_ = v___x_7266_;
goto _start;
}
else
{
lean_dec(v_j_7256_);
lean_dec(v_adjustResult_7255_);
return v_b_7260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7270_, lean_object* v_j_7271_, lean_object* v_as_7272_, lean_object* v_i_7273_, lean_object* v_stop_7274_, lean_object* v_b_7275_){
_start:
{
size_t v_i_boxed_7276_; size_t v_stop_boxed_7277_; lean_object* v_res_7278_; 
v_i_boxed_7276_ = lean_unbox_usize(v_i_7273_);
lean_dec(v_i_7273_);
v_stop_boxed_7277_ = lean_unbox_usize(v_stop_7274_);
lean_dec(v_stop_7274_);
v_res_7278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7270_, v_j_7271_, v_as_7272_, v_i_boxed_7276_, v_stop_boxed_7277_, v_b_7275_);
lean_dec_ref(v_as_7272_);
return v_res_7278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7279_, lean_object* v_aa_7280_, lean_object* v_adjustResult_7281_, lean_object* v_n_7282_, lean_object* v_j_7283_, lean_object* v_a_7284_){
_start:
{
lean_object* v_zero_7285_; uint8_t v_isZero_7286_; 
v_zero_7285_ = lean_unsigned_to_nat(0u);
v_isZero_7286_ = lean_nat_dec_eq(v_j_7283_, v_zero_7285_);
if (v_isZero_7286_ == 1)
{
lean_dec(v_j_7283_);
lean_dec(v_adjustResult_7281_);
return v_a_7284_;
}
else
{
lean_object* v_one_7287_; lean_object* v_n_7288_; lean_object* v___x_7289_; lean_object* v___x_7290_; lean_object* v_j_7291_; lean_object* v_b_7292_; lean_object* v___x_7293_; uint8_t v___x_7294_; 
v_one_7287_ = lean_unsigned_to_nat(1u);
v_n_7288_ = lean_nat_sub(v_j_7283_, v_one_7287_);
v___x_7289_ = lean_nat_sub(v_n_7282_, v_j_7283_);
lean_dec(v_j_7283_);
v___x_7290_ = lean_nat_sub(v_n_7279_, v_one_7287_);
v_j_7291_ = lean_nat_sub(v___x_7290_, v___x_7289_);
lean_dec(v___x_7289_);
lean_dec(v___x_7290_);
v_b_7292_ = lean_array_fget_borrowed(v_aa_7280_, v_j_7291_);
v___x_7293_ = lean_array_get_size(v_b_7292_);
v___x_7294_ = lean_nat_dec_lt(v_zero_7285_, v___x_7293_);
if (v___x_7294_ == 0)
{
lean_dec(v_j_7291_);
v_j_7283_ = v_n_7288_;
goto _start;
}
else
{
uint8_t v___x_7296_; 
v___x_7296_ = lean_nat_dec_le(v___x_7293_, v___x_7293_);
if (v___x_7296_ == 0)
{
if (v___x_7294_ == 0)
{
lean_dec(v_j_7291_);
v_j_7283_ = v_n_7288_;
goto _start;
}
else
{
size_t v___x_7298_; size_t v___x_7299_; lean_object* v___x_7300_; 
v___x_7298_ = ((size_t)0ULL);
v___x_7299_ = lean_usize_of_nat(v___x_7293_);
lean_inc(v_adjustResult_7281_);
v___x_7300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7281_, v_j_7291_, v_b_7292_, v___x_7298_, v___x_7299_, v_a_7284_);
v_j_7283_ = v_n_7288_;
v_a_7284_ = v___x_7300_;
goto _start;
}
}
else
{
size_t v___x_7302_; size_t v___x_7303_; lean_object* v___x_7304_; 
v___x_7302_ = ((size_t)0ULL);
v___x_7303_ = lean_usize_of_nat(v___x_7293_);
lean_inc(v_adjustResult_7281_);
v___x_7304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7281_, v_j_7291_, v_b_7292_, v___x_7302_, v___x_7303_, v_a_7284_);
v_j_7283_ = v_n_7288_;
v_a_7284_ = v___x_7304_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7306_, lean_object* v_aa_7307_, lean_object* v_adjustResult_7308_, lean_object* v_n_7309_, lean_object* v_j_7310_, lean_object* v_a_7311_){
_start:
{
lean_object* v_res_7312_; 
v_res_7312_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7306_, v_aa_7307_, v_adjustResult_7308_, v_n_7309_, v_j_7310_, v_a_7311_);
lean_dec(v_n_7309_);
lean_dec_ref(v_aa_7307_);
lean_dec(v_n_7306_);
return v_res_7312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7313_, lean_object* v_adjustResult_7314_, lean_object* v_aa_7315_, lean_object* v_n_7316_, lean_object* v_j_7317_, lean_object* v_a_7318_){
_start:
{
lean_object* v_zero_7319_; uint8_t v_isZero_7320_; 
v_zero_7319_ = lean_unsigned_to_nat(0u);
v_isZero_7320_ = lean_nat_dec_eq(v_j_7317_, v_zero_7319_);
if (v_isZero_7320_ == 1)
{
lean_dec(v_adjustResult_7314_);
return v_a_7318_;
}
else
{
lean_object* v_one_7321_; lean_object* v_n_7322_; lean_object* v___x_7323_; lean_object* v___x_7324_; lean_object* v_j_7325_; lean_object* v_b_7326_; lean_object* v___x_7327_; uint8_t v___x_7328_; 
v_one_7321_ = lean_unsigned_to_nat(1u);
v_n_7322_ = lean_nat_sub(v_j_7317_, v_one_7321_);
v___x_7323_ = lean_nat_sub(v_n_7316_, v_j_7317_);
v___x_7324_ = lean_nat_sub(v_n_7313_, v_one_7321_);
v_j_7325_ = lean_nat_sub(v___x_7324_, v___x_7323_);
lean_dec(v___x_7323_);
lean_dec(v___x_7324_);
v_b_7326_ = lean_array_fget_borrowed(v_aa_7315_, v_j_7325_);
v___x_7327_ = lean_array_get_size(v_b_7326_);
v___x_7328_ = lean_nat_dec_lt(v_zero_7319_, v___x_7327_);
if (v___x_7328_ == 0)
{
lean_object* v___x_7329_; 
lean_dec(v_j_7325_);
v___x_7329_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7313_, v_aa_7315_, v_adjustResult_7314_, v_n_7316_, v_n_7322_, v_a_7318_);
return v___x_7329_;
}
else
{
uint8_t v___x_7330_; 
v___x_7330_ = lean_nat_dec_le(v___x_7327_, v___x_7327_);
if (v___x_7330_ == 0)
{
if (v___x_7328_ == 0)
{
lean_object* v___x_7331_; 
lean_dec(v_j_7325_);
v___x_7331_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7313_, v_aa_7315_, v_adjustResult_7314_, v_n_7316_, v_n_7322_, v_a_7318_);
return v___x_7331_;
}
else
{
size_t v___x_7332_; size_t v___x_7333_; lean_object* v___x_7334_; lean_object* v___x_7335_; 
v___x_7332_ = ((size_t)0ULL);
v___x_7333_ = lean_usize_of_nat(v___x_7327_);
lean_inc(v_adjustResult_7314_);
v___x_7334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7314_, v_j_7325_, v_b_7326_, v___x_7332_, v___x_7333_, v_a_7318_);
v___x_7335_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7313_, v_aa_7315_, v_adjustResult_7314_, v_n_7316_, v_n_7322_, v___x_7334_);
return v___x_7335_;
}
}
else
{
size_t v___x_7336_; size_t v___x_7337_; lean_object* v___x_7338_; lean_object* v___x_7339_; 
v___x_7336_ = ((size_t)0ULL);
v___x_7337_ = lean_usize_of_nat(v___x_7327_);
lean_inc(v_adjustResult_7314_);
v___x_7338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7314_, v_j_7325_, v_b_7326_, v___x_7336_, v___x_7337_, v_a_7318_);
v___x_7339_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7313_, v_aa_7315_, v_adjustResult_7314_, v_n_7316_, v_n_7322_, v___x_7338_);
return v___x_7339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7340_, lean_object* v_adjustResult_7341_, lean_object* v_aa_7342_, lean_object* v_n_7343_, lean_object* v_j_7344_, lean_object* v_a_7345_){
_start:
{
lean_object* v_res_7346_; 
v_res_7346_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7340_, v_adjustResult_7341_, v_aa_7342_, v_n_7343_, v_j_7344_, v_a_7345_);
lean_dec(v_j_7344_);
lean_dec(v_n_7343_);
lean_dec_ref(v_aa_7342_);
lean_dec(v_n_7340_);
return v_res_7346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7347_, lean_object* v_mr_7348_, lean_object* v_a_7349_){
_start:
{
lean_object* v_n_7350_; lean_object* v___x_7351_; 
v_n_7350_ = lean_array_get_size(v_mr_7348_);
v___x_7351_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7350_, v_adjustResult_7347_, v_mr_7348_, v_n_7350_, v_n_7350_, v_a_7349_);
return v___x_7351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7352_, lean_object* v_mr_7353_, lean_object* v_a_7354_){
_start:
{
lean_object* v_res_7355_; 
v_res_7355_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7352_, v_mr_7353_, v_a_7354_);
lean_dec_ref(v_mr_7353_);
return v_res_7355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7356_, lean_object* v_ref_7357_, lean_object* v_addEntry_7358_, lean_object* v_droppedKeys_7359_, lean_object* v_constantsPerTask_7360_, lean_object* v_droppedEntriesRef_7361_, lean_object* v_adjustResult_7362_, lean_object* v_ty_7363_, lean_object* v_a_7364_, lean_object* v_a_7365_, lean_object* v_a_7366_, lean_object* v_a_7367_){
_start:
{
lean_object* v___x_7369_; 
lean_inc_ref(v_ty_7363_);
v___x_7369_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7356_, v_ty_7363_, v_a_7364_, v_a_7365_, v_a_7366_, v_a_7367_);
if (lean_obj_tag(v___x_7369_) == 0)
{
lean_object* v_a_7370_; lean_object* v___x_7371_; 
v_a_7370_ = lean_ctor_get(v___x_7369_, 0);
lean_inc(v_a_7370_);
lean_dec_ref_known(v___x_7369_, 1);
v___x_7371_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7357_, v_addEntry_7358_, v_droppedKeys_7359_, v_constantsPerTask_7360_, v_droppedEntriesRef_7361_, v_ty_7363_, v_a_7364_, v_a_7365_, v_a_7366_, v_a_7367_);
if (lean_obj_tag(v___x_7371_) == 0)
{
lean_object* v_a_7372_; lean_object* v___x_7374_; uint8_t v_isShared_7375_; uint8_t v_isSharedCheck_7385_; 
v_a_7372_ = lean_ctor_get(v___x_7371_, 0);
v_isSharedCheck_7385_ = !lean_is_exclusive(v___x_7371_);
if (v_isSharedCheck_7385_ == 0)
{
v___x_7374_ = v___x_7371_;
v_isShared_7375_ = v_isSharedCheck_7385_;
goto v_resetjp_7373_;
}
else
{
lean_inc(v_a_7372_);
lean_dec(v___x_7371_);
v___x_7374_ = lean_box(0);
v_isShared_7375_ = v_isSharedCheck_7385_;
goto v_resetjp_7373_;
}
v_resetjp_7373_:
{
lean_object* v___x_7376_; lean_object* v___x_7377_; lean_object* v___x_7378_; lean_object* v___x_7379_; lean_object* v___x_7380_; lean_object* v___x_7381_; lean_object* v___x_7383_; 
v___x_7376_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7370_);
v___x_7377_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7372_);
v___x_7378_ = lean_nat_add(v___x_7376_, v___x_7377_);
lean_dec(v___x_7377_);
lean_dec(v___x_7376_);
v___x_7379_ = lean_mk_empty_array_with_capacity(v___x_7378_);
lean_dec(v___x_7378_);
lean_inc(v_adjustResult_7362_);
v___x_7380_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7362_, v_a_7370_, v___x_7379_);
lean_dec(v_a_7370_);
v___x_7381_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7362_, v_a_7372_, v___x_7380_);
lean_dec(v_a_7372_);
if (v_isShared_7375_ == 0)
{
lean_ctor_set(v___x_7374_, 0, v___x_7381_);
v___x_7383_ = v___x_7374_;
goto v_reusejp_7382_;
}
else
{
lean_object* v_reuseFailAlloc_7384_; 
v_reuseFailAlloc_7384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7384_, 0, v___x_7381_);
v___x_7383_ = v_reuseFailAlloc_7384_;
goto v_reusejp_7382_;
}
v_reusejp_7382_:
{
return v___x_7383_;
}
}
}
else
{
lean_object* v_a_7386_; lean_object* v___x_7388_; uint8_t v_isShared_7389_; uint8_t v_isSharedCheck_7393_; 
lean_dec(v_a_7370_);
lean_dec(v_adjustResult_7362_);
v_a_7386_ = lean_ctor_get(v___x_7371_, 0);
v_isSharedCheck_7393_ = !lean_is_exclusive(v___x_7371_);
if (v_isSharedCheck_7393_ == 0)
{
v___x_7388_ = v___x_7371_;
v_isShared_7389_ = v_isSharedCheck_7393_;
goto v_resetjp_7387_;
}
else
{
lean_inc(v_a_7386_);
lean_dec(v___x_7371_);
v___x_7388_ = lean_box(0);
v_isShared_7389_ = v_isSharedCheck_7393_;
goto v_resetjp_7387_;
}
v_resetjp_7387_:
{
lean_object* v___x_7391_; 
if (v_isShared_7389_ == 0)
{
v___x_7391_ = v___x_7388_;
goto v_reusejp_7390_;
}
else
{
lean_object* v_reuseFailAlloc_7392_; 
v_reuseFailAlloc_7392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7392_, 0, v_a_7386_);
v___x_7391_ = v_reuseFailAlloc_7392_;
goto v_reusejp_7390_;
}
v_reusejp_7390_:
{
return v___x_7391_;
}
}
}
}
else
{
lean_object* v_a_7394_; lean_object* v___x_7396_; uint8_t v_isShared_7397_; uint8_t v_isSharedCheck_7401_; 
lean_dec_ref(v_ty_7363_);
lean_dec(v_adjustResult_7362_);
lean_dec(v_droppedEntriesRef_7361_);
lean_dec(v_constantsPerTask_7360_);
lean_dec(v_droppedKeys_7359_);
lean_dec_ref(v_addEntry_7358_);
v_a_7394_ = lean_ctor_get(v___x_7369_, 0);
v_isSharedCheck_7401_ = !lean_is_exclusive(v___x_7369_);
if (v_isSharedCheck_7401_ == 0)
{
v___x_7396_ = v___x_7369_;
v_isShared_7397_ = v_isSharedCheck_7401_;
goto v_resetjp_7395_;
}
else
{
lean_inc(v_a_7394_);
lean_dec(v___x_7369_);
v___x_7396_ = lean_box(0);
v_isShared_7397_ = v_isSharedCheck_7401_;
goto v_resetjp_7395_;
}
v_resetjp_7395_:
{
lean_object* v___x_7399_; 
if (v_isShared_7397_ == 0)
{
v___x_7399_ = v___x_7396_;
goto v_reusejp_7398_;
}
else
{
lean_object* v_reuseFailAlloc_7400_; 
v_reuseFailAlloc_7400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7400_, 0, v_a_7394_);
v___x_7399_ = v_reuseFailAlloc_7400_;
goto v_reusejp_7398_;
}
v_reusejp_7398_:
{
return v___x_7399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7402_, lean_object* v_ref_7403_, lean_object* v_addEntry_7404_, lean_object* v_droppedKeys_7405_, lean_object* v_constantsPerTask_7406_, lean_object* v_droppedEntriesRef_7407_, lean_object* v_adjustResult_7408_, lean_object* v_ty_7409_, lean_object* v_a_7410_, lean_object* v_a_7411_, lean_object* v_a_7412_, lean_object* v_a_7413_, lean_object* v_a_7414_){
_start:
{
lean_object* v_res_7415_; 
v_res_7415_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7402_, v_ref_7403_, v_addEntry_7404_, v_droppedKeys_7405_, v_constantsPerTask_7406_, v_droppedEntriesRef_7407_, v_adjustResult_7408_, v_ty_7409_, v_a_7410_, v_a_7411_, v_a_7412_, v_a_7413_);
lean_dec(v_a_7413_);
lean_dec_ref(v_a_7412_);
lean_dec(v_a_7411_);
lean_dec_ref(v_a_7410_);
lean_dec(v_ref_7403_);
return v_res_7415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7416_, lean_object* v_00_u03b2_7417_, lean_object* v_moduleTreeRef_7418_, lean_object* v_ref_7419_, lean_object* v_addEntry_7420_, lean_object* v_droppedKeys_7421_, lean_object* v_constantsPerTask_7422_, lean_object* v_droppedEntriesRef_7423_, lean_object* v_adjustResult_7424_, lean_object* v_ty_7425_, lean_object* v_a_7426_, lean_object* v_a_7427_, lean_object* v_a_7428_, lean_object* v_a_7429_){
_start:
{
lean_object* v___x_7431_; 
v___x_7431_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7418_, v_ref_7419_, v_addEntry_7420_, v_droppedKeys_7421_, v_constantsPerTask_7422_, v_droppedEntriesRef_7423_, v_adjustResult_7424_, v_ty_7425_, v_a_7426_, v_a_7427_, v_a_7428_, v_a_7429_);
return v___x_7431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7432_, lean_object* v_00_u03b2_7433_, lean_object* v_moduleTreeRef_7434_, lean_object* v_ref_7435_, lean_object* v_addEntry_7436_, lean_object* v_droppedKeys_7437_, lean_object* v_constantsPerTask_7438_, lean_object* v_droppedEntriesRef_7439_, lean_object* v_adjustResult_7440_, lean_object* v_ty_7441_, lean_object* v_a_7442_, lean_object* v_a_7443_, lean_object* v_a_7444_, lean_object* v_a_7445_, lean_object* v_a_7446_){
_start:
{
lean_object* v_res_7447_; 
v_res_7447_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7432_, v_00_u03b2_7433_, v_moduleTreeRef_7434_, v_ref_7435_, v_addEntry_7436_, v_droppedKeys_7437_, v_constantsPerTask_7438_, v_droppedEntriesRef_7439_, v_adjustResult_7440_, v_ty_7441_, v_a_7442_, v_a_7443_, v_a_7444_, v_a_7445_);
lean_dec(v_a_7445_);
lean_dec_ref(v_a_7444_);
lean_dec(v_a_7443_);
lean_dec_ref(v_a_7442_);
lean_dec(v_ref_7435_);
return v_res_7447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7448_, lean_object* v_00_u03b2_7449_, lean_object* v_adjustResult_7450_, lean_object* v_mr_7451_, lean_object* v_a_7452_){
_start:
{
lean_object* v___x_7453_; 
v___x_7453_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7450_, v_mr_7451_, v_a_7452_);
return v___x_7453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7454_, lean_object* v_00_u03b2_7455_, lean_object* v_adjustResult_7456_, lean_object* v_mr_7457_, lean_object* v_a_7458_){
_start:
{
lean_object* v_res_7459_; 
v_res_7459_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7454_, v_00_u03b2_7455_, v_adjustResult_7456_, v_mr_7457_, v_a_7458_);
lean_dec_ref(v_mr_7457_);
return v_res_7459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7460_, lean_object* v_00_u03b2_7461_, lean_object* v_adjustResult_7462_, lean_object* v_j_7463_, size_t v_sz_7464_, size_t v_i_7465_, lean_object* v_bs_7466_){
_start:
{
lean_object* v___x_7467_; 
v___x_7467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7462_, v_j_7463_, v_sz_7464_, v_i_7465_, v_bs_7466_);
return v___x_7467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7468_, lean_object* v_00_u03b2_7469_, lean_object* v_adjustResult_7470_, lean_object* v_j_7471_, lean_object* v_sz_7472_, lean_object* v_i_7473_, lean_object* v_bs_7474_){
_start:
{
size_t v_sz_boxed_7475_; size_t v_i_boxed_7476_; lean_object* v_res_7477_; 
v_sz_boxed_7475_ = lean_unbox_usize(v_sz_7472_);
lean_dec(v_sz_7472_);
v_i_boxed_7476_ = lean_unbox_usize(v_i_7473_);
lean_dec(v_i_7473_);
v_res_7477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7468_, v_00_u03b2_7469_, v_adjustResult_7470_, v_j_7471_, v_sz_boxed_7475_, v_i_boxed_7476_, v_bs_7474_);
return v_res_7477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7478_, lean_object* v_00_u03b2_7479_, lean_object* v_adjustResult_7480_, lean_object* v_j_7481_, lean_object* v_as_7482_, size_t v_i_7483_, size_t v_stop_7484_, lean_object* v_b_7485_){
_start:
{
lean_object* v___x_7486_; 
v___x_7486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7480_, v_j_7481_, v_as_7482_, v_i_7483_, v_stop_7484_, v_b_7485_);
return v___x_7486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7487_, lean_object* v_00_u03b2_7488_, lean_object* v_adjustResult_7489_, lean_object* v_j_7490_, lean_object* v_as_7491_, lean_object* v_i_7492_, lean_object* v_stop_7493_, lean_object* v_b_7494_){
_start:
{
size_t v_i_boxed_7495_; size_t v_stop_boxed_7496_; lean_object* v_res_7497_; 
v_i_boxed_7495_ = lean_unbox_usize(v_i_7492_);
lean_dec(v_i_7492_);
v_stop_boxed_7496_ = lean_unbox_usize(v_stop_7493_);
lean_dec(v_stop_7493_);
v_res_7497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7487_, v_00_u03b2_7488_, v_adjustResult_7489_, v_j_7490_, v_as_7491_, v_i_boxed_7495_, v_stop_boxed_7496_, v_b_7494_);
lean_dec_ref(v_as_7491_);
return v_res_7497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7498_, lean_object* v_n_7499_, lean_object* v_00_u03b1_7500_, lean_object* v_adjustResult_7501_, lean_object* v_aa_7502_, lean_object* v_n_7503_, lean_object* v_j_7504_, lean_object* v_a_7505_, lean_object* v_a_7506_){
_start:
{
lean_object* v___x_7507_; 
v___x_7507_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7499_, v_adjustResult_7501_, v_aa_7502_, v_n_7503_, v_j_7504_, v_a_7506_);
return v___x_7507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7508_, lean_object* v_n_7509_, lean_object* v_00_u03b1_7510_, lean_object* v_adjustResult_7511_, lean_object* v_aa_7512_, lean_object* v_n_7513_, lean_object* v_j_7514_, lean_object* v_a_7515_, lean_object* v_a_7516_){
_start:
{
lean_object* v_res_7517_; 
v_res_7517_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7508_, v_n_7509_, v_00_u03b1_7510_, v_adjustResult_7511_, v_aa_7512_, v_n_7513_, v_j_7514_, v_a_7515_, v_a_7516_);
lean_dec(v_j_7514_);
lean_dec(v_n_7513_);
lean_dec_ref(v_aa_7512_);
lean_dec(v_n_7509_);
return v_res_7517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7518_, lean_object* v_n_7519_, lean_object* v_00_u03b1_7520_, lean_object* v_aa_7521_, lean_object* v_adjustResult_7522_, lean_object* v_n_7523_, lean_object* v_j_7524_, lean_object* v_a_7525_, lean_object* v_a_7526_){
_start:
{
lean_object* v___x_7527_; 
v___x_7527_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7519_, v_aa_7521_, v_adjustResult_7522_, v_n_7523_, v_j_7524_, v_a_7526_);
return v___x_7527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7528_, lean_object* v_n_7529_, lean_object* v_00_u03b1_7530_, lean_object* v_aa_7531_, lean_object* v_adjustResult_7532_, lean_object* v_n_7533_, lean_object* v_j_7534_, lean_object* v_a_7535_, lean_object* v_a_7536_){
_start:
{
lean_object* v_res_7537_; 
v_res_7537_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7528_, v_n_7529_, v_00_u03b1_7530_, v_aa_7531_, v_adjustResult_7532_, v_n_7533_, v_j_7534_, v_a_7535_, v_a_7536_);
lean_dec(v_n_7533_);
lean_dec_ref(v_aa_7531_);
lean_dec(v_n_7529_);
return v_res_7537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7538_, lean_object* v_v_7539_){
_start:
{
lean_inc(v_v_7539_);
return v_v_7539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7540_, lean_object* v_v_7541_){
_start:
{
lean_object* v_res_7542_; 
v_res_7542_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7540_, v_v_7541_);
lean_dec(v_v_7541_);
lean_dec(v_x_7540_);
return v_res_7542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7544_, lean_object* v_addEntry_7545_, lean_object* v_droppedKeys_7546_, lean_object* v_constantsPerTask_7547_, lean_object* v_droppedEntriesRef_7548_, lean_object* v_ty_7549_, lean_object* v_a_7550_, lean_object* v_a_7551_, lean_object* v_a_7552_, lean_object* v_a_7553_){
_start:
{
lean_object* v___x_7555_; 
lean_inc(v_droppedEntriesRef_7548_);
lean_inc(v_droppedKeys_7546_);
lean_inc_ref(v_addEntry_7545_);
v___x_7555_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7545_, v_droppedKeys_7546_, v_droppedEntriesRef_7548_, v_a_7550_, v_a_7551_, v_a_7552_, v_a_7553_);
if (lean_obj_tag(v___x_7555_) == 0)
{
lean_object* v_a_7556_; lean_object* v___f_7557_; lean_object* v___x_7558_; 
v_a_7556_ = lean_ctor_get(v___x_7555_, 0);
lean_inc(v_a_7556_);
lean_dec_ref_known(v___x_7555_, 1);
v___f_7557_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7558_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7556_, v_ref_7544_, v_addEntry_7545_, v_droppedKeys_7546_, v_constantsPerTask_7547_, v_droppedEntriesRef_7548_, v___f_7557_, v_ty_7549_, v_a_7550_, v_a_7551_, v_a_7552_, v_a_7553_);
return v___x_7558_;
}
else
{
lean_object* v_a_7559_; lean_object* v___x_7561_; uint8_t v_isShared_7562_; uint8_t v_isSharedCheck_7566_; 
lean_dec_ref(v_ty_7549_);
lean_dec(v_droppedEntriesRef_7548_);
lean_dec(v_constantsPerTask_7547_);
lean_dec(v_droppedKeys_7546_);
lean_dec_ref(v_addEntry_7545_);
v_a_7559_ = lean_ctor_get(v___x_7555_, 0);
v_isSharedCheck_7566_ = !lean_is_exclusive(v___x_7555_);
if (v_isSharedCheck_7566_ == 0)
{
v___x_7561_ = v___x_7555_;
v_isShared_7562_ = v_isSharedCheck_7566_;
goto v_resetjp_7560_;
}
else
{
lean_inc(v_a_7559_);
lean_dec(v___x_7555_);
v___x_7561_ = lean_box(0);
v_isShared_7562_ = v_isSharedCheck_7566_;
goto v_resetjp_7560_;
}
v_resetjp_7560_:
{
lean_object* v___x_7564_; 
if (v_isShared_7562_ == 0)
{
v___x_7564_ = v___x_7561_;
goto v_reusejp_7563_;
}
else
{
lean_object* v_reuseFailAlloc_7565_; 
v_reuseFailAlloc_7565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7565_, 0, v_a_7559_);
v___x_7564_ = v_reuseFailAlloc_7565_;
goto v_reusejp_7563_;
}
v_reusejp_7563_:
{
return v___x_7564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7567_, lean_object* v_addEntry_7568_, lean_object* v_droppedKeys_7569_, lean_object* v_constantsPerTask_7570_, lean_object* v_droppedEntriesRef_7571_, lean_object* v_ty_7572_, lean_object* v_a_7573_, lean_object* v_a_7574_, lean_object* v_a_7575_, lean_object* v_a_7576_, lean_object* v_a_7577_){
_start:
{
lean_object* v_res_7578_; 
v_res_7578_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7567_, v_addEntry_7568_, v_droppedKeys_7569_, v_constantsPerTask_7570_, v_droppedEntriesRef_7571_, v_ty_7572_, v_a_7573_, v_a_7574_, v_a_7575_, v_a_7576_);
lean_dec(v_a_7576_);
lean_dec_ref(v_a_7575_);
lean_dec(v_a_7574_);
lean_dec_ref(v_a_7573_);
lean_dec(v_ref_7567_);
return v_res_7578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7579_, lean_object* v_ref_7580_, lean_object* v_addEntry_7581_, lean_object* v_droppedKeys_7582_, lean_object* v_constantsPerTask_7583_, lean_object* v_droppedEntriesRef_7584_, lean_object* v_ty_7585_, lean_object* v_a_7586_, lean_object* v_a_7587_, lean_object* v_a_7588_, lean_object* v_a_7589_){
_start:
{
lean_object* v___x_7591_; 
v___x_7591_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7580_, v_addEntry_7581_, v_droppedKeys_7582_, v_constantsPerTask_7583_, v_droppedEntriesRef_7584_, v_ty_7585_, v_a_7586_, v_a_7587_, v_a_7588_, v_a_7589_);
return v___x_7591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7592_, lean_object* v_ref_7593_, lean_object* v_addEntry_7594_, lean_object* v_droppedKeys_7595_, lean_object* v_constantsPerTask_7596_, lean_object* v_droppedEntriesRef_7597_, lean_object* v_ty_7598_, lean_object* v_a_7599_, lean_object* v_a_7600_, lean_object* v_a_7601_, lean_object* v_a_7602_, lean_object* v_a_7603_){
_start:
{
lean_object* v_res_7604_; 
v_res_7604_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7592_, v_ref_7593_, v_addEntry_7594_, v_droppedKeys_7595_, v_constantsPerTask_7596_, v_droppedEntriesRef_7597_, v_ty_7598_, v_a_7599_, v_a_7600_, v_a_7601_, v_a_7602_);
lean_dec(v_a_7602_);
lean_dec_ref(v_a_7601_);
lean_dec(v_a_7600_);
lean_dec_ref(v_a_7599_);
lean_dec(v_ref_7593_);
return v_res_7604_;
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
