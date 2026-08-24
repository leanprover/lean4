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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint8_t l_Lean_getDiag(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
LEAN_EXPORT uint64_t l_Lean_Meta_LazyDiscrTree_Key_hash(lean_object* v_x_312_){
_start:
{
switch(lean_obj_tag(v_x_312_))
{
case 0:
{
lean_object* v_a_313_; lean_object* v_a_314_; uint64_t v___x_315_; uint64_t v___y_317_; 
v_a_313_ = lean_ctor_get(v_x_312_, 0);
v_a_314_ = lean_ctor_get(v_x_312_, 1);
v___x_315_ = 5237ULL;
if (lean_obj_tag(v_a_313_) == 0)
{
uint64_t v___x_321_; 
v___x_321_ = 1723ULL;
v___y_317_ = v___x_321_;
goto v___jp_316_;
}
else
{
uint64_t v_hash_322_; 
v_hash_322_ = lean_ctor_get_uint64(v_a_313_, sizeof(void*)*2);
v___y_317_ = v_hash_322_;
goto v___jp_316_;
}
v___jp_316_:
{
uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; 
v___x_318_ = lean_uint64_of_nat(v_a_314_);
v___x_319_ = lean_uint64_mix_hash(v___y_317_, v___x_318_);
v___x_320_ = lean_uint64_mix_hash(v___x_315_, v___x_319_);
return v___x_320_;
}
}
case 1:
{
lean_object* v_a_323_; lean_object* v_a_324_; uint64_t v___x_325_; uint64_t v___x_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; 
v_a_323_ = lean_ctor_get(v_x_312_, 0);
v_a_324_ = lean_ctor_get(v_x_312_, 1);
v___x_325_ = 3541ULL;
v___x_326_ = l_Lean_instHashableFVarId_hash(v_a_323_);
v___x_327_ = lean_uint64_of_nat(v_a_324_);
v___x_328_ = lean_uint64_mix_hash(v___x_326_, v___x_327_);
v___x_329_ = lean_uint64_mix_hash(v___x_325_, v___x_328_);
return v___x_329_;
}
case 2:
{
lean_object* v_a_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; 
v_a_330_ = lean_ctor_get(v_x_312_, 0);
v___x_331_ = 1879ULL;
v___x_332_ = l_Lean_Literal_hash(v_a_330_);
v___x_333_ = lean_uint64_mix_hash(v___x_331_, v___x_332_);
return v___x_333_;
}
case 3:
{
uint64_t v___x_334_; 
v___x_334_ = 7883ULL;
return v___x_334_;
}
case 4:
{
uint64_t v___x_335_; 
v___x_335_ = 2411ULL;
return v___x_335_;
}
case 5:
{
uint64_t v___x_336_; 
v___x_336_ = 17ULL;
return v___x_336_;
}
default: 
{
lean_object* v_a_337_; lean_object* v_a_338_; lean_object* v_a_339_; uint64_t v___x_340_; uint64_t v___y_342_; 
v_a_337_ = lean_ctor_get(v_x_312_, 0);
v_a_338_ = lean_ctor_get(v_x_312_, 1);
v_a_339_ = lean_ctor_get(v_x_312_, 2);
v___x_340_ = lean_uint64_of_nat(v_a_339_);
if (lean_obj_tag(v_a_337_) == 0)
{
uint64_t v___x_346_; 
v___x_346_ = 1723ULL;
v___y_342_ = v___x_346_;
goto v___jp_341_;
}
else
{
uint64_t v_hash_347_; 
v_hash_347_ = lean_ctor_get_uint64(v_a_337_, sizeof(void*)*2);
v___y_342_ = v_hash_347_;
goto v___jp_341_;
}
v___jp_341_:
{
uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; 
v___x_343_ = lean_uint64_of_nat(v_a_338_);
v___x_344_ = lean_uint64_mix_hash(v___y_342_, v___x_343_);
v___x_345_ = lean_uint64_mix_hash(v___x_340_, v___x_344_);
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_hash___boxed(lean_object* v_x_348_){
_start:
{
uint64_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_x_348_);
lean_dec(v_x_348_);
v_r_350_ = lean_box_uint64(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_358_ = l_Lean_mkMVar(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar(void){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0, &l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(lean_object* v_a_360_, lean_object* v_i_361_, lean_object* v_infos_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_infos_362_);
v___x_369_ = lean_nat_dec_lt(v_i_361_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_isProof(v_a_360_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_370_;
}
else
{
lean_object* v_info_371_; uint8_t v_isInstance_372_; uint8_t v___y_374_; 
v_info_371_ = lean_array_fget_borrowed(v_infos_362_, v_i_361_);
v_isInstance_372_ = lean_ctor_get_uint8(v_info_371_, sizeof(void*)*1 + 4);
if (v_isInstance_372_ == 0)
{
uint8_t v___x_390_; 
v___x_390_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_371_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; 
v___x_391_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_371_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_isProof(v_a_360_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_392_;
}
else
{
v___y_374_ = v___x_391_;
goto v___jp_373_;
}
}
else
{
v___y_374_ = v___x_369_;
goto v___jp_373_;
}
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_a_360_);
v___x_393_ = lean_box(v___x_369_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
v___jp_373_:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_isType(v_a_360_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_389_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_389_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_389_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint8_t v___x_380_; 
v___x_380_ = lean_unbox(v_a_376_);
lean_dec(v_a_376_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_box(v___y_374_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_381_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_box(v_isInstance_372_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_385_);
v___x_387_ = v___x_378_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg___boxed(lean_object* v_a_395_, lean_object* v_i_396_, lean_object* v_infos_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_a_395_, v_i_396_, v_infos_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec_ref(v_infos_397_);
lean_dec(v_i_396_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(lean_object* v_infos_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
if (lean_obj_tag(v_x_406_) == 5)
{
lean_object* v_fn_413_; lean_object* v_arg_414_; lean_object* v___x_415_; 
v_fn_413_ = lean_ctor_get(v_x_406_, 0);
lean_inc_ref(v_fn_413_);
v_arg_414_ = lean_ctor_get(v_x_406_, 1);
lean_inc_ref_n(v_arg_414_, 2);
lean_dec_ref_known(v_x_406_, 2);
v___x_415_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_arg_414_, v_x_405_, v_infos_404_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; uint8_t v___x_417_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 1);
v___x_417_ = lean_unbox(v_a_416_);
lean_dec(v_a_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_sub(v_x_405_, v___x_418_);
lean_dec(v_x_405_);
v___x_420_ = lean_array_push(v_x_407_, v_arg_414_);
v_x_405_ = v___x_419_;
v_x_406_ = v_fn_413_;
v_x_407_ = v___x_420_;
goto _start;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v_arg_414_);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_sub(v_x_405_, v___x_422_);
lean_dec(v_x_405_);
v___x_424_ = l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar;
v___x_425_ = lean_array_push(v_x_407_, v___x_424_);
v_x_405_ = v___x_423_;
v_x_406_ = v_fn_413_;
v_x_407_ = v___x_425_;
goto _start;
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v_arg_414_);
lean_dec_ref(v_fn_413_);
lean_dec_ref(v_x_407_);
lean_dec(v_x_405_);
v_a_427_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_415_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_415_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v___x_435_; 
lean_dec_ref(v_x_406_);
lean_dec(v_x_405_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v_x_407_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux___boxed(lean_object* v_infos_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_infos_436_, v_x_437_, v_x_438_, v_x_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec_ref(v_infos_436_);
return v_res_445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(lean_object* v_e_460_){
_start:
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = l_Lean_Expr_isRawNatLit(v_e_460_);
v___x_462_ = 1;
if (v___x_461_ == 0)
{
lean_object* v_f_463_; uint8_t v___x_464_; 
v_f_463_ = l_Lean_Expr_getAppFn(v_e_460_);
v___x_464_ = l_Lean_Expr_isConst(v_f_463_);
if (v___x_464_ == 0)
{
lean_dec_ref(v_f_463_);
lean_dec_ref(v_e_460_);
return v___x_461_;
}
else
{
if (v___x_461_ == 0)
{
lean_object* v_fName_465_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_fName_465_ = l_Lean_Expr_constName_x21(v_f_463_);
lean_dec_ref(v_f_463_);
v___x_483_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_484_ = lean_name_eq(v_fName_465_, v___x_483_);
if (v___x_484_ == 0)
{
goto v___jp_472_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = l_Lean_Expr_getAppNumArgs(v_e_460_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_dec_eq(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
if (v___x_487_ == 0)
{
goto v___jp_472_;
}
else
{
lean_object* v___x_488_; 
lean_dec(v_fName_465_);
v___x_488_ = l_Lean_Expr_appArg_x21(v_e_460_);
lean_dec_ref(v_e_460_);
v_e_460_ = v___x_488_;
goto _start;
}
}
v___jp_466_:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_468_ = lean_name_eq(v_fName_465_, v___x_467_);
lean_dec(v_fName_465_);
if (v___x_468_ == 0)
{
lean_dec_ref(v_e_460_);
return v___x_461_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = l_Lean_Expr_getAppNumArgs(v_e_460_);
lean_dec_ref(v_e_460_);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_nat_dec_eq(v___x_469_, v___x_470_);
lean_dec(v___x_469_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
return v___x_462_;
}
}
}
v___jp_472_:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_474_ = lean_name_eq(v_fName_465_, v___x_473_);
if (v___x_474_ == 0)
{
goto v___jp_466_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_475_ = l_Lean_Expr_getAppNumArgs(v_e_460_);
v___x_476_ = lean_unsigned_to_nat(3u);
v___x_477_ = lean_nat_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec(v___x_475_);
goto v___jp_466_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_fName_465_);
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_sub(v___x_475_, v___x_478_);
lean_dec(v___x_475_);
v___x_480_ = lean_nat_sub(v___x_479_, v___x_478_);
lean_dec(v___x_479_);
v___x_481_ = l_Lean_Expr_getRevArg_x21(v_e_460_, v___x_480_);
lean_dec_ref(v_e_460_);
v_e_460_ = v___x_481_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v_f_463_);
lean_dec_ref(v_e_460_);
return v___x_461_;
}
}
}
else
{
lean_dec_ref(v_e_460_);
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___boxed(lean_object* v_e_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(lean_object* v_e_495_){
_start:
{
uint8_t v___y_497_; lean_object* v_f_500_; 
v_f_500_ = l_Lean_Expr_getAppFn(v_e_495_);
switch(lean_obj_tag(v_f_500_))
{
case 9:
{
lean_object* v_a_501_; 
lean_dec_ref(v_e_495_);
v_a_501_ = lean_ctor_get(v_f_500_, 0);
lean_inc_ref(v_a_501_);
lean_dec_ref_known(v_f_500_, 1);
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v_val_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_val_502_ = lean_ctor_get(v_a_501_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_501_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v_a_501_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_val_502_);
lean_dec(v_a_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 1);
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_val_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_object* v___x_510_; 
lean_dec_ref(v_a_501_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
}
case 4:
{
lean_object* v_declName_511_; uint8_t v___y_513_; uint8_t v___y_526_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_declName_511_ = lean_ctor_get(v_f_500_, 0);
lean_inc(v_declName_511_);
lean_dec_ref_known(v_f_500_, 2);
v___x_544_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_545_ = lean_name_eq(v_declName_511_, v___x_544_);
if (v___x_545_ == 0)
{
v___y_526_ = v___x_545_;
goto v___jp_525_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = l_Lean_Expr_getAppNumArgs(v_e_495_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_dec_eq(v___x_546_, v___x_547_);
lean_dec(v___x_546_);
v___y_526_ = v___x_548_;
goto v___jp_525_;
}
v___jp_512_:
{
if (v___y_513_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_515_ = lean_name_eq(v_declName_511_, v___x_514_);
lean_dec(v_declName_511_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_e_495_);
v___y_497_ = v___x_515_;
goto v___jp_496_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_516_ = l_Lean_Expr_getAppNumArgs(v_e_495_);
lean_dec_ref(v_e_495_);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_nat_dec_eq(v___x_516_, v___x_517_);
lean_dec(v___x_516_);
v___y_497_ = v___x_518_;
goto v___jp_496_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_declName_511_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = l_Lean_Expr_getAppNumArgs(v_e_495_);
v___x_521_ = lean_nat_sub(v___x_520_, v___x_519_);
lean_dec(v___x_520_);
v___x_522_ = lean_nat_sub(v___x_521_, v___x_519_);
lean_dec(v___x_521_);
v___x_523_ = l_Lean_Expr_getRevArg_x21(v_e_495_, v___x_522_);
lean_dec_ref(v_e_495_);
v_e_495_ = v___x_523_;
goto _start;
}
}
v___jp_525_:
{
if (v___y_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_528_ = lean_name_eq(v_declName_511_, v___x_527_);
if (v___x_528_ == 0)
{
v___y_513_ = v___x_528_;
goto v___jp_512_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_529_ = l_Lean_Expr_getAppNumArgs(v_e_495_);
v___x_530_ = lean_unsigned_to_nat(3u);
v___x_531_ = lean_nat_dec_eq(v___x_529_, v___x_530_);
lean_dec(v___x_529_);
v___y_513_ = v___x_531_;
goto v___jp_512_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_declName_511_);
v___x_532_ = l_Lean_Expr_appArg_x21(v_e_495_);
lean_dec_ref(v_e_495_);
v___x_533_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v___x_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
return v___x_533_;
}
else
{
lean_object* v_val_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v_val_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_543_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_val_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_val_534_, v___x_538_);
lean_dec(v_val_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_539_);
v___x_541_ = v___x_536_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_549_; 
lean_dec_ref(v_f_500_);
lean_dec_ref(v_e_495_);
v___x_549_ = lean_box(0);
return v___x_549_;
}
}
v___jp_496_:
{
if (v___y_497_ == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_box(0);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0));
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object* v_e_550_){
_start:
{
uint8_t v___x_551_; 
lean_inc_ref(v_e_550_);
v___x_551_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec_ref(v_e_550_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v_e_550_);
if (lean_obj_tag(v___x_553_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_val_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_562_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_val_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v___x_553_);
v___x_563_ = lean_box(0);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object* v_e_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_572_; 
lean_inc(v_a_570_);
lean_inc_ref(v_a_569_);
lean_inc(v_a_568_);
lean_inc_ref(v_a_567_);
v___x_572_ = lean_whnf(v_e_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_583_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_583_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_583_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_583_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; uint8_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_577_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0));
v___x_578_ = l_Lean_Expr_isConstOf(v_a_573_, v___x_577_);
lean_dec(v_a_573_);
v___x_579_ = lean_box(v___x_578_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_579_);
v___x_581_ = v___x_575_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_584_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_572_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_572_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object* v_e_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v_e_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object* v_fName_612_, lean_object* v_e_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
uint8_t v___y_620_; uint8_t v___y_650_; uint8_t v___y_675_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6));
v___x_686_ = lean_name_eq(v_fName_612_, v___x_685_);
if (v___x_686_ == 0)
{
v___y_675_ = v___x_686_;
goto v___jp_674_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = l_Lean_Expr_getAppNumArgs(v_e_613_);
v___x_688_ = lean_unsigned_to_nat(2u);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
lean_dec(v___x_687_);
v___y_675_ = v___x_689_;
goto v___jp_674_;
}
v___jp_619_:
{
if (v___y_620_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_622_ = lean_name_eq(v_fName_612_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_box(v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_625_ = l_Lean_Expr_getAppNumArgs(v_e_613_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_dec_eq(v___x_625_, v___x_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = l_Lean_Expr_getAppNumArgs(v_e_613_);
v___x_632_ = lean_nat_sub(v___x_631_, v___x_630_);
lean_dec(v___x_631_);
v___x_633_ = lean_nat_sub(v___x_632_, v___x_630_);
lean_dec(v___x_632_);
v___x_634_ = l_Lean_Expr_getRevArg_x21(v_e_613_, v___x_633_);
v___x_635_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_634_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; uint8_t v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
v___x_637_ = lean_unbox(v_a_636_);
lean_dec(v_a_636_);
if (v___x_637_ == 0)
{
return v___x_635_;
}
else
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_647_; 
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_635_, 0);
lean_dec(v_unused_648_);
v___x_639_ = v___x_635_;
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
else
{
lean_dec(v___x_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_641_ = l_Lean_Expr_appArg_x21(v_e_613_);
v___x_642_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_641_);
v___x_643_ = lean_box(v___x_642_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_643_);
v___x_645_ = v___x_639_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
return v___x_635_;
}
}
}
v___jp_649_:
{
if (v___y_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2));
v___x_652_ = lean_name_eq(v_fName_612_, v___x_651_);
if (v___x_652_ == 0)
{
v___y_620_ = v___x_652_;
goto v___jp_619_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = l_Lean_Expr_getAppNumArgs(v_e_613_);
v___x_654_ = lean_unsigned_to_nat(6u);
v___x_655_ = lean_nat_dec_eq(v___x_653_, v___x_654_);
lean_dec(v___x_653_);
v___y_620_ = v___x_655_;
goto v___jp_619_;
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_656_ = l_Lean_Expr_getAppNumArgs(v_e_613_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_sub(v___x_656_, v___x_657_);
lean_dec(v___x_656_);
v___x_659_ = l_Lean_Expr_getRevArg_x21(v_e_613_, v___x_658_);
v___x_660_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_659_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; uint8_t v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
v___x_662_ = lean_unbox(v_a_661_);
lean_dec(v_a_661_);
if (v___x_662_ == 0)
{
return v___x_660_;
}
else
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_672_; 
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_660_, 0);
lean_dec(v_unused_673_);
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
else
{
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_666_ = l_Lean_Expr_appArg_x21(v_e_613_);
v___x_667_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_666_);
v___x_668_ = lean_box(v___x_667_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_668_);
v___x_670_ = v___x_664_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
return v___x_660_;
}
}
}
v___jp_674_:
{
if (v___y_675_ == 0)
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5));
v___x_677_ = lean_name_eq(v_fName_612_, v___x_676_);
if (v___x_677_ == 0)
{
v___y_650_ = v___x_677_;
goto v___jp_649_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_678_ = l_Lean_Expr_getAppNumArgs(v_e_613_);
v___x_679_ = lean_unsigned_to_nat(4u);
v___x_680_ = lean_nat_dec_eq(v___x_678_, v___x_679_);
lean_dec(v___x_678_);
v___y_650_ = v___x_680_;
goto v___jp_649_;
}
}
else
{
lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = l_Lean_Expr_appArg_x21(v_e_613_);
v___x_682_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_681_);
v___x_683_ = lean_box(v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object* v_fName_690_, lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_690_, v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec_ref(v_e_691_);
lean_dec(v_fName_690_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object* v_fName_698_, lean_object* v_e_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_698_, v_e_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object* v_fName_706_, lean_object* v_e_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(v_fName_706_, v_e_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec_ref(v_e_707_);
lean_dec(v_fName_706_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object* v_e_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_Expr_hasLooseBVars(v_e_716_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_e_716_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
else
{
uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = 0;
v___x_724_ = l_Lean_Expr_isHeadBetaTarget(v_e_716_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v_e_716_);
v___x_725_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0));
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_Expr_headBeta(v_e_716_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object* v_e_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(v_e_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object* v_e_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v_e_735_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object* v_e_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(v_e_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_745_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_box(0);
v___x_747_ = l_Lean_interruptExceptionId;
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_753_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_Lean_maxRecDepthErrorMessage;
v___x_760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_764_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_765_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_766_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_ref_766_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___y_780_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; uint8_t v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v_fileName_810_; lean_object* v_fileMap_811_; lean_object* v_options_812_; lean_object* v_currRecDepth_813_; lean_object* v_maxRecDepth_814_; lean_object* v_ref_815_; lean_object* v_currNamespace_816_; lean_object* v_openDecls_817_; lean_object* v_initHeartbeats_818_; lean_object* v_maxHeartbeats_819_; lean_object* v_quotContext_820_; lean_object* v_currMacroScope_821_; uint8_t v_diag_822_; lean_object* v_cancelTk_x3f_823_; uint8_t v_suppressElabErrors_824_; lean_object* v_inheritedTraceOptions_825_; 
v_fileName_810_ = lean_ctor_get(v___y_776_, 0);
v_fileMap_811_ = lean_ctor_get(v___y_776_, 1);
v_options_812_ = lean_ctor_get(v___y_776_, 2);
v_currRecDepth_813_ = lean_ctor_get(v___y_776_, 3);
v_maxRecDepth_814_ = lean_ctor_get(v___y_776_, 4);
v_ref_815_ = lean_ctor_get(v___y_776_, 5);
v_currNamespace_816_ = lean_ctor_get(v___y_776_, 6);
v_openDecls_817_ = lean_ctor_get(v___y_776_, 7);
v_initHeartbeats_818_ = lean_ctor_get(v___y_776_, 8);
v_maxHeartbeats_819_ = lean_ctor_get(v___y_776_, 9);
v_quotContext_820_ = lean_ctor_get(v___y_776_, 10);
v_currMacroScope_821_ = lean_ctor_get(v___y_776_, 11);
v_diag_822_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*14);
v_cancelTk_x3f_823_ = lean_ctor_get(v___y_776_, 12);
v_suppressElabErrors_824_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_825_ = lean_ctor_get(v___y_776_, 13);
if (lean_obj_tag(v_cancelTk_x3f_823_) == 1)
{
lean_object* v_val_831_; uint8_t v___x_832_; 
v_val_831_ = lean_ctor_get(v_cancelTk_x3f_823_, 0);
v___x_832_ = l_IO_CancelToken_isSet(v_val_831_);
if (v___x_832_ == 0)
{
goto v___jp_826_;
}
else
{
lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v_x_774_);
v___x_833_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
goto v___jp_826_;
}
v___jp_779_:
{
if (lean_obj_tag(v___y_780_) == 0)
{
return v___y_780_;
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v___y_780_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___y_780_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___y_780_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___y_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
v___jp_789_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v___y_792_, v___x_806_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_805_);
lean_inc(v___y_799_);
lean_inc(v___y_793_);
lean_inc(v___y_791_);
lean_inc(v___y_804_);
lean_inc(v___y_796_);
lean_inc(v___y_801_);
lean_inc(v___y_795_);
lean_inc_ref(v___y_798_);
lean_inc_ref(v___y_794_);
lean_inc_ref(v___y_803_);
v___x_808_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_808_, 0, v___y_803_);
lean_ctor_set(v___x_808_, 1, v___y_794_);
lean_ctor_set(v___x_808_, 2, v___y_798_);
lean_ctor_set(v___x_808_, 3, v___x_807_);
lean_ctor_set(v___x_808_, 4, v___y_795_);
lean_ctor_set(v___x_808_, 5, v___y_790_);
lean_ctor_set(v___x_808_, 6, v___y_801_);
lean_ctor_set(v___x_808_, 7, v___y_796_);
lean_ctor_set(v___x_808_, 8, v___y_804_);
lean_ctor_set(v___x_808_, 9, v___y_791_);
lean_ctor_set(v___x_808_, 10, v___y_793_);
lean_ctor_set(v___x_808_, 11, v___y_799_);
lean_ctor_set(v___x_808_, 12, v___y_805_);
lean_ctor_set(v___x_808_, 13, v___y_802_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*14, v___y_800_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*14 + 1, v___y_797_);
lean_inc(v___y_777_);
lean_inc(v___y_775_);
v___x_809_ = lean_apply_4(v_x_774_, v___y_775_, v___x_808_, v___y_777_, lean_box(0));
v___y_780_ = v___x_809_;
goto v___jp_779_;
}
v___jp_826_:
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_nat_dec_eq(v_maxRecDepth_814_, v___x_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
v___x_829_ = lean_nat_dec_eq(v_currRecDepth_813_, v_maxRecDepth_814_);
if (v___x_829_ == 0)
{
lean_inc(v_ref_815_);
v___y_790_ = v_ref_815_;
v___y_791_ = v_maxHeartbeats_819_;
v___y_792_ = v_currRecDepth_813_;
v___y_793_ = v_quotContext_820_;
v___y_794_ = v_fileMap_811_;
v___y_795_ = v_maxRecDepth_814_;
v___y_796_ = v_openDecls_817_;
v___y_797_ = v_suppressElabErrors_824_;
v___y_798_ = v_options_812_;
v___y_799_ = v_currMacroScope_821_;
v___y_800_ = v_diag_822_;
v___y_801_ = v_currNamespace_816_;
v___y_802_ = v_inheritedTraceOptions_825_;
v___y_803_ = v_fileName_810_;
v___y_804_ = v_initHeartbeats_818_;
v___y_805_ = v_cancelTk_x3f_823_;
goto v___jp_789_;
}
else
{
lean_object* v___x_830_; 
lean_dec_ref(v_x_774_);
lean_inc(v_ref_815_);
v___x_830_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_815_);
v___y_780_ = v___x_830_;
goto v___jp_779_;
}
}
else
{
lean_inc(v_ref_815_);
v___y_790_ = v_ref_815_;
v___y_791_ = v_maxHeartbeats_819_;
v___y_792_ = v_currRecDepth_813_;
v___y_793_ = v_quotContext_820_;
v___y_794_ = v_fileMap_811_;
v___y_795_ = v_maxRecDepth_814_;
v___y_796_ = v_openDecls_817_;
v___y_797_ = v_suppressElabErrors_824_;
v___y_798_ = v_options_812_;
v___y_799_ = v_currMacroScope_821_;
v___y_800_ = v_diag_822_;
v___y_801_ = v_currNamespace_816_;
v___y_802_ = v_inheritedTraceOptions_825_;
v___y_803_ = v_fileName_810_;
v___y_804_ = v_initHeartbeats_818_;
v___y_805_ = v_cancelTk_x3f_823_;
goto v___jp_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v_key_851_; lean_object* v_value_852_; lean_object* v_tail_853_; uint8_t v___x_854_; 
v_key_851_ = lean_ctor_get(v_x_849_, 0);
v_value_852_ = lean_ctor_get(v_x_849_, 1);
v_tail_853_ = lean_ctor_get(v_x_849_, 2);
v___x_854_ = l_Lean_ExprStructEq_beq(v_key_851_, v_a_848_);
if (v___x_854_ == 0)
{
v_x_849_ = v_tail_853_;
goto _start;
}
else
{
lean_object* v___x_856_; 
lean_inc(v_value_852_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v_value_852_);
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_a_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_buckets_862_; lean_object* v___x_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v_fold_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_buckets_862_ = lean_ctor_get(v_m_860_, 1);
v___x_863_ = lean_array_get_size(v_buckets_862_);
v___x_864_ = l_Lean_ExprStructEq_hash(v_a_861_);
v___x_865_ = 32ULL;
v___x_866_ = lean_uint64_shift_right(v___x_864_, v___x_865_);
v_fold_867_ = lean_uint64_xor(v___x_864_, v___x_866_);
v___x_868_ = 16ULL;
v___x_869_ = lean_uint64_shift_right(v_fold_867_, v___x_868_);
v___x_870_ = lean_uint64_xor(v_fold_867_, v___x_869_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
v___x_872_ = lean_usize_of_nat(v___x_863_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_sub(v___x_872_, v___x_873_);
v___x_875_ = lean_usize_land(v___x_871_, v___x_874_);
v___x_876_ = lean_array_uget_borrowed(v_buckets_862_, v___x_875_);
v___x_877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_861_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_878_, v_a_879_);
lean_dec_ref(v_a_879_);
lean_dec_ref(v_m_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_881_, lean_object* v_b_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
lean_dec(v_b_882_);
lean_dec_ref(v_a_881_);
return v_x_883_;
}
else
{
lean_object* v_key_884_; lean_object* v_value_885_; lean_object* v_tail_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_898_; 
v_key_884_ = lean_ctor_get(v_x_883_, 0);
v_value_885_ = lean_ctor_get(v_x_883_, 1);
v_tail_886_ = lean_ctor_get(v_x_883_, 2);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_898_ == 0)
{
v___x_888_ = v_x_883_;
v_isShared_889_ = v_isSharedCheck_898_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_tail_886_);
lean_inc(v_value_885_);
lean_inc(v_key_884_);
lean_dec(v_x_883_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_898_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
uint8_t v___x_890_; 
v___x_890_ = l_Lean_ExprStructEq_beq(v_key_884_, v_a_881_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_881_, v_b_882_, v_tail_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 2, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_key_884_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_value_885_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v___x_896_; 
lean_dec(v_value_885_);
lean_dec(v_key_884_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_b_882_);
lean_ctor_set(v___x_888_, 0, v_a_881_);
v___x_896_ = v___x_888_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_881_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_b_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_tail_886_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
if (lean_obj_tag(v_x_900_) == 0)
{
return v_x_899_;
}
else
{
lean_object* v_key_901_; lean_object* v_value_902_; lean_object* v_tail_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_926_; 
v_key_901_ = lean_ctor_get(v_x_900_, 0);
v_value_902_ = lean_ctor_get(v_x_900_, 1);
v_tail_903_ = lean_ctor_get(v_x_900_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_x_900_);
if (v_isSharedCheck_926_ == 0)
{
v___x_905_ = v_x_900_;
v_isShared_906_ = v_isSharedCheck_926_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_tail_903_);
lean_inc(v_value_902_);
lean_inc(v_key_901_);
lean_dec(v_x_900_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_926_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v_fold_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_907_ = lean_array_get_size(v_x_899_);
v___x_908_ = l_Lean_ExprStructEq_hash(v_key_901_);
v___x_909_ = 32ULL;
v___x_910_ = lean_uint64_shift_right(v___x_908_, v___x_909_);
v_fold_911_ = lean_uint64_xor(v___x_908_, v___x_910_);
v___x_912_ = 16ULL;
v___x_913_ = lean_uint64_shift_right(v_fold_911_, v___x_912_);
v___x_914_ = lean_uint64_xor(v_fold_911_, v___x_913_);
v___x_915_ = lean_uint64_to_usize(v___x_914_);
v___x_916_ = lean_usize_of_nat(v___x_907_);
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_sub(v___x_916_, v___x_917_);
v___x_919_ = lean_usize_land(v___x_915_, v___x_918_);
v___x_920_ = lean_array_uget_borrowed(v_x_899_, v___x_919_);
lean_inc(v___x_920_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 2, v___x_920_);
v___x_922_ = v___x_905_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_key_901_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_value_902_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v___x_920_);
v___x_922_ = v_reuseFailAlloc_925_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_array_uset(v_x_899_, v___x_919_, v___x_922_);
v_x_899_ = v___x_923_;
v_x_900_ = v_tail_903_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_927_, lean_object* v_source_928_, lean_object* v_target_929_){
_start:
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = lean_array_get_size(v_source_928_);
v___x_931_ = lean_nat_dec_lt(v_i_927_, v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v_source_928_);
lean_dec(v_i_927_);
return v_target_929_;
}
else
{
lean_object* v_es_932_; lean_object* v___x_933_; lean_object* v_source_934_; lean_object* v_target_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_es_932_ = lean_array_fget(v_source_928_, v_i_927_);
v___x_933_ = lean_box(0);
v_source_934_ = lean_array_fset(v_source_928_, v_i_927_, v___x_933_);
v_target_935_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_929_, v_es_932_);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_i_927_, v___x_936_);
lean_dec(v_i_927_);
v_i_927_ = v___x_937_;
v_source_928_ = v_source_934_;
v_target_929_ = v_target_935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_nbuckets_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_940_ = lean_array_get_size(v_data_939_);
v___x_941_ = lean_unsigned_to_nat(2u);
v_nbuckets_942_ = lean_nat_mul(v___x_940_, v___x_941_);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_box(0);
v___x_945_ = lean_mk_array(v_nbuckets_942_, v___x_944_);
v___x_946_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_943_, v_data_939_, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_947_, lean_object* v_x_948_){
_start:
{
if (lean_obj_tag(v_x_948_) == 0)
{
uint8_t v___x_949_; 
v___x_949_ = 0;
return v___x_949_;
}
else
{
lean_object* v_key_950_; lean_object* v_tail_951_; uint8_t v___x_952_; 
v_key_950_ = lean_ctor_get(v_x_948_, 0);
v_tail_951_ = lean_ctor_get(v_x_948_, 2);
v___x_952_ = l_Lean_ExprStructEq_beq(v_key_950_, v_a_947_);
if (v___x_952_ == 0)
{
v_x_948_ = v_tail_951_;
goto _start;
}
else
{
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_954_, lean_object* v_x_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_954_, v_x_955_);
lean_dec(v_x_955_);
lean_dec_ref(v_a_954_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_958_, lean_object* v_a_959_, lean_object* v_b_960_){
_start:
{
lean_object* v_size_961_; lean_object* v_buckets_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1005_; 
v_size_961_ = lean_ctor_get(v_m_958_, 0);
v_buckets_962_ = lean_ctor_get(v_m_958_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_m_958_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_964_ = v_m_958_;
v_isShared_965_ = v_isSharedCheck_1005_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_buckets_962_);
lean_inc(v_size_961_);
lean_dec(v_m_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1005_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v_fold_970_; uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; size_t v___x_978_; lean_object* v_bkt_979_; uint8_t v___x_980_; 
v___x_966_ = lean_array_get_size(v_buckets_962_);
v___x_967_ = l_Lean_ExprStructEq_hash(v_a_959_);
v___x_968_ = 32ULL;
v___x_969_ = lean_uint64_shift_right(v___x_967_, v___x_968_);
v_fold_970_ = lean_uint64_xor(v___x_967_, v___x_969_);
v___x_971_ = 16ULL;
v___x_972_ = lean_uint64_shift_right(v_fold_970_, v___x_971_);
v___x_973_ = lean_uint64_xor(v_fold_970_, v___x_972_);
v___x_974_ = lean_uint64_to_usize(v___x_973_);
v___x_975_ = lean_usize_of_nat(v___x_966_);
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_sub(v___x_975_, v___x_976_);
v___x_978_ = lean_usize_land(v___x_974_, v___x_977_);
v_bkt_979_ = lean_array_uget_borrowed(v_buckets_962_, v___x_978_);
v___x_980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_959_, v_bkt_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v_size_x27_982_; lean_object* v___x_983_; lean_object* v_buckets_x27_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_981_ = lean_unsigned_to_nat(1u);
v_size_x27_982_ = lean_nat_add(v_size_961_, v___x_981_);
lean_dec(v_size_961_);
lean_inc(v_bkt_979_);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v_a_959_);
lean_ctor_set(v___x_983_, 1, v_b_960_);
lean_ctor_set(v___x_983_, 2, v_bkt_979_);
v_buckets_x27_984_ = lean_array_uset(v_buckets_962_, v___x_978_, v___x_983_);
v___x_985_ = lean_unsigned_to_nat(4u);
v___x_986_ = lean_nat_mul(v_size_x27_982_, v___x_985_);
v___x_987_ = lean_unsigned_to_nat(3u);
v___x_988_ = lean_nat_div(v___x_986_, v___x_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_array_get_size(v_buckets_x27_984_);
v___x_990_ = lean_nat_dec_le(v___x_988_, v___x_989_);
lean_dec(v___x_988_);
if (v___x_990_ == 0)
{
lean_object* v_val_991_; lean_object* v___x_993_; 
v_val_991_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_984_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_val_991_);
lean_ctor_set(v___x_964_, 0, v_size_x27_982_);
v___x_993_ = v___x_964_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_size_x27_982_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_val_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v___x_996_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_buckets_x27_984_);
lean_ctor_set(v___x_964_, 0, v_size_x27_982_);
v___x_996_ = v___x_964_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_size_x27_982_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_buckets_x27_984_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v___x_998_; lean_object* v_buckets_x27_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_inc(v_bkt_979_);
v___x_998_ = lean_box(0);
v_buckets_x27_999_ = lean_array_uset(v_buckets_962_, v___x_978_, v___x_998_);
v___x_1000_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_959_, v_b_960_, v_bkt_979_);
v___x_1001_ = lean_array_uset(v_buckets_x27_999_, v___x_978_, v___x_1000_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_1001_);
v___x_1003_ = v___x_964_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_size_961_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_1006_, lean_object* v_e_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1010_ = lean_st_ref_take(v_a_1006_);
v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_1010_, v_e_1007_, v_a_1008_);
v___x_1012_ = lean_st_ref_put(v_a_1006_, v___x_1011_);
v___x_1013_ = lean_box(0);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1014_, lean_object* v_e_1015_, lean_object* v_a_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_1014_, v_e_1015_, v_a_1016_);
lean_dec(v_a_1014_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_apply_1(v_x_1020_, lean_box(0));
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_x_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1026_, v_x_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1033_; lean_object* v_dummy_1034_; 
v___x_1033_ = lean_box(0);
v_dummy_1034_ = l_Lean_Expr_sort___override(v___x_1033_);
return v_dummy_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1035_, lean_object* v_post_1036_, size_t v_sz_1037_, size_t v_i_1038_, lean_object* v_bs_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_usize_dec_lt(v_i_1038_, v_sz_1037_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_dec_ref(v_post_1036_);
lean_dec_ref(v_pre_1035_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_bs_1039_);
return v___x_1045_;
}
else
{
lean_object* v_v_1046_; lean_object* v___x_1047_; 
v_v_1046_ = lean_array_uget_borrowed(v_bs_1039_, v_i_1038_);
lean_inc(v_v_1046_);
lean_inc_ref(v_post_1036_);
lean_inc_ref(v_pre_1035_);
v___x_1047_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1035_, v_post_1036_, v_v_1046_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; lean_object* v_bs_x27_1050_; size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = lean_unsigned_to_nat(0u);
v_bs_x27_1050_ = lean_array_uset(v_bs_1039_, v_i_1038_, v___x_1049_);
v___x_1051_ = ((size_t)1ULL);
v___x_1052_ = lean_usize_add(v_i_1038_, v___x_1051_);
v___x_1053_ = lean_array_uset(v_bs_x27_1050_, v_i_1038_, v_a_1048_);
v_i_1038_ = v___x_1052_;
v_bs_1039_ = v___x_1053_;
goto _start;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_bs_1039_);
lean_dec_ref(v_post_1036_);
lean_dec_ref(v_pre_1035_);
v_a_1055_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1047_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1047_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1063_, lean_object* v_post_1064_, lean_object* v_x_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 5)
{
lean_object* v_fn_1072_; lean_object* v_arg_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_fn_1072_ = lean_ctor_get(v_x_1065_, 0);
lean_inc_ref(v_fn_1072_);
v_arg_1073_ = lean_ctor_get(v_x_1065_, 1);
lean_inc_ref(v_arg_1073_);
lean_dec_ref_known(v_x_1065_, 2);
v___x_1074_ = lean_array_set(v_x_1066_, v_x_1067_, v_arg_1073_);
v___x_1075_ = lean_unsigned_to_nat(1u);
v___x_1076_ = lean_nat_sub(v_x_1067_, v___x_1075_);
lean_dec(v_x_1067_);
v_x_1065_ = v_fn_1072_;
v_x_1066_ = v___x_1074_;
v_x_1067_ = v___x_1076_;
goto _start;
}
else
{
lean_object* v___x_1078_; 
lean_dec(v_x_1067_);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1063_);
v___x_1078_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1063_, v_post_1064_, v_x_1065_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; size_t v_sz_1080_; size_t v___x_1081_; lean_object* v___x_1082_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_sz_1080_ = lean_array_size(v_x_1066_);
v___x_1081_ = ((size_t)0ULL);
lean_inc_ref(v_post_1064_);
lean_inc_ref(v_pre_1063_);
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1063_, v_post_1064_, v_sz_1080_, v___x_1081_, v_x_1066_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1084_ = l_Lean_mkAppN(v_a_1079_, v_a_1083_);
lean_dec(v_a_1083_);
v___x_1085_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1063_, v_post_1064_, v___x_1084_, v___y_1068_, v___y_1069_, v___y_1070_);
return v___x_1085_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_a_1079_);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1063_);
v_a_1086_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1082_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1082_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_dec_ref(v_x_1066_);
lean_dec_ref(v_post_1064_);
lean_dec_ref(v_pre_1063_);
return v___x_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1094_, lean_object* v_pre_1095_, lean_object* v_e_1096_, lean_object* v_post_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_Core_checkSystem(v___x_1094_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1102_, 1);
lean_inc_ref(v_pre_1095_);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1099_);
lean_inc_ref(v_e_1096_);
v___x_1103_ = lean_apply_4(v_pre_1095_, v_e_1096_, v___y_1099_, v___y_1100_, lean_box(0));
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1219_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1219_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1219_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___y_1109_; 
switch(lean_obj_tag(v_a_1104_))
{
case 0:
{
lean_object* v_e_1209_; lean_object* v___x_1211_; 
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_e_1096_);
lean_dec_ref(v_pre_1095_);
v_e_1209_ = lean_ctor_get(v_a_1104_, 0);
lean_inc_ref(v_e_1209_);
lean_dec_ref_known(v_a_1104_, 1);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v_e_1209_);
v___x_1211_ = v___x_1106_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_e_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
case 1:
{
lean_object* v_e_1213_; lean_object* v___x_1214_; 
lean_del_object(v___x_1106_);
lean_dec_ref(v_e_1096_);
v_e_1213_ = lean_ctor_get(v_a_1104_, 0);
lean_inc_ref(v_e_1213_);
lean_dec_ref_known(v_a_1104_, 1);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1214_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_e_1213_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v_a_1215_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1216_;
}
else
{
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1214_;
}
}
default: 
{
lean_object* v_e_x3f_1217_; 
lean_del_object(v___x_1106_);
v_e_x3f_1217_ = lean_ctor_get(v_a_1104_, 0);
lean_inc(v_e_x3f_1217_);
lean_dec_ref_known(v_a_1104_, 1);
if (lean_obj_tag(v_e_x3f_1217_) == 0)
{
v___y_1109_ = v_e_1096_;
goto v___jp_1108_;
}
else
{
lean_object* v_val_1218_; 
lean_dec_ref(v_e_1096_);
v_val_1218_ = lean_ctor_get(v_e_x3f_1217_, 0);
lean_inc(v_val_1218_);
lean_dec_ref_known(v_e_x3f_1217_, 1);
v___y_1109_ = v_val_1218_;
goto v___jp_1108_;
}
}
}
v___jp_1108_:
{
switch(lean_obj_tag(v___y_1109_))
{
case 7:
{
lean_object* v_binderName_1110_; lean_object* v_binderType_1111_; lean_object* v_body_1112_; uint8_t v_binderInfo_1113_; lean_object* v___x_1114_; 
v_binderName_1110_ = lean_ctor_get(v___y_1109_, 0);
v_binderType_1111_ = lean_ctor_get(v___y_1109_, 1);
v_body_1112_ = lean_ctor_get(v___y_1109_, 2);
v_binderInfo_1113_ = lean_ctor_get_uint8(v___y_1109_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1111_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1114_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_binderType_1111_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
lean_inc_ref(v_body_1112_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_body_1112_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; size_t v___x_1118_; size_t v___x_1119_; uint8_t v___x_1120_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_ptr_addr(v_binderType_1111_);
v___x_1119_ = lean_ptr_addr(v_a_1115_);
v___x_1120_ = lean_usize_dec_eq(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc(v_binderName_1110_);
lean_dec_ref_known(v___y_1109_, 3);
v___x_1121_ = l_Lean_Expr_forallE___override(v_binderName_1110_, v_a_1115_, v_a_1117_, v_binderInfo_1113_);
v___x_1122_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1121_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1122_;
}
else
{
size_t v___x_1123_; size_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = lean_ptr_addr(v_body_1112_);
v___x_1124_ = lean_ptr_addr(v_a_1117_);
v___x_1125_ = lean_usize_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_inc(v_binderName_1110_);
lean_dec_ref_known(v___y_1109_, 3);
v___x_1126_ = l_Lean_Expr_forallE___override(v_binderName_1110_, v_a_1115_, v_a_1117_, v_binderInfo_1113_);
v___x_1127_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1126_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1127_;
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1113_, v_binderInfo_1113_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_inc(v_binderName_1110_);
lean_dec_ref_known(v___y_1109_, 3);
v___x_1129_ = l_Lean_Expr_forallE___override(v_binderName_1110_, v_a_1115_, v_a_1117_, v_binderInfo_1113_);
v___x_1130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1129_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; 
lean_dec(v_a_1117_);
lean_dec(v_a_1115_);
v___x_1131_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___y_1109_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1131_;
}
}
}
}
else
{
lean_dec(v_a_1115_);
lean_dec_ref_known(v___y_1109_, 3);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1116_;
}
}
else
{
lean_dec_ref_known(v___y_1109_, 3);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1114_;
}
}
case 6:
{
lean_object* v_binderName_1132_; lean_object* v_binderType_1133_; lean_object* v_body_1134_; uint8_t v_binderInfo_1135_; lean_object* v___x_1136_; 
v_binderName_1132_ = lean_ctor_get(v___y_1109_, 0);
v_binderType_1133_ = lean_ctor_get(v___y_1109_, 1);
v_body_1134_ = lean_ctor_get(v___y_1109_, 2);
v_binderInfo_1135_ = lean_ctor_get_uint8(v___y_1109_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1133_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1136_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_binderType_1133_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1138_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
lean_inc_ref(v_body_1134_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1138_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_body_1134_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; size_t v___x_1140_; size_t v___x_1141_; uint8_t v___x_1142_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v___x_1140_ = lean_ptr_addr(v_binderType_1133_);
v___x_1141_ = lean_ptr_addr(v_a_1137_);
v___x_1142_ = lean_usize_dec_eq(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_inc(v_binderName_1132_);
lean_dec_ref_known(v___y_1109_, 3);
v___x_1143_ = l_Lean_Expr_lam___override(v_binderName_1132_, v_a_1137_, v_a_1139_, v_binderInfo_1135_);
v___x_1144_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1143_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1144_;
}
else
{
size_t v___x_1145_; size_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_ptr_addr(v_body_1134_);
v___x_1146_ = lean_ptr_addr(v_a_1139_);
v___x_1147_ = lean_usize_dec_eq(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_inc(v_binderName_1132_);
lean_dec_ref_known(v___y_1109_, 3);
v___x_1148_ = l_Lean_Expr_lam___override(v_binderName_1132_, v_a_1137_, v_a_1139_, v_binderInfo_1135_);
v___x_1149_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1148_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1149_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1135_, v_binderInfo_1135_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_inc(v_binderName_1132_);
lean_dec_ref_known(v___y_1109_, 3);
v___x_1151_ = l_Lean_Expr_lam___override(v_binderName_1132_, v_a_1137_, v_a_1139_, v_binderInfo_1135_);
v___x_1152_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1151_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; 
lean_dec(v_a_1139_);
lean_dec(v_a_1137_);
v___x_1153_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___y_1109_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1153_;
}
}
}
}
else
{
lean_dec(v_a_1137_);
lean_dec_ref_known(v___y_1109_, 3);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1138_;
}
}
else
{
lean_dec_ref_known(v___y_1109_, 3);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1136_;
}
}
case 8:
{
lean_object* v_declName_1154_; lean_object* v_type_1155_; lean_object* v_value_1156_; lean_object* v_body_1157_; uint8_t v_nondep_1158_; lean_object* v___x_1159_; 
v_declName_1154_ = lean_ctor_get(v___y_1109_, 0);
v_type_1155_ = lean_ctor_get(v___y_1109_, 1);
v_value_1156_ = lean_ctor_get(v___y_1109_, 2);
v_body_1157_ = lean_ctor_get(v___y_1109_, 3);
v_nondep_1158_ = lean_ctor_get_uint8(v___y_1109_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1155_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1159_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_type_1155_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
lean_inc_ref(v_value_1156_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1161_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_value_1156_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
lean_inc_ref(v_body_1157_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_body_1157_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; size_t v___x_1165_; size_t v___x_1166_; uint8_t v___x_1167_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = lean_ptr_addr(v_type_1155_);
v___x_1166_ = lean_ptr_addr(v_a_1160_);
v___x_1167_ = lean_usize_dec_eq(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc(v_declName_1154_);
lean_dec_ref_known(v___y_1109_, 4);
v___x_1168_ = l_Lean_Expr_letE___override(v_declName_1154_, v_a_1160_, v_a_1162_, v_a_1164_, v_nondep_1158_);
v___x_1169_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1168_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1169_;
}
else
{
size_t v___x_1170_; size_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1170_ = lean_ptr_addr(v_value_1156_);
v___x_1171_ = lean_ptr_addr(v_a_1162_);
v___x_1172_ = lean_usize_dec_eq(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_inc(v_declName_1154_);
lean_dec_ref_known(v___y_1109_, 4);
v___x_1173_ = l_Lean_Expr_letE___override(v_declName_1154_, v_a_1160_, v_a_1162_, v_a_1164_, v_nondep_1158_);
v___x_1174_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1173_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1174_;
}
else
{
size_t v___x_1175_; size_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1175_ = lean_ptr_addr(v_body_1157_);
v___x_1176_ = lean_ptr_addr(v_a_1164_);
v___x_1177_ = lean_usize_dec_eq(v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_inc(v_declName_1154_);
lean_dec_ref_known(v___y_1109_, 4);
v___x_1178_ = l_Lean_Expr_letE___override(v_declName_1154_, v_a_1160_, v_a_1162_, v_a_1164_, v_nondep_1158_);
v___x_1179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1178_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1179_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v_a_1164_);
lean_dec(v_a_1162_);
lean_dec(v_a_1160_);
v___x_1180_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___y_1109_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1180_;
}
}
}
}
else
{
lean_dec(v_a_1162_);
lean_dec(v_a_1160_);
lean_dec_ref_known(v___y_1109_, 4);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1163_;
}
}
else
{
lean_dec(v_a_1160_);
lean_dec_ref_known(v___y_1109_, 4);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1161_;
}
}
else
{
lean_dec_ref_known(v___y_1109_, 4);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1159_;
}
}
case 5:
{
lean_object* v_dummy_1181_; lean_object* v_nargs_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_dummy_1181_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1182_ = l_Lean_Expr_getAppNumArgs(v___y_1109_);
lean_inc(v_nargs_1182_);
v___x_1183_ = lean_mk_array(v_nargs_1182_, v_dummy_1181_);
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_nat_sub(v_nargs_1182_, v___x_1184_);
lean_dec(v_nargs_1182_);
v___x_1186_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1095_, v_post_1097_, v___y_1109_, v___x_1183_, v___x_1185_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1186_;
}
case 10:
{
lean_object* v_data_1187_; lean_object* v_expr_1188_; lean_object* v___x_1189_; 
v_data_1187_ = lean_ctor_get(v___y_1109_, 0);
v_expr_1188_ = lean_ctor_get(v___y_1109_, 1);
lean_inc_ref(v_expr_1188_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1189_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_expr_1188_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; size_t v___x_1191_; size_t v___x_1192_; uint8_t v___x_1193_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = lean_ptr_addr(v_expr_1188_);
v___x_1192_ = lean_ptr_addr(v_a_1190_);
v___x_1193_ = lean_usize_dec_eq(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_inc(v_data_1187_);
lean_dec_ref_known(v___y_1109_, 2);
v___x_1194_ = l_Lean_Expr_mdata___override(v_data_1187_, v_a_1190_);
v___x_1195_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1194_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; 
lean_dec(v_a_1190_);
v___x_1196_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___y_1109_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1196_;
}
}
else
{
lean_dec_ref_known(v___y_1109_, 2);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1189_;
}
}
case 11:
{
lean_object* v_typeName_1197_; lean_object* v_idx_1198_; lean_object* v_struct_1199_; lean_object* v___x_1200_; 
v_typeName_1197_ = lean_ctor_get(v___y_1109_, 0);
v_idx_1198_ = lean_ctor_get(v___y_1109_, 1);
v_struct_1199_ = lean_ctor_get(v___y_1109_, 2);
lean_inc_ref(v_struct_1199_);
lean_inc_ref(v_post_1097_);
lean_inc_ref(v_pre_1095_);
v___x_1200_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1095_, v_post_1097_, v_struct_1199_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; size_t v___x_1202_; size_t v___x_1203_; uint8_t v___x_1204_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v___x_1202_ = lean_ptr_addr(v_struct_1199_);
v___x_1203_ = lean_ptr_addr(v_a_1201_);
v___x_1204_ = lean_usize_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc(v_idx_1198_);
lean_inc(v_typeName_1197_);
lean_dec_ref_known(v___y_1109_, 3);
v___x_1205_ = l_Lean_Expr_proj___override(v_typeName_1197_, v_idx_1198_, v_a_1201_);
v___x_1206_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___x_1205_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1206_;
}
else
{
lean_object* v___x_1207_; 
lean_dec(v_a_1201_);
v___x_1207_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___y_1109_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1207_;
}
}
else
{
lean_dec_ref_known(v___y_1109_, 3);
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_pre_1095_);
return v___x_1200_;
}
}
default: 
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1095_, v_post_1097_, v___y_1109_, v___y_1098_, v___y_1099_, v___y_1100_);
return v___x_1208_;
}
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_e_1096_);
lean_dec_ref(v_pre_1095_);
v_a_1220_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1103_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1103_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_post_1097_);
lean_dec_ref(v_e_1096_);
lean_dec_ref(v_pre_1095_);
v_a_1228_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1102_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1102_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1236_, lean_object* v_pre_1237_, lean_object* v_e_1238_, lean_object* v_post_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1236_, v_pre_1237_, v_e_1238_, v_post_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1245_, lean_object* v_post_1246_, lean_object* v_e_1247_, lean_object* v_a_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_inc(v_a_1248_);
v___x_1252_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1252_, 0, lean_box(0));
lean_closure_set(v___x_1252_, 1, lean_box(0));
lean_closure_set(v___x_1252_, 2, v_a_1248_);
v___x_1253_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1252_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1285_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1285_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1285_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1254_, v_e_1247_);
lean_dec(v_a_1254_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; 
lean_del_object(v___x_1256_);
v___x_1259_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1247_);
v___f_1260_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1260_, 0, v___x_1259_);
lean_closure_set(v___f_1260_, 1, v_pre_1245_);
lean_closure_set(v___f_1260_, 2, v_e_1247_);
lean_closure_set(v___f_1260_, 3, v_post_1246_);
v___x_1261_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1260_, v_a_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc_n(v_a_1262_, 2);
lean_dec_ref_known(v___x_1261_, 1);
lean_inc(v_a_1248_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1263_, 0, v_a_1248_);
lean_closure_set(v___f_1263_, 1, v_e_1247_);
lean_closure_set(v___f_1263_, 2, v_a_1262_);
v___x_1264_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1263_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1272_);
v___x_1266_ = v___x_1264_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_dec(v___x_1264_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_a_1262_);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1262_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_a_1262_);
v_a_1273_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1264_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1264_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_dec_ref(v_e_1247_);
return v___x_1261_;
}
}
else
{
lean_object* v_val_1281_; lean_object* v___x_1283_; 
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_post_1246_);
lean_dec_ref(v_pre_1245_);
v_val_1281_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1258_, 1);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_val_1281_);
v___x_1283_ = v___x_1256_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_val_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_e_1247_);
lean_dec_ref(v_post_1246_);
lean_dec_ref(v_pre_1245_);
v_a_1286_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1253_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1253_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1294_, lean_object* v_post_1295_, lean_object* v_e_1296_, lean_object* v_a_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
lean_inc_ref(v_post_1295_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc_ref(v_e_1296_);
v___x_1301_ = lean_apply_4(v_post_1295_, v_e_1296_, v___y_1298_, v___y_1299_, lean_box(0));
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1320_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1320_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1320_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
switch(lean_obj_tag(v_a_1302_))
{
case 0:
{
lean_object* v_e_1306_; lean_object* v___x_1308_; 
lean_dec_ref(v_e_1296_);
lean_dec_ref(v_post_1295_);
lean_dec_ref(v_pre_1294_);
v_e_1306_ = lean_ctor_get(v_a_1302_, 0);
lean_inc_ref(v_e_1306_);
lean_dec_ref_known(v_a_1302_, 1);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v_e_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_e_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
case 1:
{
lean_object* v_e_1310_; lean_object* v___x_1311_; 
lean_del_object(v___x_1304_);
lean_dec_ref(v_e_1296_);
v_e_1310_ = lean_ctor_get(v_a_1302_, 0);
lean_inc_ref(v_e_1310_);
lean_dec_ref_known(v_a_1302_, 1);
v___x_1311_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1294_, v_post_1295_, v_e_1310_, v_a_1297_, v___y_1298_, v___y_1299_);
return v___x_1311_;
}
default: 
{
lean_object* v_e_x3f_1312_; 
lean_dec_ref(v_post_1295_);
lean_dec_ref(v_pre_1294_);
v_e_x3f_1312_ = lean_ctor_get(v_a_1302_, 0);
lean_inc(v_e_x3f_1312_);
lean_dec_ref_known(v_a_1302_, 1);
if (lean_obj_tag(v_e_x3f_1312_) == 0)
{
lean_object* v___x_1314_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v_e_1296_);
v___x_1314_ = v___x_1304_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_e_1296_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1318_; 
lean_dec_ref(v_e_1296_);
v_val_1316_ = lean_ctor_get(v_e_x3f_1312_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v_e_x3f_1312_, 1);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v_val_1316_);
v___x_1318_ = v___x_1304_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_val_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_e_1296_);
lean_dec_ref(v_post_1295_);
lean_dec_ref(v_pre_1294_);
v_a_1321_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1301_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1301_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1329_, lean_object* v_post_1330_, lean_object* v_e_1331_, lean_object* v_a_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1329_, v_post_1330_, v_e_1331_, v_a_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v_a_1332_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1337_, lean_object* v_post_1338_, lean_object* v_sz_1339_, lean_object* v_i_1340_, lean_object* v_bs_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
size_t v_sz_boxed_1346_; size_t v_i_boxed_1347_; lean_object* v_res_1348_; 
v_sz_boxed_1346_ = lean_unbox_usize(v_sz_1339_);
lean_dec(v_sz_1339_);
v_i_boxed_1347_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_res_1348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1337_, v_post_1338_, v_sz_boxed_1346_, v_i_boxed_1347_, v_bs_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1349_, lean_object* v_post_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1349_, v_post_1350_, v_x_1351_, v_x_1352_, v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1359_, lean_object* v_post_1360_, lean_object* v_e_1361_, lean_object* v_a_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1359_, v_post_1360_, v_e_1361_, v_a_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v_a_1362_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_apply_1(v_x_1368_, lean_box(0));
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1374_, v_x_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_unsigned_to_nat(16u);
v___x_1382_ = lean_mk_array(v___x_1381_, v___x_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v___x_1383_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1387_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1387_, 0, lean_box(0));
lean_closure_set(v___x_1387_, 1, lean_box(0));
lean_closure_set(v___x_1387_, 2, v___x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1388_, lean_object* v_pre_1389_, lean_object* v_post_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_a_1396_; lean_object* v___x_1397_; 
v___x_1394_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1395_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1394_, v___y_1391_, v___y_1392_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1389_, v_post_1390_, v_input_1388_, v_a_1396_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1399_, 0, lean_box(0));
lean_closure_set(v___x_1399_, 1, lean_box(0));
lean_closure_set(v___x_1399_, 2, v_a_1396_);
v___x_1400_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1399_, v___y_1391_, v___y_1392_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v___x_1400_, 0);
lean_dec(v_unused_1408_);
v___x_1402_ = v___x_1400_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v___x_1400_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v_a_1398_);
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1398_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_dec(v_a_1396_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1409_, lean_object* v_pre_1410_, lean_object* v_post_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1409_, v_pre_1410_, v_post_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___f_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; 
v___f_1422_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1423_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1424_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1418_, v___f_1422_, v___f_1423_, v_a_1419_, v_a_1420_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1431_, v_a_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1434_, v_m_1435_, v_a_1436_);
lean_dec_ref(v_a_1436_);
lean_dec_ref(v_m_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1438_, lean_object* v_ref_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1439_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_ref_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1444_, v_ref_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1460_, lean_object* v_x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1467_, v_x_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1474_, lean_object* v_m_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1475_, v_a_1476_, v_b_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1479_, lean_object* v_a_1480_, lean_object* v_x_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1480_, v_x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1483_, lean_object* v_a_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1483_, v_a_1484_, v_x_1485_);
lean_dec(v_x_1485_);
lean_dec_ref(v_a_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1487_, lean_object* v_a_1488_, lean_object* v_x_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1488_, v_x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1491_, lean_object* v_a_1492_, lean_object* v_x_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1491_, v_a_1492_, v_x_1493_);
lean_dec(v_x_1493_);
lean_dec_ref(v_a_1492_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1496_, lean_object* v_data_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1499_, lean_object* v_a_1500_, lean_object* v_b_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1500_, v_b_1501_, v_x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1504_, lean_object* v_i_1505_, lean_object* v_source_1506_, lean_object* v_target_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1505_, v_source_1506_, v_target_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1510_, v_x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v_env_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1516_ = lean_st_ref_get(v___y_1514_);
v_env_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc_ref(v_env_1517_);
lean_dec(v___x_1516_);
v___x_1518_ = l_Lean_isRecCore(v_env_1517_, v_declName_1513_);
v___x_1519_ = lean_box(v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1521_, v___y_1522_);
lean_dec(v___y_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1525_, v___y_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v_env_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1542_ = lean_st_ref_get(v___y_1540_);
v_env_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc_ref(v_env_1543_);
lean_dec(v___x_1542_);
v___x_1544_ = l_Lean_getReducibilityStatusCore(v_env_1543_, v_declName_1539_);
v___x_1545_ = lean_box(v___x_1544_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1547_, v___y_1548_);
lean_dec(v___y_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1573_; 
v___x_1557_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1551_, v___y_1555_);
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1573_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1573_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_unbox(v_a_1558_);
lean_dec(v_a_1558_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = 1;
v___x_1564_ = lean_box(v___x_1563_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1564_);
v___x_1566_ = v___x_1560_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
else
{
uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = 0;
v___x_1569_ = lean_box(v___x_1568_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1569_);
v___x_1571_ = v___x_1560_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
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
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1581_, lean_object* v_b_1582_){
_start:
{
lean_object* v_array_1584_; lean_object* v_start_1585_; lean_object* v_stop_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1603_; 
v_array_1584_ = lean_ctor_get(v_a_1581_, 0);
v_start_1585_ = lean_ctor_get(v_a_1581_, 1);
v_stop_1586_ = lean_ctor_get(v_a_1581_, 2);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_a_1581_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1588_ = v_a_1581_;
v_isShared_1589_ = v_isSharedCheck_1603_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_stop_1586_);
lean_inc(v_start_1585_);
lean_inc(v_array_1584_);
lean_dec(v_a_1581_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1603_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_nat_dec_lt(v_start_1585_, v_stop_1586_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
lean_del_object(v___x_1588_);
lean_dec(v_stop_1586_);
lean_dec(v_start_1585_);
lean_dec_ref(v_array_1584_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_b_1582_);
return v___x_1591_;
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_add(v_start_1585_, v___x_1593_);
lean_inc_ref(v_array_1584_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___x_1594_);
v___x_1596_ = v___x_1588_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_array_1584_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_stop_1586_);
v___x_1596_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = lean_array_fget(v_array_1584_, v_start_1585_);
lean_dec(v_start_1585_);
lean_dec_ref(v_array_1584_);
v___x_1598_ = l_Lean_Expr_hasExprMVar(v___x_1597_);
lean_dec(v___x_1597_);
if (v___x_1598_ == 0)
{
v_a_1581_ = v___x_1596_;
v_b_1582_ = v___x_1592_;
goto _start;
}
else
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_dec_ref_known(v___x_1600_, 1);
v_a_1581_ = v___x_1596_;
v_b_1582_ = v___x_1592_;
goto _start;
}
else
{
lean_dec_ref(v___x_1596_);
return v___x_1600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1604_, lean_object* v_b_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1604_, v_b_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1616_, uint8_t v_isMatch_1617_, uint8_t v_root_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___y_1625_; lean_object* v_b_1626_; lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1616_, v_root_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1800_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1800_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1800_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___y_1643_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; 
if (v_root_1618_ == 0)
{
lean_object* v___x_1788_; 
lean_inc(v_a_1638_);
v___x_1788_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1638_);
if (lean_obj_tag(v___x_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1799_; 
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_val_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1799_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 2);
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_val_1789_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
else
{
lean_dec(v___x_1788_);
v___y_1653_ = v_a_1619_;
v___y_1654_ = v_a_1620_;
v___y_1655_ = v_a_1621_;
v___y_1656_ = v_a_1622_;
goto v___jp_1652_;
}
}
else
{
v___y_1653_ = v_a_1619_;
v___y_1654_ = v_a_1620_;
v___y_1655_ = v_a_1621_;
v___y_1656_ = v_a_1622_;
goto v___jp_1652_;
}
v___jp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1644_ = l_Lean_Expr_getAppNumArgs(v_a_1638_);
lean_inc(v___x_1644_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___y_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_mk_empty_array_with_capacity(v___x_1644_);
lean_dec(v___x_1644_);
v___x_1647_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1638_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1645_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1648_);
v___x_1650_ = v___x_1640_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
v___jp_1652_:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Expr_getAppFn(v_a_1638_);
switch(lean_obj_tag(v___x_1657_))
{
case 1:
{
lean_object* v_fvarId_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_del_object(v___x_1640_);
v_fvarId_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_fvarId_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = l_Lean_Expr_getAppNumArgs(v_a_1638_);
lean_inc(v___x_1659_);
v___x_1660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1660_, 0, v_fvarId_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_mk_empty_array_with_capacity(v___x_1659_);
lean_dec(v___x_1659_);
v___x_1662_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1638_, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1660_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
case 2:
{
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
if (v_isMatch_1617_ == 0)
{
lean_object* v_mvarId_1665_; lean_object* v___x_1666_; uint8_t v_isDefEqStuckEx_1667_; 
v_mvarId_1665_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_mvarId_1665_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1666_ = l_Lean_Meta_Context_config(v___y_1653_);
v_isDefEqStuckEx_1667_ = lean_ctor_get_uint8(v___x_1666_, 4);
lean_dec_ref(v___x_1666_);
if (v_isDefEqStuckEx_1667_ == 0)
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1665_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1682_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_unbox(v_a_1669_);
lean_dec(v_a_1669_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1678_);
v___x_1680_ = v___x_1671_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1668_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1668_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_mvarId_1665_);
v___x_1691_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec_ref_known(v___x_1657_, 1);
v___x_1693_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
return v___x_1694_;
}
}
case 4:
{
lean_object* v_declName_1695_; lean_object* v___x_1696_; uint8_t v_isDefEqStuckEx_1697_; 
v_declName_1695_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_declName_1695_);
lean_dec_ref_known(v___x_1657_, 2);
v___x_1696_ = l_Lean_Meta_Context_config(v___y_1653_);
v_isDefEqStuckEx_1697_ = lean_ctor_get_uint8(v___x_1696_, 4);
lean_dec_ref(v___x_1696_);
if (v_isDefEqStuckEx_1697_ == 0)
{
v___y_1643_ = v_declName_1695_;
goto v___jp_1642_;
}
else
{
uint8_t v___x_1698_; 
v___x_1698_ = l_Lean_Expr_hasExprMVar(v_a_1638_);
if (v___x_1698_ == 0)
{
v___y_1643_ = v_declName_1695_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1699_; 
lean_inc(v_declName_1695_);
v___x_1699_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1695_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; uint8_t v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = lean_unbox(v_a_1700_);
lean_dec(v_a_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v_env_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_st_ref_get(v___y_1656_);
v_env_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_ref(v_env_1703_);
lean_dec(v___x_1702_);
v___x_1704_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1703_, v_a_1638_);
if (lean_obj_tag(v___x_1704_) == 1)
{
lean_object* v_val_1705_; lean_object* v_numDiscrs_1706_; lean_object* v_nargs_1707_; lean_object* v_dummy_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_val_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v_numDiscrs_1706_ = lean_ctor_get(v_val_1705_, 1);
lean_inc(v_numDiscrs_1706_);
v_nargs_1707_ = l_Lean_Expr_getAppNumArgs(v_a_1638_);
v_dummy_1708_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1707_);
v___x_1709_ = lean_mk_array(v_nargs_1707_, v_dummy_1708_);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_sub(v_nargs_1707_, v___x_1710_);
lean_dec(v_nargs_1707_);
lean_inc(v_a_1638_);
v___x_1712_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1638_, v___x_1709_, v___x_1711_);
v___x_1713_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1705_);
lean_dec(v_val_1705_);
v___x_1714_ = lean_nat_add(v___x_1713_, v_numDiscrs_1706_);
lean_dec(v_numDiscrs_1706_);
v___x_1715_ = l_Array_toSubarray___redArg(v___x_1712_, v___x_1713_, v___x_1714_);
v___x_1716_ = lean_box(0);
v___x_1717_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1715_, v___x_1716_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_dec_ref_known(v___x_1717_, 1);
v___y_1643_ = v_declName_1695_;
goto v___jp_1642_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_declName_1695_);
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v___x_1726_; lean_object* v_a_1727_; uint8_t v___x_1728_; 
lean_dec(v___x_1704_);
lean_inc(v_declName_1695_);
v___x_1726_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1695_, v___y_1656_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = lean_unbox(v_a_1727_);
lean_dec(v_a_1727_);
if (v___x_1728_ == 0)
{
v___y_1643_ = v_declName_1695_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_dec_ref_known(v___x_1729_, 1);
v___y_1643_ = v_declName_1695_;
goto v___jp_1642_;
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_declName_1695_);
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
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
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref_known(v___x_1738_, 1);
v___y_1643_ = v_declName_1695_;
goto v___jp_1642_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_declName_1695_);
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
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
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_declName_1695_);
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v_a_1747_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1699_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1699_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1755_; lean_object* v_body_1756_; uint8_t v___x_1757_; 
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v_binderType_1755_ = lean_ctor_get(v___x_1657_, 1);
lean_inc_ref(v_binderType_1755_);
v_body_1756_ = lean_ctor_get(v___x_1657_, 2);
lean_inc_ref(v_body_1756_);
lean_dec_ref_known(v___x_1657_, 3);
v___x_1757_ = l_Lean_Expr_hasLooseBVars(v_body_1756_);
if (v___x_1757_ == 0)
{
v___y_1625_ = v_binderType_1755_;
v_b_1626_ = v_body_1756_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1756_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___y_1625_ = v_binderType_1755_;
v_b_1626_ = v_a_1759_;
goto v___jp_1624_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_binderType_1755_);
v_a_1760_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1758_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1758_);
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
case 9:
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v_a_1768_ = lean_ctor_get(v___x_1657_, 0);
lean_inc_ref(v_a_1768_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1769_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_a_1768_);
v___x_1770_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
case 11:
{
lean_object* v_typeName_1773_; lean_object* v_idx_1774_; lean_object* v_struct_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_del_object(v___x_1640_);
v_typeName_1773_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_typeName_1773_);
v_idx_1774_ = lean_ctor_get(v___x_1657_, 1);
lean_inc(v_idx_1774_);
v_struct_1775_ = lean_ctor_get(v___x_1657_, 2);
lean_inc_ref(v_struct_1775_);
lean_dec_ref_known(v___x_1657_, 3);
v___x_1776_ = l_Lean_Expr_getAppNumArgs(v_a_1638_);
lean_inc(v___x_1776_);
v___x_1777_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1777_, 0, v_typeName_1773_);
lean_ctor_set(v___x_1777_, 1, v_idx_1774_);
lean_ctor_set(v___x_1777_, 2, v___x_1776_);
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_mk_empty_array_with_capacity(v___x_1778_);
v___x_1780_ = lean_array_push(v___x_1779_, v_struct_1775_);
v___x_1781_ = lean_mk_empty_array_with_capacity(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1782_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1638_, v___x_1781_);
v___x_1783_ = l_Array_append___redArg(v___x_1780_, v___x_1782_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1777_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
default: 
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec_ref(v___x_1657_);
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v___x_1786_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1637_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1637_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
v___jp_1624_:
{
uint8_t v___x_1627_; 
v___x_1627_ = l_Lean_Expr_hasLooseBVars(v_b_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1628_ = lean_box(5);
v___x_1629_ = lean_unsigned_to_nat(2u);
v___x_1630_ = lean_mk_empty_array_with_capacity(v___x_1629_);
v___x_1631_ = lean_array_push(v___x_1630_, v___y_1625_);
v___x_1632_ = lean_array_push(v___x_1631_, v_b_1626_);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1628_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v_b_1626_);
lean_dec_ref(v___y_1625_);
v___x_1635_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1809_, lean_object* v_isMatch_1810_, lean_object* v_root_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
uint8_t v_isMatch_boxed_1817_; uint8_t v_root_boxed_1818_; lean_object* v_res_1819_; 
v_isMatch_boxed_1817_ = lean_unbox(v_isMatch_1810_);
v_root_boxed_1818_ = lean_unbox(v_root_1811_);
v_res_1819_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1809_, v_isMatch_boxed_1817_, v_root_boxed_1818_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1820_, v___y_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1834_, lean_object* v_R_1835_, lean_object* v_a_1836_, lean_object* v_b_1837_, lean_object* v_c_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1836_, v_b_1837_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1845_, lean_object* v_R_1846_, lean_object* v_a_1847_, lean_object* v_b_1848_, lean_object* v_c_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1845_, v_R_1846_, v_a_1847_, v_b_1848_, v_c_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1856_, uint8_t v_root_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
uint8_t v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = 1;
v___x_1864_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1856_, v___x_1863_, v_root_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1865_, lean_object* v_root_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
uint8_t v_root_boxed_1872_; lean_object* v_res_1873_; 
v_root_boxed_1872_ = lean_unbox(v_root_1866_);
v_res_1873_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1865_, v_root_boxed_1872_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
return v_res_1873_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_unsigned_to_nat(16u);
v___x_1878_ = lean_mk_array(v___x_1877_, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1879_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1884_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_1885_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___x_1886_);
lean_ctor_set(v___x_1888_, 2, v___x_1885_);
lean_ctor_set(v___x_1888_, 3, v___x_1884_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1893_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1896_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v___x_1897_);
lean_ctor_set(v___x_1899_, 2, v___x_1896_);
lean_ctor_set(v___x_1899_, 3, v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1902_, lean_object* v_x_1903_){
_start:
{
lean_object* v_values_1904_; lean_object* v_star_1905_; lean_object* v_children_1906_; lean_object* v_pending_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
v_values_1904_ = lean_ctor_get(v_x_1902_, 0);
v_star_1905_ = lean_ctor_get(v_x_1902_, 1);
v_children_1906_ = lean_ctor_get(v_x_1902_, 2);
v_pending_1907_ = lean_ctor_get(v_x_1902_, 3);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_x_1902_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1909_ = v_x_1902_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_pending_1907_);
lean_inc(v_children_1906_);
lean_inc(v_star_1905_);
lean_inc(v_values_1904_);
lean_dec(v_x_1902_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_array_push(v_pending_1907_, v_x_1903_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 3, v___x_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_values_1904_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_star_1905_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_children_1906_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1917_, v_x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1921_ = lean_unsigned_to_nat(1u);
v___x_1922_ = lean_mk_empty_array_with_capacity(v___x_1921_);
v___x_1923_ = lean_array_push(v___x_1922_, v___x_1920_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1925_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___x_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; lean_object* v_env_1936_; lean_object* v___x_1937_; lean_object* v_mctx_1938_; lean_object* v_lctx_1939_; lean_object* v_options_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1935_ = lean_st_ref_get(v___y_1933_);
v_env_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc_ref(v_env_1936_);
lean_dec(v___x_1935_);
v___x_1937_ = lean_st_ref_get(v___y_1931_);
v_mctx_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc_ref(v_mctx_1938_);
lean_dec(v___x_1937_);
v_lctx_1939_ = lean_ctor_get(v___y_1930_, 2);
v_options_1940_ = lean_ctor_get(v___y_1932_, 2);
lean_inc_ref(v_options_1940_);
lean_inc_ref(v_lctx_1939_);
v___x_1941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1941_, 0, v_env_1936_);
lean_ctor_set(v___x_1941_, 1, v_mctx_1938_);
lean_ctor_set(v___x_1941_, 2, v_lctx_1939_);
lean_ctor_set(v___x_1941_, 3, v_options_1940_);
v___x_1942_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_msgData_1929_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_ref_1957_; lean_object* v___x_1958_; lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1967_; 
v_ref_1957_ = lean_ctor_get(v___y_1954_, 5);
v___x_1958_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
lean_inc(v_ref_1957_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v_ref_1957_);
lean_ctor_set(v___x_1963_, 1, v_a_1959_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 1);
lean_ctor_set(v___x_1961_, 0, v___x_1963_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1978_, lean_object* v_todo_1979_, lean_object* v_e_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1980_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1980_, v_root_1978_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2127_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_2127_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2127_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_v_1993_; lean_object* v___x_1999_; lean_object* v_k_2001_; lean_object* v_nargs_2002_; lean_object* v_todo_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; 
v___x_1999_ = l_Lean_Expr_getAppFn(v_a_1988_);
switch(lean_obj_tag(v___x_1999_))
{
case 9:
{
lean_object* v_a_2046_; 
lean_dec(v_a_1988_);
v_a_2046_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref(v_a_2046_);
lean_dec_ref_known(v___x_1999_, 1);
v_v_1993_ = v_a_2046_;
goto v___jp_1992_;
}
case 4:
{
lean_object* v_declName_2047_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; 
v_declName_2047_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_declName_2047_);
if (v_root_1978_ == 0)
{
lean_object* v___x_2055_; 
lean_inc(v_a_1988_);
v___x_2055_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1988_);
if (lean_obj_tag(v___x_2055_) == 1)
{
lean_object* v_val_2056_; 
lean_dec(v_declName_2047_);
lean_dec_ref_known(v___x_1999_, 2);
lean_dec(v_a_1988_);
v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v_v_1993_ = v_val_2056_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2057_; 
lean_dec(v___x_2055_);
lean_del_object(v___x_1990_);
v___x_2057_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2047_, v_a_1988_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2068_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2068_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2068_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_unbox(v_a_2058_);
lean_dec(v_a_2058_);
if (v___x_2062_ == 0)
{
lean_del_object(v___x_2060_);
v___y_2049_ = v_a_1981_;
v___y_2050_ = v_a_1982_;
v___y_2051_ = v_a_1983_;
v___y_2052_ = v_a_1984_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v_declName_2047_);
lean_dec_ref_known(v___x_1999_, 2);
lean_dec(v_a_1988_);
v___x_2063_ = lean_box(3);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_todo_1979_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2064_);
v___x_2066_ = v___x_2060_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref_known(v___x_1999_, 2);
lean_dec(v_declName_2047_);
lean_dec(v_a_1988_);
lean_dec_ref(v_todo_1979_);
v_a_2069_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2057_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2057_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
else
{
lean_del_object(v___x_1990_);
v___y_2049_ = v_a_1981_;
v___y_2050_ = v_a_1982_;
v___y_2051_ = v_a_1983_;
v___y_2052_ = v_a_1984_;
goto v___jp_2048_;
}
v___jp_2048_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = l_Lean_Expr_getAppNumArgs(v_a_1988_);
lean_inc(v___x_2053_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_declName_2047_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v_k_2001_ = v___x_2054_;
v_nargs_2002_ = v___x_2053_;
v_todo_2003_ = v_todo_1979_;
v___y_2004_ = v___y_2049_;
v___y_2005_ = v___y_2050_;
v___y_2006_ = v___y_2051_;
v___y_2007_ = v___y_2052_;
goto v___jp_2000_;
}
}
case 11:
{
lean_object* v_typeName_2077_; lean_object* v_idx_2078_; lean_object* v_struct_2079_; lean_object* v___x_2080_; lean_object* v___y_2082_; lean_object* v_env_2086_; uint8_t v___x_2087_; 
lean_del_object(v___x_1990_);
v_typeName_2077_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_typeName_2077_);
v_idx_2078_ = lean_ctor_get(v___x_1999_, 1);
lean_inc(v_idx_2078_);
v_struct_2079_ = lean_ctor_get(v___x_1999_, 2);
lean_inc_ref(v_struct_2079_);
v___x_2080_ = lean_st_ref_get(v_a_1984_);
v_env_2086_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_ref(v_env_2086_);
lean_dec(v___x_2080_);
v___x_2087_ = l_Lean_isClass(v_env_2086_, v_typeName_2077_);
if (v___x_2087_ == 0)
{
v___y_2082_ = v_struct_2079_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2079_);
v___y_2082_ = v___x_2088_;
goto v___jp_2081_;
}
v___jp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = l_Lean_Expr_getAppNumArgs(v_a_1988_);
lean_inc(v___x_2083_);
v___x_2084_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2084_, 0, v_typeName_2077_);
lean_ctor_set(v___x_2084_, 1, v_idx_2078_);
lean_ctor_set(v___x_2084_, 2, v___x_2083_);
v___x_2085_ = lean_array_push(v_todo_1979_, v___y_2082_);
v_k_2001_ = v___x_2084_;
v_nargs_2002_ = v___x_2083_;
v_todo_2003_ = v___x_2085_;
v___y_2004_ = v_a_1981_;
v___y_2005_ = v_a_1982_;
v___y_2006_ = v_a_1983_;
v___y_2007_ = v_a_1984_;
goto v___jp_2000_;
}
}
case 1:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec_ref_known(v___x_1999_, 1);
lean_del_object(v___x_1990_);
lean_dec(v_a_1988_);
v___x_2089_ = lean_box(3);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_todo_1979_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
case 2:
{
lean_object* v_mvarId_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
lean_del_object(v___x_1990_);
lean_dec(v_a_1988_);
v_mvarId_2092_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_mvarId_2092_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2093_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2094_ = l_Lean_instBEqMVarId_beq(v_mvarId_2092_, v___x_2093_);
lean_dec(v_mvarId_2092_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec_ref(v_todo_1979_);
v___x_2095_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2096_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2095_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_box(3);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_todo_1979_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
case 7:
{
lean_object* v_binderType_2100_; lean_object* v_body_2101_; lean_object* v_b_2103_; uint8_t v___x_2113_; 
lean_del_object(v___x_1990_);
lean_dec(v_a_1988_);
v_binderType_2100_ = lean_ctor_get(v___x_1999_, 1);
lean_inc_ref(v_binderType_2100_);
v_body_2101_ = lean_ctor_get(v___x_1999_, 2);
lean_inc_ref(v_body_2101_);
lean_dec_ref_known(v___x_1999_, 3);
v___x_2113_ = l_Lean_Expr_hasLooseBVars(v_body_2101_);
if (v___x_2113_ == 0)
{
v_b_2103_ = v_body_2101_;
goto v___jp_2102_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2101_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v_b_2103_ = v_a_2115_;
goto v___jp_2102_;
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_binderType_2100_);
lean_dec_ref(v_todo_1979_);
v_a_2116_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2114_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2114_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
v___jp_2102_:
{
uint8_t v___x_2104_; 
v___x_2104_ = l_Lean_Expr_hasLooseBVars(v_b_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2105_ = lean_box(5);
v___x_2106_ = lean_array_push(v_todo_1979_, v_binderType_2100_);
v___x_2107_ = lean_array_push(v___x_2106_, v_b_2103_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2105_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec_ref(v_b_2103_);
lean_dec_ref(v_binderType_2100_);
v___x_2110_ = lean_box(4);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v_todo_1979_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
}
default: 
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v___x_1999_);
lean_del_object(v___x_1990_);
lean_dec(v_a_1988_);
v___x_2124_ = lean_box(4);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v_todo_1979_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
v___jp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_v_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v_todo_1979_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1995_);
v___x_1997_ = v___x_1990_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
v___jp_2000_:
{
lean_object* v___x_2008_; 
lean_inc(v_nargs_2002_);
v___x_2008_ = l_Lean_Meta_getFunInfoNArgs(v___x_1999_, v_nargs_2002_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v_paramInfo_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2036_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v_paramInfo_2010_ = lean_ctor_get(v_a_2009_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2009_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v_a_2009_, 1);
lean_dec(v_unused_2037_);
v___x_2012_ = v_a_2009_;
v_isShared_2013_ = v_isSharedCheck_2036_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_paramInfo_2010_);
lean_dec(v_a_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2036_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_nat_sub(v_nargs_2002_, v___x_2014_);
lean_dec(v_nargs_2002_);
v___x_2016_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2010_, v___x_2015_, v_a_1988_, v_todo_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec_ref(v_paramInfo_2010_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2027_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v_a_2017_);
lean_ctor_set(v___x_2012_, 0, v_k_2001_);
v___x_2022_ = v___x_2012_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_k_2001_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2022_);
v___x_2024_ = v___x_2019_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_del_object(v___x_2012_);
lean_dec(v_k_2001_);
v_a_2028_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2016_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2016_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_todo_2003_);
lean_dec(v_nargs_2002_);
lean_dec(v_k_2001_);
lean_dec(v_a_1988_);
v_a_2038_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2008_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2008_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v_todo_1979_);
v_a_2128_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_1987_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_1987_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref(v_e_1980_);
v___x_2136_ = lean_box(3);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set(v___x_2137_, 1, v_todo_1979_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2139_, lean_object* v_todo_2140_, lean_object* v_e_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
uint8_t v_root_boxed_2147_; lean_object* v_res_2148_; 
v_root_boxed_2147_ = lean_unbox(v_root_2139_);
v_res_2148_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2147_, v_todo_2140_, v_e_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2149_, lean_object* v_msg_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2157_, lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2157_, v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
return v_res_2164_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_unsigned_to_nat(8u);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2172_ = 1;
v___x_2173_ = lean_unsigned_to_nat(8u);
v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2173_);
v___x_2175_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2172_, v___x_2174_, v_e_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2183_, uint8_t v_root_2184_, lean_object* v_todo_2185_, lean_object* v_keys_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2192_ = lean_array_get_size(v_todo_2185_);
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = lean_nat_dec_eq(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_e_2198_; lean_object* v_todo_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2195_ = l_Lean_instInhabitedExpr;
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_nat_sub(v___x_2192_, v___x_2196_);
v_e_2198_ = lean_array_get(v___x_2195_, v_todo_2185_, v___x_2197_);
lean_dec(v___x_2197_);
v_todo_2199_ = lean_array_pop(v_todo_2185_);
v___x_2200_ = lean_box(v_root_2184_);
lean_inc_ref(v_op_2183_);
lean_inc(v_a_2190_);
lean_inc_ref(v_a_2189_);
lean_inc(v_a_2188_);
lean_inc_ref(v_a_2187_);
v___x_2201_ = lean_apply_8(v_op_2183_, v___x_2200_, v_todo_2199_, v_e_2198_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, lean_box(0));
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v_fst_2203_; lean_object* v_snd_2204_; lean_object* v___x_2205_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v_fst_2203_ = lean_ctor_get(v_a_2202_, 0);
lean_inc(v_fst_2203_);
v_snd_2204_ = lean_ctor_get(v_a_2202_, 1);
lean_inc(v_snd_2204_);
lean_dec(v_a_2202_);
v___x_2205_ = lean_array_push(v_keys_2186_, v_fst_2203_);
v_root_2184_ = v___x_2194_;
v_todo_2185_ = v_snd_2204_;
v_keys_2186_ = v___x_2205_;
goto _start;
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v_keys_2186_);
lean_dec_ref(v_op_2183_);
v_a_2207_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2201_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2201_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v___x_2215_; 
lean_dec_ref(v_todo_2185_);
lean_dec_ref(v_op_2183_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_keys_2186_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2216_, lean_object* v_root_2217_, lean_object* v_todo_2218_, lean_object* v_keys_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
uint8_t v_root_boxed_2225_; lean_object* v_res_2226_; 
v_root_boxed_2225_ = lean_unbox(v_root_2217_);
v_res_2226_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2216_, v_root_boxed_2225_, v_todo_2218_, v_keys_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_op_2234_; lean_object* v___x_2235_; lean_object* v_todo_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_op_2234_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2235_ = lean_unsigned_to_nat(8u);
v_todo_2236_ = lean_mk_empty_array_with_capacity(v___x_2235_);
v___x_2237_ = 1;
lean_inc_ref(v_todo_2236_);
v___x_2238_ = lean_array_push(v_todo_2236_, v_e_2228_);
v___x_2239_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2234_, v___x_2237_, v___x_2238_, v_todo_2236_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2247_, lean_object* v_todo_2248_, lean_object* v_e_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
uint8_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = 1;
v___x_2256_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2249_, v___x_2255_, v_root_2247_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2274_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2274_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2274_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_fst_2261_; lean_object* v_snd_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2273_; 
v_fst_2261_ = lean_ctor_get(v_a_2257_, 0);
v_snd_2262_ = lean_ctor_get(v_a_2257_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_a_2257_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2264_ = v_a_2257_;
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snd_2262_);
lean_inc(v_fst_2261_);
lean_dec(v_a_2257_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = l_Array_append___redArg(v_todo_2248_, v_snd_2262_);
lean_dec(v_snd_2262_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_fst_2261_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2268_);
v___x_2270_ = v___x_2259_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2248_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2275_, lean_object* v_todo_2276_, lean_object* v_e_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v_root_boxed_2283_; lean_object* v_res_2284_; 
v_root_boxed_2283_ = lean_unbox(v_root_2275_);
v_res_2284_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2283_, v_todo_2276_, v_e_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_op_2292_; lean_object* v___x_2293_; lean_object* v_todo_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_op_2292_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2293_ = lean_unsigned_to_nat(8u);
v_todo_2294_ = lean_mk_empty_array_with_capacity(v___x_2293_);
v___x_2295_ = 1;
lean_inc_ref(v_todo_2294_);
v___x_2296_ = lean_array_push(v_todo_2294_, v_e_2286_);
v___x_2297_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2292_, v___x_2295_, v___x_2296_, v_todo_2294_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2305_, lean_object* v_m_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_tries_2312_; lean_object* v_roots_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2354_; 
v_tries_2312_ = lean_ctor_get(v_d_2305_, 0);
v_roots_2313_ = lean_ctor_get(v_d_2305_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_d_2305_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2315_ = v_d_2305_;
v_isShared_2316_ = v_isSharedCheck_2354_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_roots_2313_);
lean_inc(v_tries_2312_);
lean_dec(v_d_2305_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2354_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v_keyedConfig_2318_; uint8_t v_trackZetaDelta_2319_; lean_object* v_zetaDeltaSet_2320_; lean_object* v_lctx_2321_; lean_object* v_localInstances_2322_; lean_object* v_defEqCtx_x3f_2323_; lean_object* v_synthPendingDepth_2324_; lean_object* v_customCanUnfoldPredicate_x3f_2325_; uint8_t v_univApprox_2326_; uint8_t v_inTypeClassResolution_2327_; uint8_t v_cacheInferType_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2317_ = lean_st_mk_ref(v_tries_2312_);
v_keyedConfig_2318_ = lean_ctor_get(v_a_2307_, 0);
v_trackZetaDelta_2319_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*7);
v_zetaDeltaSet_2320_ = lean_ctor_get(v_a_2307_, 1);
v_lctx_2321_ = lean_ctor_get(v_a_2307_, 2);
v_localInstances_2322_ = lean_ctor_get(v_a_2307_, 3);
v_defEqCtx_x3f_2323_ = lean_ctor_get(v_a_2307_, 4);
v_synthPendingDepth_2324_ = lean_ctor_get(v_a_2307_, 5);
v_customCanUnfoldPredicate_x3f_2325_ = lean_ctor_get(v_a_2307_, 6);
v_univApprox_2326_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2327_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*7 + 2);
v_cacheInferType_2328_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*7 + 3);
v___x_2329_ = 2;
lean_inc_ref(v_keyedConfig_2318_);
v___x_2330_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2329_, v_keyedConfig_2318_);
lean_inc(v_customCanUnfoldPredicate_x3f_2325_);
lean_inc(v_synthPendingDepth_2324_);
lean_inc(v_defEqCtx_x3f_2323_);
lean_inc_ref(v_localInstances_2322_);
lean_inc_ref(v_lctx_2321_);
lean_inc(v_zetaDeltaSet_2320_);
v___x_2331_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v_zetaDeltaSet_2320_);
lean_ctor_set(v___x_2331_, 2, v_lctx_2321_);
lean_ctor_set(v___x_2331_, 3, v_localInstances_2322_);
lean_ctor_set(v___x_2331_, 4, v_defEqCtx_x3f_2323_);
lean_ctor_set(v___x_2331_, 5, v_synthPendingDepth_2324_);
lean_ctor_set(v___x_2331_, 6, v_customCanUnfoldPredicate_x3f_2325_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*7, v_trackZetaDelta_2319_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*7 + 1, v_univApprox_2326_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2327_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*7 + 3, v_cacheInferType_2328_);
lean_inc(v_a_2310_);
lean_inc_ref(v_a_2309_);
lean_inc(v_a_2308_);
lean_inc(v___x_2317_);
v___x_2332_ = lean_apply_6(v_m_2306_, v___x_2317_, v___x_2331_, v_a_2308_, v_a_2309_, v_a_2310_, lean_box(0));
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2345_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2337_ = lean_st_ref_get(v___x_2317_);
lean_dec(v___x_2317_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2337_);
v___x_2339_ = v___x_2315_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_roots_2313_);
v___x_2339_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_a_2333_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2340_);
v___x_2342_ = v___x_2335_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v___x_2317_);
lean_del_object(v___x_2315_);
lean_dec_ref(v_roots_2313_);
v_a_2346_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2332_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2332_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2355_, lean_object* v_m_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2355_, v_m_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2363_, lean_object* v_00_u03b2_2364_, lean_object* v_d_2365_, lean_object* v_m_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2365_, v_m_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2373_, lean_object* v_00_u03b2_2374_, lean_object* v_d_2375_, lean_object* v_m_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2373_, v_00_u03b2_2374_, v_d_2375_, v_m_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2383_, lean_object* v_v_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2387_ = lean_st_ref_take(v_a_2385_);
v___x_2388_ = lean_array_set(v___x_2387_, v_i_2383_, v_v_2384_);
v___x_2389_ = lean_st_ref_put(v_a_2385_, v___x_2388_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2392_, lean_object* v_v_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2392_, v_v_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec(v_i_2392_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2397_, lean_object* v_i_2398_, lean_object* v_v_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2398_, v_v_2399_, v_a_2400_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_i_2408_, lean_object* v_v_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2407_, v_i_2408_, v_v_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec(v_i_2408_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_sz_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_sz_2419_ = lean_array_get_size(v_a_2418_);
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2422_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2423_ = lean_unsigned_to_nat(1u);
v___x_2424_ = lean_mk_empty_array_with_capacity(v___x_2423_);
v___x_2425_ = lean_array_push(v___x_2424_, v_e_2417_);
v___x_2426_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2421_);
lean_ctor_set(v___x_2426_, 1, v___x_2420_);
lean_ctor_set(v___x_2426_, 2, v___x_2422_);
lean_ctor_set(v___x_2426_, 3, v___x_2425_);
v___x_2427_ = lean_array_push(v_a_2418_, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v_sz_2419_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2429_, lean_object* v_e_2430_){
_start:
{
lean_object* v_modifyGet_2431_; lean_object* v___f_2432_; lean_object* v___x_2433_; 
v_modifyGet_2431_ = lean_ctor_get(v_inst_2429_, 2);
lean_inc(v_modifyGet_2431_);
lean_dec_ref(v_inst_2429_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2432_, 0, v_e_2430_);
v___x_2433_ = lean_apply_2(v_modifyGet_2431_, lean_box(0), v___f_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2434_, lean_object* v_00_u03b1_2435_, lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_e_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2437_, v_e_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2440_, lean_object* v_00_u03b1_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_e_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2440_, v_00_u03b1_2441_, v_inst_2442_, v_inst_2443_, v_e_2444_);
lean_dec_ref(v_inst_2442_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2446_, lean_object* v_e_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2450_; lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2450_ = lean_st_ref_take(v_a_2448_);
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_array_get_size(v___x_2450_);
v___x_2458_ = lean_nat_dec_lt(v_i_2446_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_dec_ref(v_e_2447_);
v_fst_2452_ = v___x_2456_;
v_snd_2453_ = v___x_2450_;
goto v___jp_2451_;
}
else
{
lean_object* v_v_2459_; lean_object* v_xs_x27_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_v_2459_ = lean_array_fget(v___x_2450_, v_i_2446_);
v_xs_x27_2460_ = lean_array_fset(v___x_2450_, v_i_2446_, v___x_2456_);
v___x_2461_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2459_, v_e_2447_);
v___x_2462_ = lean_array_fset(v_xs_x27_2460_, v_i_2446_, v___x_2461_);
v_fst_2452_ = v___x_2456_;
v_snd_2453_ = v___x_2462_;
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_st_ref_put(v_a_2448_, v_snd_2453_);
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_fst_2452_);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2463_, lean_object* v_e_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2463_, v_e_2464_, v_a_2465_);
lean_dec(v_a_2465_);
lean_dec(v_i_2463_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2468_, lean_object* v_i_2469_, lean_object* v_e_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2469_, v_e_2470_, v_a_2471_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2478_, lean_object* v_i_2479_, lean_object* v_e_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2478_, v_i_2479_, v_e_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec(v_i_2479_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
lean_inc(v___y_2489_);
v___x_2495_ = lean_apply_6(v_x_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2504_, lean_object* v_localInsts_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___f_2513_; lean_object* v___x_2514_; 
lean_inc(v___y_2507_);
v___f_2513_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2513_, 0, v_x_2506_);
lean_closure_set(v___f_2513_, 1, v___y_2507_);
v___x_2514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2504_, v_localInsts_2505_, v___f_2513_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2514_) == 0)
{
return v___x_2514_;
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2523_, lean_object* v_localInsts_2524_, lean_object* v_x_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2523_, v_localInsts_2524_, v_x_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2533_, lean_object* v_00_u03b1_2534_, lean_object* v_lctx_2535_, lean_object* v_localInsts_2536_, lean_object* v_x_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2535_, v_localInsts_2536_, v_x_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03b1_2546_, lean_object* v_lctx_2547_, lean_object* v_localInsts_2548_, lean_object* v_x_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2545_, v_00_u03b1_2546_, v_lctx_2547_, v_localInsts_2548_, v_x_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v_sz_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2560_ = lean_st_ref_take(v___y_2558_);
v_sz_2561_ = lean_array_get_size(v___x_2560_);
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2564_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2565_ = lean_unsigned_to_nat(1u);
v___x_2566_ = lean_mk_empty_array_with_capacity(v___x_2565_);
v___x_2567_ = lean_array_push(v___x_2566_, v_e_2557_);
v___x_2568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2563_);
lean_ctor_set(v___x_2568_, 1, v___x_2562_);
lean_ctor_set(v___x_2568_, 2, v___x_2564_);
lean_ctor_set(v___x_2568_, 3, v___x_2567_);
v___x_2569_ = lean_array_push(v___x_2560_, v___x_2568_);
v___x_2570_ = lean_st_ref_put(v___y_2558_, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_sz_2561_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2572_, v___y_2573_);
lean_dec(v___y_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2576_, lean_object* v_e_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2577_, v___y_2578_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2585_, lean_object* v_e_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2585_, v_e_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2594_, lean_object* v_todo_2595_, lean_object* v_e_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2594_, v_todo_2595_, v_e_2596_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2604_, lean_object* v_todo_2605_, lean_object* v_e_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
uint8_t v___x_3410__boxed_2613_; lean_object* v_res_2614_; 
v___x_3410__boxed_2613_ = lean_unbox(v___x_2604_);
v_res_2614_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3410__boxed_2613_, v_todo_2605_, v_e_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2615_, lean_object* v_b_2616_, lean_object* v_x_2617_){
_start:
{
if (lean_obj_tag(v_x_2617_) == 0)
{
lean_dec(v_b_2616_);
lean_dec(v_a_2615_);
return v_x_2617_;
}
else
{
lean_object* v_key_2618_; lean_object* v_value_2619_; lean_object* v_tail_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2632_; 
v_key_2618_ = lean_ctor_get(v_x_2617_, 0);
v_value_2619_ = lean_ctor_get(v_x_2617_, 1);
v_tail_2620_ = lean_ctor_get(v_x_2617_, 2);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_x_2617_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2622_ = v_x_2617_;
v_isShared_2623_ = v_isSharedCheck_2632_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_tail_2620_);
lean_inc(v_value_2619_);
lean_inc(v_key_2618_);
lean_dec(v_x_2617_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2632_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
uint8_t v___x_2624_; 
v___x_2624_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2618_, v_a_2615_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2615_, v_b_2616_, v_tail_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 2, v___x_2625_);
v___x_2627_ = v___x_2622_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_key_2618_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_value_2619_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
else
{
lean_object* v___x_2630_; 
lean_dec(v_value_2619_);
lean_dec(v_key_2618_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 1, v_b_2616_);
lean_ctor_set(v___x_2622_, 0, v_a_2615_);
v___x_2630_ = v___x_2622_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2615_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_b_2616_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_tail_2620_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2633_, lean_object* v_x_2634_){
_start:
{
if (lean_obj_tag(v_x_2634_) == 0)
{
uint8_t v___x_2635_; 
v___x_2635_ = 0;
return v___x_2635_;
}
else
{
lean_object* v_key_2636_; lean_object* v_tail_2637_; uint8_t v___x_2638_; 
v_key_2636_ = lean_ctor_get(v_x_2634_, 0);
v_tail_2637_ = lean_ctor_get(v_x_2634_, 2);
v___x_2638_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2636_, v_a_2633_);
if (v___x_2638_ == 0)
{
v_x_2634_ = v_tail_2637_;
goto _start;
}
else
{
return v___x_2638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2640_, lean_object* v_x_2641_){
_start:
{
uint8_t v_res_2642_; lean_object* v_r_2643_; 
v_res_2642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2640_, v_x_2641_);
lean_dec(v_x_2641_);
lean_dec(v_a_2640_);
v_r_2643_ = lean_box(v_res_2642_);
return v_r_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2644_, lean_object* v_x_2645_){
_start:
{
if (lean_obj_tag(v_x_2645_) == 0)
{
return v_x_2644_;
}
else
{
lean_object* v_key_2646_; lean_object* v_value_2647_; lean_object* v_tail_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2671_; 
v_key_2646_ = lean_ctor_get(v_x_2645_, 0);
v_value_2647_ = lean_ctor_get(v_x_2645_, 1);
v_tail_2648_ = lean_ctor_get(v_x_2645_, 2);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_x_2645_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2650_ = v_x_2645_;
v_isShared_2651_ = v_isSharedCheck_2671_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_tail_2648_);
lean_inc(v_value_2647_);
lean_inc(v_key_2646_);
lean_dec(v_x_2645_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2671_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; uint64_t v___x_2653_; uint64_t v___x_2654_; uint64_t v___x_2655_; uint64_t v_fold_2656_; uint64_t v___x_2657_; uint64_t v___x_2658_; uint64_t v___x_2659_; size_t v___x_2660_; size_t v___x_2661_; size_t v___x_2662_; size_t v___x_2663_; size_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2652_ = lean_array_get_size(v_x_2644_);
v___x_2653_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2646_);
v___x_2654_ = 32ULL;
v___x_2655_ = lean_uint64_shift_right(v___x_2653_, v___x_2654_);
v_fold_2656_ = lean_uint64_xor(v___x_2653_, v___x_2655_);
v___x_2657_ = 16ULL;
v___x_2658_ = lean_uint64_shift_right(v_fold_2656_, v___x_2657_);
v___x_2659_ = lean_uint64_xor(v_fold_2656_, v___x_2658_);
v___x_2660_ = lean_uint64_to_usize(v___x_2659_);
v___x_2661_ = lean_usize_of_nat(v___x_2652_);
v___x_2662_ = ((size_t)1ULL);
v___x_2663_ = lean_usize_sub(v___x_2661_, v___x_2662_);
v___x_2664_ = lean_usize_land(v___x_2660_, v___x_2663_);
v___x_2665_ = lean_array_uget_borrowed(v_x_2644_, v___x_2664_);
lean_inc(v___x_2665_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 2, v___x_2665_);
v___x_2667_ = v___x_2650_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_key_2646_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_value_2647_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_array_uset(v_x_2644_, v___x_2664_, v___x_2667_);
v_x_2644_ = v___x_2668_;
v_x_2645_ = v_tail_2648_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2672_, lean_object* v_source_2673_, lean_object* v_target_2674_){
_start:
{
lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = lean_array_get_size(v_source_2673_);
v___x_2676_ = lean_nat_dec_lt(v_i_2672_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_dec_ref(v_source_2673_);
lean_dec(v_i_2672_);
return v_target_2674_;
}
else
{
lean_object* v_es_2677_; lean_object* v___x_2678_; lean_object* v_source_2679_; lean_object* v_target_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_es_2677_ = lean_array_fget(v_source_2673_, v_i_2672_);
v___x_2678_ = lean_box(0);
v_source_2679_ = lean_array_fset(v_source_2673_, v_i_2672_, v___x_2678_);
v_target_2680_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2674_, v_es_2677_);
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_2682_ = lean_nat_add(v_i_2672_, v___x_2681_);
lean_dec(v_i_2672_);
v_i_2672_ = v___x_2682_;
v_source_2673_ = v_source_2679_;
v_target_2674_ = v_target_2680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2684_){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v_nbuckets_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2685_ = lean_array_get_size(v_data_2684_);
v___x_2686_ = lean_unsigned_to_nat(2u);
v_nbuckets_2687_ = lean_nat_mul(v___x_2685_, v___x_2686_);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_mk_array(v_nbuckets_2687_, v___x_2689_);
v___x_2691_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2688_, v_data_2684_, v___x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2692_, lean_object* v_a_2693_, lean_object* v_b_2694_){
_start:
{
lean_object* v_size_2695_; lean_object* v_buckets_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2739_; 
v_size_2695_ = lean_ctor_get(v_m_2692_, 0);
v_buckets_2696_ = lean_ctor_get(v_m_2692_, 1);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_m_2692_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2698_ = v_m_2692_;
v_isShared_2699_ = v_isSharedCheck_2739_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_buckets_2696_);
lean_inc(v_size_2695_);
lean_dec(v_m_2692_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2739_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; uint64_t v___x_2701_; uint64_t v___x_2702_; uint64_t v___x_2703_; uint64_t v_fold_2704_; uint64_t v___x_2705_; uint64_t v___x_2706_; uint64_t v___x_2707_; size_t v___x_2708_; size_t v___x_2709_; size_t v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; lean_object* v_bkt_2713_; uint8_t v___x_2714_; 
v___x_2700_ = lean_array_get_size(v_buckets_2696_);
v___x_2701_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2693_);
v___x_2702_ = 32ULL;
v___x_2703_ = lean_uint64_shift_right(v___x_2701_, v___x_2702_);
v_fold_2704_ = lean_uint64_xor(v___x_2701_, v___x_2703_);
v___x_2705_ = 16ULL;
v___x_2706_ = lean_uint64_shift_right(v_fold_2704_, v___x_2705_);
v___x_2707_ = lean_uint64_xor(v_fold_2704_, v___x_2706_);
v___x_2708_ = lean_uint64_to_usize(v___x_2707_);
v___x_2709_ = lean_usize_of_nat(v___x_2700_);
v___x_2710_ = ((size_t)1ULL);
v___x_2711_ = lean_usize_sub(v___x_2709_, v___x_2710_);
v___x_2712_ = lean_usize_land(v___x_2708_, v___x_2711_);
v_bkt_2713_ = lean_array_uget_borrowed(v_buckets_2696_, v___x_2712_);
v___x_2714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2693_, v_bkt_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v_size_x27_2716_; lean_object* v___x_2717_; lean_object* v_buckets_x27_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2715_ = lean_unsigned_to_nat(1u);
v_size_x27_2716_ = lean_nat_add(v_size_2695_, v___x_2715_);
lean_dec(v_size_2695_);
lean_inc(v_bkt_2713_);
v___x_2717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2717_, 0, v_a_2693_);
lean_ctor_set(v___x_2717_, 1, v_b_2694_);
lean_ctor_set(v___x_2717_, 2, v_bkt_2713_);
v_buckets_x27_2718_ = lean_array_uset(v_buckets_2696_, v___x_2712_, v___x_2717_);
v___x_2719_ = lean_unsigned_to_nat(4u);
v___x_2720_ = lean_nat_mul(v_size_x27_2716_, v___x_2719_);
v___x_2721_ = lean_unsigned_to_nat(3u);
v___x_2722_ = lean_nat_div(v___x_2720_, v___x_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_array_get_size(v_buckets_x27_2718_);
v___x_2724_ = lean_nat_dec_le(v___x_2722_, v___x_2723_);
lean_dec(v___x_2722_);
if (v___x_2724_ == 0)
{
lean_object* v_val_2725_; lean_object* v___x_2727_; 
v_val_2725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2718_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v_val_2725_);
lean_ctor_set(v___x_2698_, 0, v_size_x27_2716_);
v___x_2727_ = v___x_2698_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_size_x27_2716_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_val_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
else
{
lean_object* v___x_2730_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v_buckets_x27_2718_);
lean_ctor_set(v___x_2698_, 0, v_size_x27_2716_);
v___x_2730_ = v___x_2698_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_size_x27_2716_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_buckets_x27_2718_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
else
{
lean_object* v___x_2732_; lean_object* v_buckets_x27_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_inc(v_bkt_2713_);
v___x_2732_ = lean_box(0);
v_buckets_x27_2733_ = lean_array_uset(v_buckets_2696_, v___x_2712_, v___x_2732_);
v___x_2734_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2693_, v_b_2694_, v_bkt_2713_);
v___x_2735_ = lean_array_uset(v_buckets_x27_2733_, v___x_2712_, v___x_2734_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v___x_2735_);
v___x_2737_ = v___x_2698_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_size_2695_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2740_, lean_object* v_x_2741_){
_start:
{
if (lean_obj_tag(v_x_2741_) == 0)
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_box(0);
return v___x_2742_;
}
else
{
lean_object* v_key_2743_; lean_object* v_value_2744_; lean_object* v_tail_2745_; uint8_t v___x_2746_; 
v_key_2743_ = lean_ctor_get(v_x_2741_, 0);
v_value_2744_ = lean_ctor_get(v_x_2741_, 1);
v_tail_2745_ = lean_ctor_get(v_x_2741_, 2);
v___x_2746_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2743_, v_a_2740_);
if (v___x_2746_ == 0)
{
v_x_2741_ = v_tail_2745_;
goto _start;
}
else
{
lean_object* v___x_2748_; 
lean_inc(v_value_2744_);
v___x_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2748_, 0, v_value_2744_);
return v___x_2748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2749_, lean_object* v_x_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2749_, v_x_2750_);
lean_dec(v_x_2750_);
lean_dec(v_a_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_buckets_2754_; lean_object* v___x_2755_; uint64_t v___x_2756_; uint64_t v___x_2757_; uint64_t v___x_2758_; uint64_t v_fold_2759_; uint64_t v___x_2760_; uint64_t v___x_2761_; uint64_t v___x_2762_; size_t v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_buckets_2754_ = lean_ctor_get(v_m_2752_, 1);
v___x_2755_ = lean_array_get_size(v_buckets_2754_);
v___x_2756_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2753_);
v___x_2757_ = 32ULL;
v___x_2758_ = lean_uint64_shift_right(v___x_2756_, v___x_2757_);
v_fold_2759_ = lean_uint64_xor(v___x_2756_, v___x_2758_);
v___x_2760_ = 16ULL;
v___x_2761_ = lean_uint64_shift_right(v_fold_2759_, v___x_2760_);
v___x_2762_ = lean_uint64_xor(v_fold_2759_, v___x_2761_);
v___x_2763_ = lean_uint64_to_usize(v___x_2762_);
v___x_2764_ = lean_usize_of_nat(v___x_2755_);
v___x_2765_ = ((size_t)1ULL);
v___x_2766_ = lean_usize_sub(v___x_2764_, v___x_2765_);
v___x_2767_ = lean_usize_land(v___x_2763_, v___x_2766_);
v___x_2768_ = lean_array_uget_borrowed(v_buckets_2754_, v___x_2767_);
v___x_2769_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2753_, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_m_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2773_, lean_object* v_entry_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_snd_2781_; lean_object* v_snd_2782_; lean_object* v_fst_2783_; lean_object* v_fst_2784_; lean_object* v_snd_2785_; lean_object* v_fst_2786_; lean_object* v_fst_2787_; lean_object* v_snd_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_snd_2781_ = lean_ctor_get(v_p_2773_, 1);
v_snd_2782_ = lean_ctor_get(v_entry_2774_, 1);
lean_inc(v_snd_2782_);
v_fst_2783_ = lean_ctor_get(v_p_2773_, 0);
v_fst_2784_ = lean_ctor_get(v_snd_2781_, 0);
v_snd_2785_ = lean_ctor_get(v_snd_2781_, 1);
v_fst_2786_ = lean_ctor_get(v_entry_2774_, 0);
lean_inc(v_fst_2786_);
lean_dec_ref(v_entry_2774_);
v_fst_2787_ = lean_ctor_get(v_snd_2782_, 0);
lean_inc(v_fst_2787_);
v_snd_2788_ = lean_ctor_get(v_snd_2782_, 1);
v___x_2789_ = lean_array_get_size(v_fst_2786_);
v___x_2790_ = lean_unsigned_to_nat(0u);
v___x_2791_ = lean_nat_dec_eq(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v_fst_2792_; lean_object* v_snd_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2898_; 
v_fst_2792_ = lean_ctor_get(v_fst_2787_, 0);
v_snd_2793_ = lean_ctor_get(v_fst_2787_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_fst_2787_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2795_ = v_fst_2787_;
v_isShared_2796_ = v_isSharedCheck_2898_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_snd_2793_);
lean_inc(v_fst_2792_);
lean_dec(v_fst_2787_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2898_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v_e_2800_; lean_object* v_todo_2801_; lean_object* v___x_2802_; lean_object* v___f_2803_; lean_object* v___x_2804_; 
v___x_2797_ = l_Lean_instInhabitedExpr;
v___x_2798_ = lean_unsigned_to_nat(1u);
v___x_2799_ = lean_nat_sub(v___x_2789_, v___x_2798_);
v_e_2800_ = lean_array_get(v___x_2797_, v_fst_2786_, v___x_2799_);
lean_dec(v___x_2799_);
v_todo_2801_ = lean_array_pop(v_fst_2786_);
v___x_2802_ = lean_box(v___x_2791_);
v___f_2803_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2803_, 0, v___x_2802_);
lean_closure_set(v___f_2803_, 1, v_todo_2801_);
lean_closure_set(v___f_2803_, 2, v_e_2800_);
v___x_2804_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2792_, v_snd_2793_, v___f_2803_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v_fst_2806_; lean_object* v_snd_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2889_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v_fst_2806_ = lean_ctor_get(v_a_2805_, 0);
v_snd_2807_ = lean_ctor_get(v_a_2805_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_a_2805_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2809_ = v_a_2805_;
v_isShared_2810_ = v_isSharedCheck_2889_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_snd_2807_);
lean_inc(v_fst_2806_);
lean_dec(v_a_2805_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2889_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = lean_box(3);
v___x_2812_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2806_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2785_, v_fst_2806_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v___x_2815_; 
lean_inc(v_snd_2785_);
lean_inc(v_fst_2784_);
lean_inc(v_fst_2783_);
lean_dec_ref(v_p_2773_);
lean_inc(v_snd_2782_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_snd_2782_);
lean_ctor_set(v___x_2809_, 0, v_snd_2807_);
v___x_2815_ = v___x_2809_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_snd_2807_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_snd_2782_);
v___x_2815_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2835_; 
v_isSharedCheck_2835_ = !lean_is_exclusive(v_snd_2782_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; lean_object* v_unused_2837_; 
v_unused_2836_ = lean_ctor_get(v_snd_2782_, 1);
lean_dec(v_unused_2836_);
v_unused_2837_ = lean_ctor_get(v_snd_2782_, 0);
lean_dec(v_unused_2837_);
v___x_2817_ = v_snd_2782_;
v_isShared_2818_ = v_isSharedCheck_2835_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v_snd_2782_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2835_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2834_; 
v___x_2819_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2815_, v_a_2775_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2834_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2834_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2785_, v_fst_2806_, v_a_2820_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v___x_2824_);
lean_ctor_set(v___x_2795_, 0, v_fst_2784_);
v___x_2826_ = v___x_2795_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_fst_2784_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___x_2826_);
lean_ctor_set(v___x_2817_, 0, v_fst_2783_);
v___x_2828_ = v___x_2817_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_fst_2783_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2828_);
v___x_2830_ = v___x_2822_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2839_; lean_object* v___x_2841_; 
lean_dec(v_fst_2806_);
lean_del_object(v___x_2795_);
v_val_2839_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_val_2839_);
lean_dec_ref_known(v___x_2813_, 1);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_snd_2782_);
lean_ctor_set(v___x_2809_, 0, v_snd_2807_);
v___x_2841_ = v___x_2809_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_snd_2807_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_snd_2782_);
v___x_2841_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v___x_2842_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2839_, v___x_2841_, v_a_2775_);
lean_dec(v_val_2839_);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2842_, 0);
lean_dec(v_unused_2850_);
v___x_2844_ = v___x_2842_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v___x_2842_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_p_2773_);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_p_2773_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
else
{
uint8_t v___x_2852_; 
lean_dec(v_fst_2806_);
v___x_2852_ = lean_nat_dec_eq(v_fst_2784_, v___x_2790_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2854_; 
lean_del_object(v___x_2795_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_snd_2782_);
lean_ctor_set(v___x_2809_, 0, v_snd_2807_);
v___x_2854_ = v___x_2809_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_snd_2807_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_snd_2782_);
v___x_2854_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
v___x_2855_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2784_, v___x_2854_, v_a_2775_);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v___x_2855_, 0);
lean_dec(v_unused_2863_);
v___x_2857_ = v___x_2855_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v___x_2855_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v_p_2773_);
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_p_2773_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v___x_2866_; 
lean_inc(v_snd_2785_);
lean_inc(v_fst_2783_);
lean_dec_ref(v_p_2773_);
lean_inc(v_snd_2782_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_snd_2782_);
lean_ctor_set(v___x_2809_, 0, v_snd_2807_);
v___x_2866_ = v___x_2809_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_snd_2807_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_snd_2782_);
v___x_2866_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2885_; 
v_isSharedCheck_2885_ = !lean_is_exclusive(v_snd_2782_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; lean_object* v_unused_2887_; 
v_unused_2886_ = lean_ctor_get(v_snd_2782_, 1);
lean_dec(v_unused_2886_);
v_unused_2887_ = lean_ctor_get(v_snd_2782_, 0);
lean_dec(v_unused_2887_);
v___x_2868_ = v_snd_2782_;
v_isShared_2869_ = v_isSharedCheck_2885_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v_snd_2782_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2885_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2884_; 
v___x_2870_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2866_, v_a_2775_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2884_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2884_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 1, v_snd_2785_);
lean_ctor_set(v___x_2795_, 0, v_a_2871_);
v___x_2876_ = v___x_2795_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2871_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_snd_2785_);
v___x_2876_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2878_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v___x_2876_);
lean_ctor_set(v___x_2868_, 0, v_fst_2783_);
v___x_2878_ = v___x_2868_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_fst_2783_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2878_);
v___x_2880_ = v___x_2873_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
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
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_del_object(v___x_2795_);
lean_dec(v_snd_2782_);
lean_dec_ref(v_p_2773_);
v_a_2890_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2804_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2804_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
else
{
lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2907_; 
lean_inc(v_snd_2788_);
lean_inc(v_fst_2783_);
lean_inc(v_snd_2781_);
lean_dec(v_fst_2787_);
lean_dec(v_fst_2786_);
lean_dec_ref(v_p_2773_);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_snd_2782_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; lean_object* v_unused_2909_; 
v_unused_2908_ = lean_ctor_get(v_snd_2782_, 1);
lean_dec(v_unused_2908_);
v_unused_2909_ = lean_ctor_get(v_snd_2782_, 0);
lean_dec(v_unused_2909_);
v___x_2900_ = v_snd_2782_;
v_isShared_2901_ = v_isSharedCheck_2907_;
goto v_resetjp_2899_;
}
else
{
lean_dec(v_snd_2782_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2907_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v_values_2902_; lean_object* v___x_2904_; 
v_values_2902_ = lean_array_push(v_fst_2783_, v_snd_2788_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 1, v_snd_2781_);
lean_ctor_set(v___x_2900_, 0, v_values_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_values_2902_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_snd_2781_);
v___x_2904_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2910_, lean_object* v_entry_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2910_, v_entry_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2919_, lean_object* v_p_2920_, lean_object* v_entry_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2920_, v_entry_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2929_, lean_object* v_p_2930_, lean_object* v_entry_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2929_, v_p_2930_, v_entry_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2939_, lean_object* v_m_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2940_, v_a_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2943_, lean_object* v_m_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2943_, v_m_2944_, v_a_2945_);
lean_dec(v_a_2945_);
lean_dec_ref(v_m_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2947_, lean_object* v_m_2948_, lean_object* v_a_2949_, lean_object* v_b_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2948_, v_a_2949_, v_b_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2952_, lean_object* v_a_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2953_, v_x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2956_, lean_object* v_a_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2956_, v_a_2957_, v_x_2958_);
lean_dec(v_x_2958_);
lean_dec(v_a_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2960_, lean_object* v_a_2961_, lean_object* v_x_2962_){
_start:
{
uint8_t v___x_2963_; 
v___x_2963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2961_, v_x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2964_, lean_object* v_a_2965_, lean_object* v_x_2966_){
_start:
{
uint8_t v_res_2967_; lean_object* v_r_2968_; 
v_res_2967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2964_, v_a_2965_, v_x_2966_);
lean_dec(v_x_2966_);
lean_dec(v_a_2965_);
v_r_2968_ = lean_box(v_res_2967_);
return v_r_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2969_, lean_object* v_data_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_2972_, lean_object* v_a_2973_, lean_object* v_b_2974_, lean_object* v_x_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2973_, v_b_2974_, v_x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2977_, lean_object* v_i_2978_, lean_object* v_source_2979_, lean_object* v_target_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_2978_, v_source_2979_, v_target_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_2983_, v_x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_2986_, size_t v_i_2987_, size_t v_stop_2988_, lean_object* v_b_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_usize_dec_eq(v_i_2987_, v_stop_2988_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_array_uget_borrowed(v_as_2986_, v_i_2987_);
lean_inc(v___x_2997_);
v___x_2998_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_2989_, v___x_2997_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; size_t v___x_3000_; size_t v___x_3001_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = ((size_t)1ULL);
v___x_3001_ = lean_usize_add(v_i_2987_, v___x_3000_);
v_i_2987_ = v___x_3001_;
v_b_2989_ = v_a_2999_;
goto _start;
}
else
{
return v___x_2998_;
}
}
else
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_b_2989_);
return v___x_3003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3004_, lean_object* v_i_3005_, lean_object* v_stop_3006_, lean_object* v_b_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
size_t v_i_boxed_3014_; size_t v_stop_boxed_3015_; lean_object* v_res_3016_; 
v_i_boxed_3014_ = lean_unbox_usize(v_i_3005_);
lean_dec(v_i_3005_);
v_stop_boxed_3015_ = lean_unbox_usize(v_stop_3006_);
lean_dec(v_stop_3006_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3004_, v_i_boxed_3014_, v_stop_boxed_3015_, v_b_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v_as_3004_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3017_, lean_object* v_starIdx_3018_, lean_object* v_children_3019_, lean_object* v_entries_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_starIdx_3018_);
lean_ctor_set(v___x_3027_, 1, v_children_3019_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v_values_3017_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_array_get_size(v_entries_3020_);
v___x_3031_ = lean_nat_dec_lt(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
v___x_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3028_);
return v___x_3032_;
}
else
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_nat_dec_le(v___x_3030_, v___x_3030_);
if (v___x_3033_ == 0)
{
if (v___x_3031_ == 0)
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3028_);
return v___x_3034_;
}
else
{
size_t v___x_3035_; size_t v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = lean_usize_of_nat(v___x_3030_);
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3020_, v___x_3035_, v___x_3036_, v___x_3028_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
return v___x_3037_;
}
}
else
{
size_t v___x_3038_; size_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = ((size_t)0ULL);
v___x_3039_ = lean_usize_of_nat(v___x_3030_);
v___x_3040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3020_, v___x_3038_, v___x_3039_, v___x_3028_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
return v___x_3040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3041_, lean_object* v_starIdx_3042_, lean_object* v_children_3043_, lean_object* v_entries_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3041_, v_starIdx_3042_, v_children_3043_, v_entries_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_entries_3044_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3052_, lean_object* v_values_3053_, lean_object* v_starIdx_3054_, lean_object* v_children_3055_, lean_object* v_entries_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3053_, v_starIdx_3054_, v_children_3055_, v_entries_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3064_, lean_object* v_values_3065_, lean_object* v_starIdx_3066_, lean_object* v_children_3067_, lean_object* v_entries_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3064_, v_values_3065_, v_starIdx_3066_, v_children_3067_, v_entries_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_entries_3068_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3076_, lean_object* v_as_3077_, size_t v_i_3078_, size_t v_stop_3079_, lean_object* v_b_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3077_, v_i_3078_, v_stop_3079_, v_b_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3088_, lean_object* v_as_3089_, lean_object* v_i_3090_, lean_object* v_stop_3091_, lean_object* v_b_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
size_t v_i_boxed_3099_; size_t v_stop_boxed_3100_; lean_object* v_res_3101_; 
v_i_boxed_3099_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_stop_boxed_3100_ = lean_unbox_usize(v_stop_3091_);
lean_dec(v_stop_3091_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3088_, v_as_3089_, v_i_boxed_3099_, v_stop_boxed_3100_, v_b_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v_as_3089_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v_values_3112_; lean_object* v_star_3113_; lean_object* v_children_3114_; lean_object* v_pending_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3145_; 
v___x_3109_ = lean_st_ref_get(v_a_3103_);
v___x_3110_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3111_ = lean_array_get(v___x_3110_, v___x_3109_, v_c_3102_);
lean_dec(v___x_3109_);
v_values_3112_ = lean_ctor_get(v___x_3111_, 0);
v_star_3113_ = lean_ctor_get(v___x_3111_, 1);
v_children_3114_ = lean_ctor_get(v___x_3111_, 2);
v_pending_3115_ = lean_ctor_get(v___x_3111_, 3);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3117_ = v___x_3111_;
v_isShared_3118_ = v_isSharedCheck_3145_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_pending_3115_);
lean_inc(v_children_3114_);
lean_inc(v_star_3113_);
lean_inc(v_values_3112_);
lean_dec(v___x_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3145_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = lean_array_get_size(v_pending_3115_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = lean_nat_dec_eq(v___x_3119_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3102_, v___x_3110_, v_a_3103_);
lean_dec_ref(v___x_3122_);
v___x_3123_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3112_, v_star_3113_, v_children_3114_, v_pending_3115_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec_ref(v_pending_3115_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v_snd_3125_; lean_object* v_fst_3126_; lean_object* v_fst_3127_; lean_object* v_snd_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v_snd_3125_ = lean_ctor_get(v_a_3124_, 1);
v_fst_3126_ = lean_ctor_get(v_a_3124_, 0);
v_fst_3127_ = lean_ctor_get(v_snd_3125_, 0);
v_snd_3128_ = lean_ctor_get(v_snd_3125_, 1);
v___x_3129_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
lean_inc(v_snd_3128_);
lean_inc(v_fst_3127_);
lean_inc(v_fst_3126_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 3, v___x_3129_);
lean_ctor_set(v___x_3117_, 2, v_snd_3128_);
lean_ctor_set(v___x_3117_, 1, v_fst_3127_);
lean_ctor_set(v___x_3117_, 0, v_fst_3126_);
v___x_3131_ = v___x_3117_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_fst_3126_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_fst_3127_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_snd_3128_);
lean_ctor_set(v_reuseFailAlloc_3141_, 3, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
v___x_3132_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3102_, v___x_3131_, v_a_3103_);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v___x_3132_, 0);
lean_dec(v_unused_3140_);
v___x_3134_ = v___x_3132_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_dec(v___x_3132_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v_a_3124_);
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3124_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_del_object(v___x_3117_);
return v___x_3123_;
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_del_object(v___x_3117_);
lean_dec_ref(v_pending_3115_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_star_3113_);
lean_ctor_set(v___x_3142_, 1, v_children_3114_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_values_3112_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
return v___x_3144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec(v_c_3146_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3154_, lean_object* v_c_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3163_, lean_object* v_c_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3163_, v_c_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec(v_c_3164_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3172_, lean_object* v_fallback_3173_, lean_object* v_x_3174_){
_start:
{
if (lean_obj_tag(v_x_3174_) == 0)
{
lean_inc(v_fallback_3173_);
return v_fallback_3173_;
}
else
{
lean_object* v_key_3175_; lean_object* v_value_3176_; lean_object* v_tail_3177_; uint8_t v___x_3178_; 
v_key_3175_ = lean_ctor_get(v_x_3174_, 0);
v_value_3176_ = lean_ctor_get(v_x_3174_, 1);
v_tail_3177_ = lean_ctor_get(v_x_3174_, 2);
v___x_3178_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3175_, v_a_3172_);
if (v___x_3178_ == 0)
{
v_x_3174_ = v_tail_3177_;
goto _start;
}
else
{
lean_inc(v_value_3176_);
return v_value_3176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3180_, lean_object* v_fallback_3181_, lean_object* v_x_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3180_, v_fallback_3181_, v_x_3182_);
lean_dec(v_x_3182_);
lean_dec(v_fallback_3181_);
lean_dec(v_a_3180_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3184_, lean_object* v_a_3185_, lean_object* v_fallback_3186_){
_start:
{
lean_object* v_buckets_3187_; lean_object* v___x_3188_; uint64_t v___x_3189_; uint64_t v___x_3190_; uint64_t v___x_3191_; uint64_t v_fold_3192_; uint64_t v___x_3193_; uint64_t v___x_3194_; uint64_t v___x_3195_; size_t v___x_3196_; size_t v___x_3197_; size_t v___x_3198_; size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_buckets_3187_ = lean_ctor_get(v_m_3184_, 1);
v___x_3188_ = lean_array_get_size(v_buckets_3187_);
v___x_3189_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3185_);
v___x_3190_ = 32ULL;
v___x_3191_ = lean_uint64_shift_right(v___x_3189_, v___x_3190_);
v_fold_3192_ = lean_uint64_xor(v___x_3189_, v___x_3191_);
v___x_3193_ = 16ULL;
v___x_3194_ = lean_uint64_shift_right(v_fold_3192_, v___x_3193_);
v___x_3195_ = lean_uint64_xor(v_fold_3192_, v___x_3194_);
v___x_3196_ = lean_uint64_to_usize(v___x_3195_);
v___x_3197_ = lean_usize_of_nat(v___x_3188_);
v___x_3198_ = ((size_t)1ULL);
v___x_3199_ = lean_usize_sub(v___x_3197_, v___x_3198_);
v___x_3200_ = lean_usize_land(v___x_3196_, v___x_3199_);
v___x_3201_ = lean_array_uget_borrowed(v_buckets_3187_, v___x_3200_);
v___x_3202_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3185_, v_fallback_3186_, v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3203_, lean_object* v_a_3204_, lean_object* v_fallback_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3203_, v_a_3204_, v_fallback_3205_);
lean_dec(v_fallback_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_m_3203_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3207_, lean_object* v_rest_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = lean_nat_dec_eq(v_next_3207_, v___x_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3207_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3243_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3243_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3243_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v_snd_3222_; 
v_snd_3222_ = lean_ctor_get(v_a_3218_, 1);
lean_inc(v_snd_3222_);
lean_dec(v_a_3218_);
if (lean_obj_tag(v_rest_3208_) == 0)
{
lean_object* v_fst_3223_; lean_object* v_snd_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v_fst_3223_ = lean_ctor_get(v_snd_3222_, 0);
lean_inc(v_fst_3223_);
v_snd_3224_ = lean_ctor_get(v_snd_3222_, 1);
lean_inc(v_snd_3224_);
lean_dec(v_snd_3222_);
v___x_3225_ = lean_st_ref_take(v_a_3209_);
v___x_3226_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
lean_ctor_set(v___x_3227_, 1, v_fst_3223_);
lean_ctor_set(v___x_3227_, 2, v_snd_3224_);
lean_ctor_set(v___x_3227_, 3, v___x_3226_);
v___x_3228_ = lean_array_set(v___x_3225_, v_next_3207_, v___x_3227_);
lean_dec(v_next_3207_);
v___x_3229_ = lean_st_ref_put(v_a_3209_, v___x_3228_);
v___x_3230_ = lean_box(0);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3230_);
v___x_3232_ = v___x_3220_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
else
{
lean_object* v_fst_3234_; lean_object* v_snd_3235_; lean_object* v_head_3236_; lean_object* v_tail_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
lean_del_object(v___x_3220_);
lean_dec(v_next_3207_);
v_fst_3234_ = lean_ctor_get(v_snd_3222_, 0);
lean_inc(v_fst_3234_);
v_snd_3235_ = lean_ctor_get(v_snd_3222_, 1);
lean_inc(v_snd_3235_);
lean_dec(v_snd_3222_);
v_head_3236_ = lean_ctor_get(v_rest_3208_, 0);
v_tail_3237_ = lean_ctor_get(v_rest_3208_, 1);
v___x_3238_ = lean_box(3);
v___x_3239_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3236_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
lean_dec(v_fst_3234_);
v___x_3240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3235_, v_head_3236_, v___x_3215_);
lean_dec(v_snd_3235_);
v_next_3207_ = v___x_3240_;
v_rest_3208_ = v_tail_3237_;
goto _start;
}
else
{
lean_dec(v_snd_3235_);
v_next_3207_ = v_fst_3234_;
v_rest_3208_ = v_tail_3237_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_next_3207_);
v_a_3244_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3217_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3217_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v_next_3207_);
v___x_3252_ = lean_box(0);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3254_, lean_object* v_rest_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3254_, v_rest_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec(v_rest_3255_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3263_, lean_object* v_next_3264_, lean_object* v_rest_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3264_, v_rest_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3273_, lean_object* v_next_3274_, lean_object* v_rest_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3273_, v_next_3274_, v_rest_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec(v_rest_3275_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3283_, lean_object* v_m_3284_, lean_object* v_a_3285_, lean_object* v_fallback_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3284_, v_a_3285_, v_fallback_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3288_, lean_object* v_m_3289_, lean_object* v_a_3290_, lean_object* v_fallback_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3288_, v_m_3289_, v_a_3290_, v_fallback_3291_);
lean_dec(v_fallback_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_m_3289_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3293_, lean_object* v_a_3294_, lean_object* v_fallback_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3294_, v_fallback_3295_, v_x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3298_, lean_object* v_a_3299_, lean_object* v_fallback_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3298_, v_a_3299_, v_fallback_3300_, v_x_3301_);
lean_dec(v_x_3301_);
lean_dec(v_fallback_3300_);
lean_dec(v_a_3299_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3303_, lean_object* v_path_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
if (lean_obj_tag(v_path_3304_) == 0)
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v_t_3303_);
return v___x_3310_;
}
else
{
lean_object* v_head_3311_; lean_object* v_tail_3312_; lean_object* v_roots_3313_; lean_object* v___x_3314_; lean_object* v_idx_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_head_3311_ = lean_ctor_get(v_path_3304_, 0);
lean_inc(v_head_3311_);
v_tail_3312_ = lean_ctor_get(v_path_3304_, 1);
lean_inc(v_tail_3312_);
lean_dec_ref_known(v_path_3304_, 2);
v_roots_3313_ = lean_ctor_get(v_t_3303_, 1);
v___x_3314_ = lean_unsigned_to_nat(0u);
v_idx_3315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3313_, v_head_3311_, v___x_3314_);
lean_dec(v_head_3311_);
v___x_3316_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3316_, 0, lean_box(0));
lean_closure_set(v___x_3316_, 1, v_idx_3315_);
lean_closure_set(v___x_3316_, 2, v_tail_3312_);
v___x_3317_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3303_, v___x_3316_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3326_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v_snd_3322_; lean_object* v___x_3324_; 
v_snd_3322_ = lean_ctor_get(v_a_3318_, 1);
lean_inc(v_snd_3322_);
lean_dec(v_a_3318_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_snd_3322_);
v___x_3324_ = v___x_3320_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_snd_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
v_a_3327_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3317_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3317_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3335_, lean_object* v_path_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3335_, v_path_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3343_, lean_object* v_t_3344_, lean_object* v_path_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3344_, v_path_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3352_, lean_object* v_t_3353_, lean_object* v_path_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3352_, v_t_3353_, v_path_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3363_, lean_object* v_e_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3366_ = lean_array_get_size(v_a_3365_);
v___x_3367_ = lean_nat_dec_lt(v___x_3366_, v_score_3363_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3368_ = lean_unsigned_to_nat(1u);
v___x_3369_ = lean_mk_empty_array_with_capacity(v___x_3368_);
v___x_3370_ = lean_array_push(v___x_3369_, v_e_3364_);
v___x_3371_ = lean_array_push(v_a_3365_, v___x_3370_);
return v___x_3371_;
}
else
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3373_ = lean_array_push(v_a_3365_, v___x_3372_);
v_a_3365_ = v___x_3373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3375_, lean_object* v_e_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3375_, v_e_3376_, v_a_3377_);
lean_dec(v_score_3375_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3379_, lean_object* v_score_3380_, lean_object* v_e_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3380_, v_e_3381_, v_a_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3384_, lean_object* v_score_3385_, lean_object* v_e_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3384_, v_score_3385_, v_e_3386_, v_a_3387_);
lean_dec(v_score_3385_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3389_, lean_object* v_score_3390_, lean_object* v_e_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = lean_array_get_size(v_e_3391_);
v___x_3393_ = lean_unsigned_to_nat(0u);
v___x_3394_ = lean_nat_dec_eq(v___x_3392_, v___x_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_array_get_size(v_r_3389_);
v___x_3396_ = lean_nat_dec_lt(v_score_3390_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3390_, v_e_3391_, v_r_3389_);
return v___x_3397_;
}
else
{
if (v___x_3396_ == 0)
{
lean_dec_ref(v_e_3391_);
return v_r_3389_;
}
else
{
lean_object* v_v_3398_; lean_object* v___x_3399_; lean_object* v_xs_x27_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_v_3398_ = lean_array_fget(v_r_3389_, v_score_3390_);
v___x_3399_ = lean_box(0);
v_xs_x27_3400_ = lean_array_fset(v_r_3389_, v_score_3390_, v___x_3399_);
v___x_3401_ = lean_array_push(v_v_3398_, v_e_3391_);
v___x_3402_ = lean_array_fset(v_xs_x27_3400_, v_score_3390_, v___x_3401_);
return v___x_3402_;
}
}
}
else
{
lean_dec_ref(v_e_3391_);
return v_r_3389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3403_, lean_object* v_score_3404_, lean_object* v_e_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3403_, v_score_3404_, v_e_3405_);
lean_dec(v_score_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3407_, lean_object* v_r_3408_, lean_object* v_score_3409_, lean_object* v_e_3410_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3408_, v_score_3409_, v_e_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3412_, lean_object* v_r_3413_, lean_object* v_score_3414_, lean_object* v_e_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3412_, v_r_3413_, v_score_3414_, v_e_3415_);
lean_dec(v_score_3414_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3417_, size_t v_i_3418_, size_t v_stop_3419_, lean_object* v_b_3420_){
_start:
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_usize_dec_eq(v_i_3418_, v_stop_3419_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; size_t v___x_3425_; size_t v___x_3426_; 
v___x_3422_ = lean_array_uget_borrowed(v_as_3417_, v_i_3418_);
v___x_3423_ = lean_array_get_size(v___x_3422_);
v___x_3424_ = lean_nat_add(v_b_3420_, v___x_3423_);
lean_dec(v_b_3420_);
v___x_3425_ = ((size_t)1ULL);
v___x_3426_ = lean_usize_add(v_i_3418_, v___x_3425_);
v_i_3418_ = v___x_3426_;
v_b_3420_ = v___x_3424_;
goto _start;
}
else
{
return v_b_3420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3428_, lean_object* v_i_3429_, lean_object* v_stop_3430_, lean_object* v_b_3431_){
_start:
{
size_t v_i_boxed_3432_; size_t v_stop_boxed_3433_; lean_object* v_res_3434_; 
v_i_boxed_3432_ = lean_unbox_usize(v_i_3429_);
lean_dec(v_i_3429_);
v_stop_boxed_3433_ = lean_unbox_usize(v_stop_3430_);
lean_dec(v_stop_3430_);
v_res_3434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3428_, v_i_boxed_3432_, v_stop_boxed_3433_, v_b_3431_);
lean_dec_ref(v_as_3428_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3435_, size_t v_i_3436_, size_t v_stop_3437_, lean_object* v_b_3438_){
_start:
{
lean_object* v___y_3440_; uint8_t v___x_3444_; 
v___x_3444_ = lean_usize_dec_eq(v_i_3436_, v_stop_3437_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3445_ = lean_array_uget_borrowed(v_as_3435_, v_i_3436_);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_array_get_size(v___x_3445_);
v___x_3448_ = lean_nat_dec_lt(v___x_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
v___y_3440_ = v_b_3438_;
goto v___jp_3439_;
}
else
{
uint8_t v___x_3449_; 
v___x_3449_ = lean_nat_dec_le(v___x_3447_, v___x_3447_);
if (v___x_3449_ == 0)
{
if (v___x_3448_ == 0)
{
v___y_3440_ = v_b_3438_;
goto v___jp_3439_;
}
else
{
size_t v___x_3450_; size_t v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((size_t)0ULL);
v___x_3451_ = lean_usize_of_nat(v___x_3447_);
v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3445_, v___x_3450_, v___x_3451_, v_b_3438_);
v___y_3440_ = v___x_3452_;
goto v___jp_3439_;
}
}
else
{
size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = lean_usize_of_nat(v___x_3447_);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3445_, v___x_3453_, v___x_3454_, v_b_3438_);
v___y_3440_ = v___x_3455_;
goto v___jp_3439_;
}
}
}
else
{
return v_b_3438_;
}
v___jp_3439_:
{
size_t v___x_3441_; size_t v___x_3442_; 
v___x_3441_ = ((size_t)1ULL);
v___x_3442_ = lean_usize_add(v_i_3436_, v___x_3441_);
v_i_3436_ = v___x_3442_;
v_b_3438_ = v___y_3440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3456_, lean_object* v_i_3457_, lean_object* v_stop_3458_, lean_object* v_b_3459_){
_start:
{
size_t v_i_boxed_3460_; size_t v_stop_boxed_3461_; lean_object* v_res_3462_; 
v_i_boxed_3460_ = lean_unbox_usize(v_i_3457_);
lean_dec(v_i_3457_);
v_stop_boxed_3461_ = lean_unbox_usize(v_stop_3458_);
lean_dec(v_stop_3458_);
v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3456_, v_i_boxed_3460_, v_stop_boxed_3461_, v_b_3459_);
lean_dec_ref(v_as_3456_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3463_){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_array_get_size(v_mr_3463_);
v___x_3466_ = lean_nat_dec_lt(v___x_3464_, v___x_3465_);
if (v___x_3466_ == 0)
{
return v___x_3464_;
}
else
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_nat_dec_le(v___x_3465_, v___x_3465_);
if (v___x_3467_ == 0)
{
if (v___x_3466_ == 0)
{
return v___x_3464_;
}
else
{
size_t v___x_3468_; size_t v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = ((size_t)0ULL);
v___x_3469_ = lean_usize_of_nat(v___x_3465_);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3463_, v___x_3468_, v___x_3469_, v___x_3464_);
return v___x_3470_;
}
}
else
{
size_t v___x_3471_; size_t v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = ((size_t)0ULL);
v___x_3472_ = lean_usize_of_nat(v___x_3465_);
v___x_3473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3463_, v___x_3471_, v___x_3472_, v___x_3464_);
return v___x_3473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3474_);
lean_dec_ref(v_mr_3474_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3476_, lean_object* v_mr_3477_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_mr_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3479_, v_mr_3480_);
lean_dec_ref(v_mr_3480_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3482_, lean_object* v_as_3483_, size_t v_i_3484_, size_t v_stop_3485_, lean_object* v_b_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3483_, v_i_3484_, v_stop_3485_, v_b_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3488_, lean_object* v_as_3489_, lean_object* v_i_3490_, lean_object* v_stop_3491_, lean_object* v_b_3492_){
_start:
{
size_t v_i_boxed_3493_; size_t v_stop_boxed_3494_; lean_object* v_res_3495_; 
v_i_boxed_3493_ = lean_unbox_usize(v_i_3490_);
lean_dec(v_i_3490_);
v_stop_boxed_3494_ = lean_unbox_usize(v_stop_3491_);
lean_dec(v_stop_3491_);
v_res_3495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3488_, v_as_3489_, v_i_boxed_3493_, v_stop_boxed_3494_, v_b_3492_);
lean_dec_ref(v_as_3489_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3496_, lean_object* v_as_3497_, size_t v_i_3498_, size_t v_stop_3499_, lean_object* v_b_3500_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3497_, v_i_3498_, v_stop_3499_, v_b_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3502_, lean_object* v_as_3503_, lean_object* v_i_3504_, lean_object* v_stop_3505_, lean_object* v_b_3506_){
_start:
{
size_t v_i_boxed_3507_; size_t v_stop_boxed_3508_; lean_object* v_res_3509_; 
v_i_boxed_3507_ = lean_unbox_usize(v_i_3504_);
lean_dec(v_i_3504_);
v_stop_boxed_3508_ = lean_unbox_usize(v_stop_3505_);
lean_dec(v_stop_3505_);
v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3502_, v_as_3503_, v_i_boxed_3507_, v_stop_boxed_3508_, v_b_3506_);
lean_dec_ref(v_as_3503_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3510_, lean_object* v_j_3511_, lean_object* v_x_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_apply_2(v_f_3510_, v_j_3511_, v_x_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3533_, lean_object* v_x1_3534_, lean_object* v_x2_3535_){
_start:
{
lean_object* v___x_3536_; size_t v_sz_3537_; size_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3536_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3537_ = lean_array_size(v_x2_3535_);
v___x_3538_ = ((size_t)0ULL);
v___x_3539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3536_, v___f_3533_, v_sz_3537_, v___x_3538_, v_x2_3535_);
v___x_3540_ = l_Array_append___redArg(v_x1_3534_, v___x_3539_);
lean_dec(v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3541_, lean_object* v_mr_3542_, lean_object* v_f_3543_, lean_object* v_i_3544_, lean_object* v_x_3545_, lean_object* v_r_3546_){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v_j_3549_; lean_object* v_b_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_sub(v_n_3541_, v___x_3547_);
v_j_3549_ = lean_nat_sub(v___x_3548_, v_i_3544_);
lean_dec(v___x_3548_);
v_b_3550_ = lean_array_fget_borrowed(v_mr_3542_, v_j_3549_);
v___x_3551_ = lean_unsigned_to_nat(0u);
v___x_3552_ = lean_array_get_size(v_b_3550_);
v___x_3553_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3554_ = lean_nat_dec_lt(v___x_3551_, v___x_3552_);
if (v___x_3554_ == 0)
{
lean_dec(v_j_3549_);
lean_dec(v_f_3543_);
return v_r_3546_;
}
else
{
lean_object* v___f_3555_; lean_object* v___f_3556_; uint8_t v___x_3557_; 
v___f_3555_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3555_, 0, v_f_3543_);
lean_closure_set(v___f_3555_, 1, v_j_3549_);
v___f_3556_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3556_, 0, v___f_3555_);
v___x_3557_ = lean_nat_dec_le(v___x_3552_, v___x_3552_);
if (v___x_3557_ == 0)
{
if (v___x_3554_ == 0)
{
lean_dec_ref(v___f_3556_);
return v_r_3546_;
}
else
{
size_t v___x_3558_; size_t v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((size_t)0ULL);
v___x_3559_ = lean_usize_of_nat(v___x_3552_);
lean_inc(v_b_3550_);
v___x_3560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3553_, v___f_3556_, v_b_3550_, v___x_3558_, v___x_3559_, v_r_3546_);
return v___x_3560_;
}
}
else
{
size_t v___x_3561_; size_t v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = ((size_t)0ULL);
v___x_3562_ = lean_usize_of_nat(v___x_3552_);
lean_inc(v_b_3550_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3553_, v___f_3556_, v_b_3550_, v___x_3561_, v___x_3562_, v_r_3546_);
return v___x_3563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3564_, lean_object* v_mr_3565_, lean_object* v_f_3566_, lean_object* v_i_3567_, lean_object* v_x_3568_, lean_object* v_r_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3564_, v_mr_3565_, v_f_3566_, v_i_3567_, v_x_3568_, v_r_3569_);
lean_dec(v_i_3567_);
lean_dec_ref(v_mr_3565_);
lean_dec(v_n_3564_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3571_, lean_object* v_a_3572_, lean_object* v_f_3573_){
_start:
{
lean_object* v_n_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; 
v_n_3574_ = lean_array_get_size(v_mr_3571_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3575_, 0, v_n_3574_);
lean_closure_set(v___f_3575_, 1, v_mr_3571_);
lean_closure_set(v___f_3575_, 2, v_f_3573_);
v___x_3576_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3574_, v___f_3575_, v_n_3574_, lean_box(0), v_a_3572_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3577_, lean_object* v_00_u03b2_3578_, lean_object* v_mr_3579_, lean_object* v_a_3580_, lean_object* v_f_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3579_, v_a_3580_, v_f_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3583_, size_t v_i_3584_, lean_object* v_bs_3585_){
_start:
{
uint8_t v___x_3586_; 
v___x_3586_ = lean_usize_dec_lt(v_i_3584_, v_sz_3583_);
if (v___x_3586_ == 0)
{
return v_bs_3585_;
}
else
{
lean_object* v_v_3587_; lean_object* v___x_3588_; lean_object* v_bs_x27_3589_; size_t v___x_3590_; size_t v___x_3591_; lean_object* v___x_3592_; 
v_v_3587_ = lean_array_uget(v_bs_3585_, v_i_3584_);
v___x_3588_ = lean_unsigned_to_nat(0u);
v_bs_x27_3589_ = lean_array_uset(v_bs_3585_, v_i_3584_, v___x_3588_);
v___x_3590_ = ((size_t)1ULL);
v___x_3591_ = lean_usize_add(v_i_3584_, v___x_3590_);
v___x_3592_ = lean_array_uset(v_bs_x27_3589_, v_i_3584_, v_v_3587_);
v_i_3584_ = v___x_3591_;
v_bs_3585_ = v___x_3592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3594_, lean_object* v_i_3595_, lean_object* v_bs_3596_){
_start:
{
size_t v_sz_boxed_3597_; size_t v_i_boxed_3598_; lean_object* v_res_3599_; 
v_sz_boxed_3597_ = lean_unbox_usize(v_sz_3594_);
lean_dec(v_sz_3594_);
v_i_boxed_3598_ = lean_unbox_usize(v_i_3595_);
lean_dec(v_i_3595_);
v_res_3599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3597_, v_i_boxed_3598_, v_bs_3596_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3600_, size_t v_i_3601_, size_t v_stop_3602_, lean_object* v_b_3603_){
_start:
{
uint8_t v___x_3604_; 
v___x_3604_ = lean_usize_dec_eq(v_i_3601_, v_stop_3602_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; size_t v_sz_3606_; size_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; size_t v___x_3610_; size_t v___x_3611_; 
v___x_3605_ = lean_array_uget_borrowed(v_as_3600_, v_i_3601_);
v_sz_3606_ = lean_array_size(v___x_3605_);
v___x_3607_ = ((size_t)0ULL);
lean_inc(v___x_3605_);
v___x_3608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3606_, v___x_3607_, v___x_3605_);
v___x_3609_ = l_Array_append___redArg(v_b_3603_, v___x_3608_);
lean_dec_ref(v___x_3608_);
v___x_3610_ = ((size_t)1ULL);
v___x_3611_ = lean_usize_add(v_i_3601_, v___x_3610_);
v_i_3601_ = v___x_3611_;
v_b_3603_ = v___x_3609_;
goto _start;
}
else
{
return v_b_3603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3613_, lean_object* v_i_3614_, lean_object* v_stop_3615_, lean_object* v_b_3616_){
_start:
{
size_t v_i_boxed_3617_; size_t v_stop_boxed_3618_; lean_object* v_res_3619_; 
v_i_boxed_3617_ = lean_unbox_usize(v_i_3614_);
lean_dec(v_i_3614_);
v_stop_boxed_3618_ = lean_unbox_usize(v_stop_3615_);
lean_dec(v_stop_3615_);
v_res_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3613_, v_i_boxed_3617_, v_stop_boxed_3618_, v_b_3616_);
lean_dec_ref(v_as_3613_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3620_, lean_object* v_aa_3621_, lean_object* v_n_3622_, lean_object* v_j_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v_zero_3625_; uint8_t v_isZero_3626_; 
v_zero_3625_ = lean_unsigned_to_nat(0u);
v_isZero_3626_ = lean_nat_dec_eq(v_j_3623_, v_zero_3625_);
if (v_isZero_3626_ == 1)
{
lean_dec(v_j_3623_);
return v_a_3624_;
}
else
{
lean_object* v_one_3627_; lean_object* v_n_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v_j_3631_; lean_object* v_b_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v_one_3627_ = lean_unsigned_to_nat(1u);
v_n_3628_ = lean_nat_sub(v_j_3623_, v_one_3627_);
v___x_3629_ = lean_nat_sub(v_n_3622_, v_j_3623_);
lean_dec(v_j_3623_);
v___x_3630_ = lean_nat_sub(v_n_3620_, v_one_3627_);
v_j_3631_ = lean_nat_sub(v___x_3630_, v___x_3629_);
lean_dec(v___x_3629_);
lean_dec(v___x_3630_);
v_b_3632_ = lean_array_fget_borrowed(v_aa_3621_, v_j_3631_);
lean_dec(v_j_3631_);
v___x_3633_ = lean_array_get_size(v_b_3632_);
v___x_3634_ = lean_nat_dec_lt(v_zero_3625_, v___x_3633_);
if (v___x_3634_ == 0)
{
v_j_3623_ = v_n_3628_;
goto _start;
}
else
{
size_t v___x_3636_; size_t v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = ((size_t)0ULL);
v___x_3637_ = lean_usize_of_nat(v___x_3633_);
v___x_3638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3632_, v___x_3636_, v___x_3637_, v_a_3624_);
v_j_3623_ = v_n_3628_;
v_a_3624_ = v___x_3638_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3640_, lean_object* v_aa_3641_, lean_object* v_n_3642_, lean_object* v_j_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3640_, v_aa_3641_, v_n_3642_, v_j_3643_, v_a_3644_);
lean_dec(v_n_3642_);
lean_dec_ref(v_aa_3641_);
lean_dec(v_n_3640_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_n_3648_; lean_object* v___x_3649_; 
v_n_3648_ = lean_array_get_size(v_mr_3646_);
v___x_3649_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3648_, v_mr_3646_, v_n_3648_, v_n_3648_, v_a_3647_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3650_, v_a_3651_);
lean_dec_ref(v_mr_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3653_, v_a_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3656_, v_a_3657_);
lean_dec_ref(v_mr_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3659_, lean_object* v_mr_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3660_, v_a_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3663_, lean_object* v_mr_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3663_, v_mr_3664_, v_a_3665_);
lean_dec_ref(v_mr_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3667_, lean_object* v_mr_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3668_, v_a_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3671_, lean_object* v_mr_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3671_, v_mr_3672_, v_a_3673_);
lean_dec_ref(v_mr_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3675_, size_t v_sz_3676_, size_t v_i_3677_, lean_object* v_bs_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3676_, v_i_3677_, v_bs_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3680_, lean_object* v_sz_3681_, lean_object* v_i_3682_, lean_object* v_bs_3683_){
_start:
{
size_t v_sz_boxed_3684_; size_t v_i_boxed_3685_; lean_object* v_res_3686_; 
v_sz_boxed_3684_ = lean_unbox_usize(v_sz_3681_);
lean_dec(v_sz_3681_);
v_i_boxed_3685_ = lean_unbox_usize(v_i_3682_);
lean_dec(v_i_3682_);
v_res_3686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3680_, v_sz_boxed_3684_, v_i_boxed_3685_, v_bs_3683_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3687_, lean_object* v_as_3688_, size_t v_i_3689_, size_t v_stop_3690_, lean_object* v_b_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3688_, v_i_3689_, v_stop_3690_, v_b_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3693_, lean_object* v_as_3694_, lean_object* v_i_3695_, lean_object* v_stop_3696_, lean_object* v_b_3697_){
_start:
{
size_t v_i_boxed_3698_; size_t v_stop_boxed_3699_; lean_object* v_res_3700_; 
v_i_boxed_3698_ = lean_unbox_usize(v_i_3695_);
lean_dec(v_i_3695_);
v_stop_boxed_3699_ = lean_unbox_usize(v_stop_3696_);
lean_dec(v_stop_3696_);
v_res_3700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3693_, v_as_3694_, v_i_boxed_3698_, v_stop_boxed_3699_, v_b_3697_);
lean_dec_ref(v_as_3694_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3701_, lean_object* v_n_3702_, lean_object* v_aa_3703_, lean_object* v_n_3704_, lean_object* v_j_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3702_, v_aa_3703_, v_n_3704_, v_j_3705_, v_a_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3709_, lean_object* v_n_3710_, lean_object* v_aa_3711_, lean_object* v_n_3712_, lean_object* v_j_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3709_, v_n_3710_, v_aa_3711_, v_n_3712_, v_j_3713_, v_a_3714_, v_a_3715_);
lean_dec(v_n_3712_);
lean_dec_ref(v_aa_3711_);
lean_dec(v_n_3710_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3724_, lean_object* v___x_3725_, lean_object* v_score_3726_, lean_object* v___x_3727_, lean_object* v_k_3728_, lean_object* v_args_3729_, lean_object* v_cases_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3724_, v_k_3728_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_dec_ref(v___x_3725_);
return v_cases_3730_;
}
else
{
lean_object* v_val_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_val_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_val_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v___x_3733_ = l_Array_append___redArg(v___x_3725_, v_args_3729_);
v___x_3734_ = lean_nat_add(v_score_3726_, v___x_3727_);
v___x_3735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
lean_ctor_set(v___x_3735_, 2, v_val_3732_);
v___x_3736_ = lean_array_push(v_cases_3730_, v___x_3735_);
return v___x_3736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3737_, lean_object* v___x_3738_, lean_object* v_score_3739_, lean_object* v___x_3740_, lean_object* v_k_3741_, lean_object* v_args_3742_, lean_object* v_cases_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3737_, v___x_3738_, v_score_3739_, v___x_3740_, v_k_3741_, v_args_3742_, v_cases_3743_);
lean_dec_ref(v_args_3742_);
lean_dec(v_k_3741_);
lean_dec(v___x_3740_);
lean_dec(v_score_3739_);
lean_dec_ref(v_snd_3737_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3745_, lean_object* v_result_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3753_ = lean_array_get_size(v_cases_3745_);
v___x_3754_ = lean_unsigned_to_nat(0u);
v___x_3755_ = lean_nat_dec_eq(v___x_3753_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v_ca_3759_; lean_object* v_todo_3760_; lean_object* v_score_3761_; lean_object* v_c_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3827_; 
v___x_3756_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3757_ = lean_unsigned_to_nat(1u);
v___x_3758_ = lean_nat_sub(v___x_3753_, v___x_3757_);
v_ca_3759_ = lean_array_get(v___x_3756_, v_cases_3745_, v___x_3758_);
lean_dec(v___x_3758_);
v_todo_3760_ = lean_ctor_get(v_ca_3759_, 0);
v_score_3761_ = lean_ctor_get(v_ca_3759_, 1);
v_c_3762_ = lean_ctor_get(v_ca_3759_, 2);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_ca_3759_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3764_ = v_ca_3759_;
v_isShared_3765_ = v_isSharedCheck_3827_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_c_3762_);
lean_inc(v_score_3761_);
lean_inc(v_todo_3760_);
lean_dec(v_ca_3759_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3827_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3762_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
lean_dec(v_c_3762_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; uint8_t v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v_snd_3795_; lean_object* v_fst_3796_; lean_object* v_fst_3797_; lean_object* v_snd_3798_; lean_object* v_cases_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v_snd_3795_ = lean_ctor_get(v_a_3767_, 1);
lean_inc(v_snd_3795_);
v_fst_3796_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_fst_3796_);
lean_dec(v_a_3767_);
v_fst_3797_ = lean_ctor_get(v_snd_3795_, 0);
lean_inc(v_fst_3797_);
v_snd_3798_ = lean_ctor_get(v_snd_3795_, 1);
lean_inc(v_snd_3798_);
lean_dec(v_snd_3795_);
v_cases_3799_ = lean_array_pop(v_cases_3745_);
v___x_3800_ = lean_array_get_size(v_todo_3760_);
v___x_3801_ = lean_nat_dec_eq(v___x_3800_, v___x_3754_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; uint8_t v___x_3803_; uint8_t v___y_3805_; 
lean_dec(v_fst_3796_);
v___x_3802_ = l_Lean_instInhabitedExpr;
v___x_3803_ = lean_nat_dec_eq(v_fst_3797_, v___x_3754_);
if (v___x_3803_ == 0)
{
v___y_3805_ = v___x_3801_;
goto v___jp_3804_;
}
else
{
lean_object* v_size_3814_; uint8_t v___x_3815_; 
v_size_3814_ = lean_ctor_get(v_snd_3798_, 0);
v___x_3815_ = lean_nat_dec_eq(v_size_3814_, v___x_3754_);
if (v___x_3815_ == 0)
{
v___y_3805_ = v___x_3815_;
goto v___jp_3804_;
}
else
{
lean_dec(v_snd_3798_);
lean_dec(v_fst_3797_);
lean_del_object(v___x_3764_);
lean_dec(v_score_3761_);
lean_dec_ref(v_todo_3760_);
v_cases_3745_ = v_cases_3799_;
goto _start;
}
}
v___jp_3804_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___f_3809_; 
v___x_3806_ = lean_nat_sub(v___x_3800_, v___x_3757_);
v___x_3807_ = lean_array_get(v___x_3802_, v_todo_3760_, v___x_3806_);
lean_dec(v___x_3806_);
v___x_3808_ = lean_array_pop(v_todo_3760_);
lean_inc(v_score_3761_);
lean_inc_ref(v___x_3808_);
v___f_3809_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3809_, 0, v_snd_3798_);
lean_closure_set(v___f_3809_, 1, v___x_3808_);
lean_closure_set(v___f_3809_, 2, v_score_3761_);
lean_closure_set(v___f_3809_, 3, v___x_3757_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3811_; 
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 2, v_fst_3797_);
lean_ctor_set(v___x_3764_, 0, v___x_3808_);
v___x_3811_ = v___x_3764_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_score_3761_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_fst_3797_);
v___x_3811_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_array_push(v_cases_3799_, v___x_3811_);
v___y_3769_ = v___y_3805_;
v___y_3770_ = v___f_3809_;
v___y_3771_ = v___x_3807_;
v___y_3772_ = v___x_3812_;
goto v___jp_3768_;
}
}
else
{
lean_dec_ref(v___x_3808_);
lean_dec(v_fst_3797_);
lean_del_object(v___x_3764_);
lean_dec(v_score_3761_);
v___y_3769_ = v___y_3805_;
v___y_3770_ = v___f_3809_;
v___y_3771_ = v___x_3807_;
v___y_3772_ = v_cases_3799_;
goto v___jp_3768_;
}
}
}
else
{
lean_object* v___x_3817_; 
lean_dec(v_snd_3798_);
lean_dec(v_fst_3797_);
lean_del_object(v___x_3764_);
lean_dec_ref(v_todo_3760_);
v___x_3817_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3746_, v_score_3761_, v_fst_3796_);
lean_dec(v_score_3761_);
v_cases_3745_ = v_cases_3799_;
v_result_3746_ = v___x_3817_;
goto _start;
}
v___jp_3768_:
{
uint8_t v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = 1;
v___x_3774_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3771_, v___x_3773_, v___y_3769_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v_fst_3776_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v___x_3774_, 1);
v_fst_3776_ = lean_ctor_get(v_a_3775_, 0);
lean_inc(v_fst_3776_);
switch(lean_obj_tag(v_fst_3776_))
{
case 3:
{
lean_dec(v_a_3775_);
lean_dec_ref(v___y_3770_);
v_cases_3745_ = v___y_3772_;
goto _start;
}
case 5:
{
lean_object* v_snd_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_snd_3778_ = lean_ctor_get(v_a_3775_, 1);
lean_inc(v_snd_3778_);
lean_dec(v_a_3775_);
v___x_3779_ = lean_box(4);
v___x_3780_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3770_);
v___x_3781_ = lean_apply_3(v___y_3770_, v___x_3779_, v___x_3780_, v___y_3772_);
v___x_3782_ = lean_apply_3(v___y_3770_, v_fst_3776_, v_snd_3778_, v___x_3781_);
v_cases_3745_ = v___x_3782_;
goto _start;
}
default: 
{
lean_object* v_snd_3784_; lean_object* v___x_3785_; 
v_snd_3784_ = lean_ctor_get(v_a_3775_, 1);
lean_inc(v_snd_3784_);
lean_dec(v_a_3775_);
v___x_3785_ = lean_apply_3(v___y_3770_, v_fst_3776_, v_snd_3784_, v___y_3772_);
v_cases_3745_ = v___x_3785_;
goto _start;
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v___y_3772_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v_result_3746_);
v_a_3787_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3774_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3774_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_del_object(v___x_3764_);
lean_dec(v_score_3761_);
lean_dec_ref(v_todo_3760_);
lean_dec_ref(v_result_3746_);
lean_dec_ref(v_cases_3745_);
v_a_3819_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3766_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3766_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
else
{
lean_object* v___x_3828_; 
lean_dec_ref(v_cases_3745_);
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_result_3746_);
return v___x_3828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3829_, lean_object* v_result_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3829_, v_result_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3838_, lean_object* v_cases_3839_, lean_object* v_result_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3839_, v_result_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_cases_3849_, lean_object* v_result_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3848_, v_cases_3849_, v_result_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_box(3);
v___x_3868_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3860_, v___x_3867_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3869_);
return v___x_3870_;
}
else
{
lean_object* v_val_3871_; lean_object* v___x_3872_; 
v_val_3871_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_val_3871_);
lean_dec_ref_known(v___x_3868_, 1);
v___x_3872_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3871_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_val_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3884_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3875_ = v___x_3872_;
v_isShared_3876_ = v_isSharedCheck_3884_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3872_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3884_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v_fst_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
v_fst_3877_ = lean_ctor_get(v_a_3873_, 0);
lean_inc(v_fst_3877_);
lean_dec(v_a_3873_);
v___x_3878_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3879_ = lean_unsigned_to_nat(1u);
v___x_3880_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3878_, v___x_3879_, v_fst_3877_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 0, v___x_3880_);
v___x_3882_ = v___x_3875_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3872_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3872_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_root_3893_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3901_, lean_object* v_root_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3910_, lean_object* v_root_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3910_, v_root_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_root_3911_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3919_, lean_object* v_k_3920_, lean_object* v_args_3921_, lean_object* v_cases_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3919_, v_k_3920_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_dec_ref(v_args_3921_);
return v_cases_3922_;
}
else
{
lean_object* v_val_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_val_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_val_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = lean_unsigned_to_nat(1u);
v___x_3926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3926_, 0, v_args_3921_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
lean_ctor_set(v___x_3926_, 2, v_val_3924_);
v___x_3927_ = lean_array_push(v_cases_3922_, v___x_3926_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3928_, lean_object* v_k_3929_, lean_object* v_args_3930_, lean_object* v_cases_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3928_, v_k_3929_, v_args_3930_, v_cases_3931_);
lean_dec(v_k_3929_);
lean_dec_ref(v_r_3928_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3935_, lean_object* v_e_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v___x_3943_; 
v___x_3943_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3935_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = 1;
v___x_3946_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3936_, v___x_3945_, v___x_3945_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v_fst_3948_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3946_, 1);
v_fst_3948_ = lean_ctor_get(v_a_3947_, 0);
lean_inc(v_fst_3948_);
switch(lean_obj_tag(v_fst_3948_))
{
case 3:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_dec(v_a_3947_);
v___x_3949_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3950_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3949_, v_a_3944_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
return v___x_3950_;
}
case 5:
{
lean_object* v_snd_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_snd_3951_ = lean_ctor_get(v_a_3947_, 1);
lean_inc(v_snd_3951_);
lean_dec(v_a_3947_);
v___x_3952_ = lean_box(4);
v___x_3953_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3954_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3935_, v___x_3952_, v___x_3953_, v___x_3953_);
v___x_3955_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3935_, v_fst_3948_, v_snd_3951_, v___x_3954_);
v___x_3956_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3955_, v_a_3944_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
return v___x_3956_;
}
default: 
{
lean_object* v_snd_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_snd_3957_ = lean_ctor_get(v_a_3947_, 1);
lean_inc(v_snd_3957_);
lean_dec(v_a_3947_);
v___x_3958_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3959_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3935_, v_fst_3948_, v_snd_3957_, v___x_3958_);
lean_dec(v_fst_3948_);
v___x_3960_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3959_, v_a_3944_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
return v___x_3960_;
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
lean_dec(v_a_3944_);
v_a_3961_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3963_ = v___x_3946_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3946_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
else
{
lean_dec_ref(v_e_3936_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3969_, lean_object* v_e_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3969_, v_e_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_root_3969_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_3978_, lean_object* v_root_3979_, lean_object* v_e_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3979_, v_e_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_3988_, lean_object* v_root_3989_, lean_object* v_e_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_3988_, v_root_3989_, v_e_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_root_3989_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_3998_, lean_object* v_e_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_roots_4005_; lean_object* v_keyedConfig_4006_; uint8_t v_trackZetaDelta_4007_; lean_object* v_zetaDeltaSet_4008_; lean_object* v_lctx_4009_; lean_object* v_localInstances_4010_; lean_object* v_defEqCtx_x3f_4011_; lean_object* v_synthPendingDepth_4012_; lean_object* v_customCanUnfoldPredicate_x3f_4013_; uint8_t v_univApprox_4014_; uint8_t v_inTypeClassResolution_4015_; uint8_t v_cacheInferType_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_roots_4005_ = lean_ctor_get(v_d_3998_, 1);
v_keyedConfig_4006_ = lean_ctor_get(v_a_4000_, 0);
v_trackZetaDelta_4007_ = lean_ctor_get_uint8(v_a_4000_, sizeof(void*)*7);
v_zetaDeltaSet_4008_ = lean_ctor_get(v_a_4000_, 1);
v_lctx_4009_ = lean_ctor_get(v_a_4000_, 2);
v_localInstances_4010_ = lean_ctor_get(v_a_4000_, 3);
v_defEqCtx_x3f_4011_ = lean_ctor_get(v_a_4000_, 4);
v_synthPendingDepth_4012_ = lean_ctor_get(v_a_4000_, 5);
v_customCanUnfoldPredicate_x3f_4013_ = lean_ctor_get(v_a_4000_, 6);
v_univApprox_4014_ = lean_ctor_get_uint8(v_a_4000_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4015_ = lean_ctor_get_uint8(v_a_4000_, sizeof(void*)*7 + 2);
v_cacheInferType_4016_ = lean_ctor_get_uint8(v_a_4000_, sizeof(void*)*7 + 3);
lean_inc_ref(v_roots_4005_);
v___x_4017_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4017_, 0, lean_box(0));
lean_closure_set(v___x_4017_, 1, v_roots_4005_);
lean_closure_set(v___x_4017_, 2, v_e_3999_);
v___x_4018_ = 2;
lean_inc_ref(v_keyedConfig_4006_);
v___x_4019_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4018_, v_keyedConfig_4006_);
lean_inc(v_customCanUnfoldPredicate_x3f_4013_);
lean_inc(v_synthPendingDepth_4012_);
lean_inc(v_defEqCtx_x3f_4011_);
lean_inc_ref(v_localInstances_4010_);
lean_inc_ref(v_lctx_4009_);
lean_inc(v_zetaDeltaSet_4008_);
v___x_4020_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
lean_ctor_set(v___x_4020_, 1, v_zetaDeltaSet_4008_);
lean_ctor_set(v___x_4020_, 2, v_lctx_4009_);
lean_ctor_set(v___x_4020_, 3, v_localInstances_4010_);
lean_ctor_set(v___x_4020_, 4, v_defEqCtx_x3f_4011_);
lean_ctor_set(v___x_4020_, 5, v_synthPendingDepth_4012_);
lean_ctor_set(v___x_4020_, 6, v_customCanUnfoldPredicate_x3f_4013_);
lean_ctor_set_uint8(v___x_4020_, sizeof(void*)*7, v_trackZetaDelta_4007_);
lean_ctor_set_uint8(v___x_4020_, sizeof(void*)*7 + 1, v_univApprox_4014_);
lean_ctor_set_uint8(v___x_4020_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4015_);
lean_ctor_set_uint8(v___x_4020_, sizeof(void*)*7 + 3, v_cacheInferType_4016_);
v___x_4021_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_3998_, v___x_4017_, v___x_4020_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec_ref_known(v___x_4020_, 7);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4022_, lean_object* v_e_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4022_, v_e_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4030_, lean_object* v_d_4031_, lean_object* v_e_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4031_, v_e_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4039_, lean_object* v_d_4040_, lean_object* v_e_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4039_, v_d_4040_, v_e_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
return v_res_4047_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4051_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
lean_ctor_set(v___x_4052_, 1, v___x_4050_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4054_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4058_, lean_object* v_k_4059_, lean_object* v_f_4060_){
_start:
{
lean_object* v_roots_4061_; lean_object* v_tries_4062_; lean_object* v___x_4063_; 
v_roots_4061_ = lean_ctor_get(v_d_4058_, 0);
v_tries_4062_ = lean_ctor_get(v_d_4058_, 1);
v___x_4063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4061_, v_k_4059_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4075_; 
lean_inc_ref(v_tries_4062_);
lean_inc_ref(v_roots_4061_);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_d_4058_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; lean_object* v_unused_4077_; 
v_unused_4076_ = lean_ctor_get(v_d_4058_, 1);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v_d_4058_, 0);
lean_dec(v_unused_4077_);
v___x_4065_ = v_d_4058_;
v_isShared_4066_ = v_isSharedCheck_4075_;
goto v_resetjp_4064_;
}
else
{
lean_dec(v_d_4058_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4075_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; lean_object* v_roots_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4067_ = lean_array_get_size(v_tries_4062_);
v_roots_4068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4061_, v_k_4059_, v___x_4067_);
v___x_4069_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_4070_ = lean_apply_1(v_f_4060_, v___x_4069_);
v___x_4071_ = lean_array_push(v_tries_4062_, v___x_4070_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 1, v___x_4071_);
lean_ctor_set(v___x_4065_, 0, v_roots_4068_);
v___x_4073_ = v___x_4065_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_roots_4068_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
else
{
lean_object* v_val_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
lean_dec(v_k_4059_);
v_val_4078_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_val_4078_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4079_ = lean_array_get_size(v_tries_4062_);
v___x_4080_ = lean_nat_dec_lt(v_val_4078_, v___x_4079_);
if (v___x_4080_ == 0)
{
lean_dec(v_val_4078_);
lean_dec_ref(v_f_4060_);
return v_d_4058_;
}
else
{
lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4092_; 
lean_inc_ref(v_tries_4062_);
lean_inc_ref(v_roots_4061_);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_d_4058_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; lean_object* v_unused_4094_; 
v_unused_4093_ = lean_ctor_get(v_d_4058_, 1);
lean_dec(v_unused_4093_);
v_unused_4094_ = lean_ctor_get(v_d_4058_, 0);
lean_dec(v_unused_4094_);
v___x_4082_ = v_d_4058_;
v_isShared_4083_ = v_isSharedCheck_4092_;
goto v_resetjp_4081_;
}
else
{
lean_dec(v_d_4058_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4092_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v_v_4084_; lean_object* v___x_4085_; lean_object* v_xs_x27_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4090_; 
v_v_4084_ = lean_array_fget(v_tries_4062_, v_val_4078_);
v___x_4085_ = lean_box(0);
v_xs_x27_4086_ = lean_array_fset(v_tries_4062_, v_val_4078_, v___x_4085_);
v___x_4087_ = lean_apply_1(v_f_4060_, v_v_4084_);
v___x_4088_ = lean_array_fset(v_xs_x27_4086_, v_val_4078_, v___x_4087_);
lean_dec(v_val_4078_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 1, v___x_4088_);
v___x_4090_ = v___x_4082_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_roots_4061_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4095_, lean_object* v_d_4096_, lean_object* v_k_4097_, lean_object* v_f_4098_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4096_, v_k_4097_, v_f_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4100_, lean_object* v_x_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_array_push(v_x_4101_, v_e_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4103_, lean_object* v_k_4104_, lean_object* v_e_4105_){
_start:
{
lean_object* v___f_4106_; lean_object* v___x_4107_; 
v___f_4106_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4106_, 0, v_e_4105_);
v___x_4107_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4103_, v_k_4104_, v___f_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4108_, lean_object* v_d_4109_, lean_object* v_k_4110_, lean_object* v_e_4111_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4109_, v_k_4110_, v_e_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4113_, size_t v_i_4114_, lean_object* v_bs_4115_){
_start:
{
uint8_t v___x_4116_; 
v___x_4116_ = lean_usize_dec_lt(v_i_4114_, v_sz_4113_);
if (v___x_4116_ == 0)
{
return v_bs_4115_;
}
else
{
lean_object* v_v_4117_; lean_object* v___x_4118_; lean_object* v_bs_x27_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; size_t v___x_4123_; size_t v___x_4124_; lean_object* v___x_4125_; 
v_v_4117_ = lean_array_uget(v_bs_4115_, v_i_4114_);
v___x_4118_ = lean_unsigned_to_nat(0u);
v_bs_x27_4119_ = lean_array_uset(v_bs_4115_, v_i_4114_, v___x_4118_);
v___x_4120_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4121_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4118_);
lean_ctor_set(v___x_4122_, 2, v___x_4121_);
lean_ctor_set(v___x_4122_, 3, v_v_4117_);
v___x_4123_ = ((size_t)1ULL);
v___x_4124_ = lean_usize_add(v_i_4114_, v___x_4123_);
v___x_4125_ = lean_array_uset(v_bs_x27_4119_, v_i_4114_, v___x_4122_);
v_i_4114_ = v___x_4124_;
v_bs_4115_ = v___x_4125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4127_, lean_object* v_i_4128_, lean_object* v_bs_4129_){
_start:
{
size_t v_sz_boxed_4130_; size_t v_i_boxed_4131_; lean_object* v_res_4132_; 
v_sz_boxed_4130_ = lean_unbox_usize(v_sz_4127_);
lean_dec(v_sz_4127_);
v_i_boxed_4131_ = lean_unbox_usize(v_i_4128_);
lean_dec(v_i_4128_);
v_res_4132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4130_, v_i_boxed_4131_, v_bs_4129_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4133_, lean_object* v_x_4134_){
_start:
{
if (lean_obj_tag(v_x_4134_) == 0)
{
return v_x_4133_;
}
else
{
lean_object* v_key_4135_; lean_object* v_value_4136_; lean_object* v_tail_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_key_4135_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_key_4135_);
v_value_4136_ = lean_ctor_get(v_x_4134_, 1);
lean_inc(v_value_4136_);
v_tail_4137_ = lean_ctor_get(v_x_4134_, 2);
lean_inc(v_tail_4137_);
lean_dec_ref_known(v_x_4134_, 3);
v___x_4138_ = lean_unsigned_to_nat(1u);
v___x_4139_ = lean_nat_add(v_value_4136_, v___x_4138_);
lean_dec(v_value_4136_);
v___x_4140_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4133_, v_key_4135_, v___x_4139_);
v_x_4133_ = v___x_4140_;
v_x_4134_ = v_tail_4137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4142_, size_t v_i_4143_, size_t v_stop_4144_, lean_object* v_b_4145_){
_start:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_usize_dec_eq(v_i_4143_, v_stop_4144_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; lean_object* v___x_4148_; size_t v___x_4149_; size_t v___x_4150_; 
v___x_4147_ = lean_array_uget_borrowed(v_as_4142_, v_i_4143_);
lean_inc(v___x_4147_);
v___x_4148_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4145_, v___x_4147_);
v___x_4149_ = ((size_t)1ULL);
v___x_4150_ = lean_usize_add(v_i_4143_, v___x_4149_);
v_i_4143_ = v___x_4150_;
v_b_4145_ = v___x_4148_;
goto _start;
}
else
{
return v_b_4145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4152_, lean_object* v_i_4153_, lean_object* v_stop_4154_, lean_object* v_b_4155_){
_start:
{
size_t v_i_boxed_4156_; size_t v_stop_boxed_4157_; lean_object* v_res_4158_; 
v_i_boxed_4156_ = lean_unbox_usize(v_i_4153_);
lean_dec(v_i_4153_);
v_stop_boxed_4157_ = lean_unbox_usize(v_stop_4154_);
lean_dec(v_stop_4154_);
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4152_, v_i_boxed_4156_, v_stop_boxed_4157_, v_b_4155_);
lean_dec_ref(v_as_4152_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4159_){
_start:
{
lean_object* v_roots_4160_; lean_object* v_tries_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4184_; 
v_roots_4160_ = lean_ctor_get(v_d_4159_, 0);
v_tries_4161_ = lean_ctor_get(v_d_4159_, 1);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_d_4159_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4163_ = v_d_4159_;
v_isShared_4164_ = v_isSharedCheck_4184_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_tries_4161_);
lean_inc(v_roots_4160_);
lean_dec(v_d_4159_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4184_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___y_4166_; lean_object* v_buckets_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; 
v_buckets_4177_ = lean_ctor_get(v_roots_4160_, 1);
v___x_4178_ = lean_unsigned_to_nat(0u);
v___x_4179_ = lean_array_get_size(v_buckets_4177_);
v___x_4180_ = lean_nat_dec_lt(v___x_4178_, v___x_4179_);
if (v___x_4180_ == 0)
{
v___y_4166_ = v_roots_4160_;
goto v___jp_4165_;
}
else
{
size_t v___x_4181_; size_t v___x_4182_; lean_object* v___x_4183_; 
lean_inc_ref(v_buckets_4177_);
v___x_4181_ = ((size_t)0ULL);
v___x_4182_ = lean_usize_of_nat(v___x_4179_);
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4177_, v___x_4181_, v___x_4182_, v_roots_4160_);
lean_dec_ref(v_buckets_4177_);
v___y_4166_ = v___x_4183_;
goto v___jp_4165_;
}
v___jp_4165_:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; size_t v_sz_4170_; size_t v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4167_ = lean_unsigned_to_nat(1u);
v___x_4168_ = lean_mk_empty_array_with_capacity(v___x_4167_);
lean_dec_ref(v___x_4168_);
v___x_4169_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4170_ = lean_array_size(v_tries_4161_);
v___x_4171_ = ((size_t)0ULL);
v___x_4172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4170_, v___x_4171_, v_tries_4161_);
v___x_4173_ = l_Array_append___redArg(v___x_4169_, v___x_4172_);
lean_dec_ref(v___x_4172_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 1, v___y_4166_);
lean_ctor_set(v___x_4163_, 0, v___x_4173_);
v___x_4175_ = v___x_4163_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v___y_4166_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4185_, lean_object* v_d_4186_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4188_, size_t v_sz_4189_, size_t v_i_4190_, lean_object* v_bs_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4189_, v_i_4190_, v_bs_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4193_, lean_object* v_sz_4194_, lean_object* v_i_4195_, lean_object* v_bs_4196_){
_start:
{
size_t v_sz_boxed_4197_; size_t v_i_boxed_4198_; lean_object* v_res_4199_; 
v_sz_boxed_4197_ = lean_unbox_usize(v_sz_4194_);
lean_dec(v_sz_4194_);
v_i_boxed_4198_ = lean_unbox_usize(v_i_4195_);
lean_dec(v_i_4195_);
v_res_4199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4193_, v_sz_boxed_4197_, v_i_boxed_4198_, v_bs_4196_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4200_, lean_object* v_x_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l_Array_append___redArg(v_x_4201_, v_y_4200_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4203_, lean_object* v_x_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4203_, v_x_4204_);
lean_dec_ref(v_y_4203_);
return v_res_4205_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Array_instInhabited(lean_box(0));
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4207_, lean_object* v_snd_4208_, lean_object* v_x_4209_, lean_object* v_x_4210_){
_start:
{
if (lean_obj_tag(v_x_4210_) == 0)
{
lean_dec_ref(v_snd_4208_);
return v_x_4209_;
}
else
{
lean_object* v_key_4211_; lean_object* v_value_4212_; lean_object* v_tail_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_key_4211_ = lean_ctor_get(v_x_4210_, 0);
lean_inc(v_key_4211_);
v_value_4212_ = lean_ctor_get(v_x_4210_, 1);
lean_inc(v_value_4212_);
v_tail_4213_ = lean_ctor_get(v_x_4210_, 2);
lean_inc(v_tail_4213_);
lean_dec_ref_known(v_x_4210_, 3);
v___x_4214_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4215_ = lean_array_get_borrowed(v___x_4214_, v_tries_4207_, v_value_4212_);
lean_dec(v_value_4212_);
lean_inc_ref(v_snd_4208_);
lean_inc(v___x_4215_);
v___x_4216_ = lean_apply_1(v_snd_4208_, v___x_4215_);
v___x_4217_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4209_, v_key_4211_, v___x_4216_);
v_x_4209_ = v___x_4217_;
v_x_4210_ = v_tail_4213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4219_, lean_object* v_snd_4220_, lean_object* v_x_4221_, lean_object* v_x_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4219_, v_snd_4220_, v_x_4221_, v_x_4222_);
lean_dec_ref(v_tries_4219_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4224_, lean_object* v_snd_4225_, lean_object* v_as_4226_, size_t v_i_4227_, size_t v_stop_4228_, lean_object* v_b_4229_){
_start:
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_usize_dec_eq(v_i_4227_, v_stop_4228_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; lean_object* v___x_4232_; size_t v___x_4233_; size_t v___x_4234_; 
v___x_4231_ = lean_array_uget_borrowed(v_as_4226_, v_i_4227_);
lean_inc(v___x_4231_);
lean_inc_ref(v_snd_4225_);
v___x_4232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4224_, v_snd_4225_, v_b_4229_, v___x_4231_);
v___x_4233_ = ((size_t)1ULL);
v___x_4234_ = lean_usize_add(v_i_4227_, v___x_4233_);
v_i_4227_ = v___x_4234_;
v_b_4229_ = v___x_4232_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4225_);
return v_b_4229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4236_, lean_object* v_snd_4237_, lean_object* v_as_4238_, lean_object* v_i_4239_, lean_object* v_stop_4240_, lean_object* v_b_4241_){
_start:
{
size_t v_i_boxed_4242_; size_t v_stop_boxed_4243_; lean_object* v_res_4244_; 
v_i_boxed_4242_ = lean_unbox_usize(v_i_4239_);
lean_dec(v_i_4239_);
v_stop_boxed_4243_ = lean_unbox_usize(v_stop_4240_);
lean_dec(v_stop_4240_);
v_res_4244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4236_, v_snd_4237_, v_as_4238_, v_i_boxed_4242_, v_stop_boxed_4243_, v_b_4241_);
lean_dec_ref(v_as_4238_);
lean_dec_ref(v_tries_4236_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4247_, lean_object* v_y_4248_){
_start:
{
lean_object* v_fst_4250_; lean_object* v_buckets_4251_; lean_object* v_tries_4252_; lean_object* v_snd_4253_; lean_object* v_roots_4260_; lean_object* v_roots_4261_; lean_object* v_tries_4262_; lean_object* v_size_4263_; lean_object* v_buckets_4264_; lean_object* v_tries_4265_; lean_object* v_size_4266_; lean_object* v_buckets_4267_; uint8_t v___x_4268_; 
v_roots_4260_ = lean_ctor_get(v_y_4248_, 0);
v_roots_4261_ = lean_ctor_get(v_x_4247_, 0);
v_tries_4262_ = lean_ctor_get(v_y_4248_, 1);
v_size_4263_ = lean_ctor_get(v_roots_4260_, 0);
v_buckets_4264_ = lean_ctor_get(v_roots_4260_, 1);
v_tries_4265_ = lean_ctor_get(v_x_4247_, 1);
v_size_4266_ = lean_ctor_get(v_roots_4261_, 0);
v_buckets_4267_ = lean_ctor_get(v_roots_4261_, 1);
v___x_4268_ = lean_nat_dec_le(v_size_4263_, v_size_4266_);
if (v___x_4268_ == 0)
{
lean_object* v___f_4269_; 
lean_inc_ref(v_buckets_4267_);
lean_inc_ref(v_tries_4265_);
lean_dec_ref(v_x_4247_);
v___f_4269_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4250_ = v_y_4248_;
v_buckets_4251_ = v_buckets_4267_;
v_tries_4252_ = v_tries_4265_;
v_snd_4253_ = v___f_4269_;
goto v___jp_4249_;
}
else
{
lean_object* v___f_4270_; 
lean_inc_ref(v_buckets_4264_);
lean_inc_ref(v_tries_4262_);
lean_dec_ref(v_y_4248_);
v___f_4270_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4250_ = v_x_4247_;
v_buckets_4251_ = v_buckets_4264_;
v_tries_4252_ = v_tries_4262_;
v_snd_4253_ = v___f_4270_;
goto v___jp_4249_;
}
v___jp_4249_:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; uint8_t v___x_4256_; 
v___x_4254_ = lean_unsigned_to_nat(0u);
v___x_4255_ = lean_array_get_size(v_buckets_4251_);
v___x_4256_ = lean_nat_dec_lt(v___x_4254_, v___x_4255_);
if (v___x_4256_ == 0)
{
lean_dec_ref(v_tries_4252_);
lean_dec_ref(v_buckets_4251_);
return v_fst_4250_;
}
else
{
size_t v___x_4257_; size_t v___x_4258_; lean_object* v___x_4259_; 
v___x_4257_ = ((size_t)0ULL);
v___x_4258_ = lean_usize_of_nat(v___x_4255_);
lean_inc_ref(v_snd_4253_);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4252_, v_snd_4253_, v_buckets_4251_, v___x_4257_, v___x_4258_, v_fst_4250_);
lean_dec_ref(v_buckets_4251_);
lean_dec_ref(v_tries_4252_);
return v___x_4259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4271_, lean_object* v_x_4272_, lean_object* v_y_4273_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4272_, v_y_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4275_, lean_object* v_tries_4276_, lean_object* v_snd_4277_, lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4276_, v_snd_4277_, v_x_4278_, v_x_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4281_, lean_object* v_tries_4282_, lean_object* v_snd_4283_, lean_object* v_x_4284_, lean_object* v_x_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4281_, v_tries_4282_, v_snd_4283_, v_x_4284_, v_x_4285_);
lean_dec_ref(v_tries_4282_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4287_, lean_object* v_tries_4288_, lean_object* v_snd_4289_, lean_object* v_as_4290_, size_t v_i_4291_, size_t v_stop_4292_, lean_object* v_b_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4288_, v_snd_4289_, v_as_4290_, v_i_4291_, v_stop_4292_, v_b_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4295_, lean_object* v_tries_4296_, lean_object* v_snd_4297_, lean_object* v_as_4298_, lean_object* v_i_4299_, lean_object* v_stop_4300_, lean_object* v_b_4301_){
_start:
{
size_t v_i_boxed_4302_; size_t v_stop_boxed_4303_; lean_object* v_res_4304_; 
v_i_boxed_4302_ = lean_unbox_usize(v_i_4299_);
lean_dec(v_i_4299_);
v_stop_boxed_4303_ = lean_unbox_usize(v_stop_4300_);
lean_dec(v_stop_4300_);
v_res_4304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4295_, v_tries_4296_, v_snd_4297_, v_as_4298_, v_i_boxed_4302_, v_stop_boxed_4303_, v_b_4301_);
lean_dec_ref(v_as_4298_);
lean_dec_ref(v_tries_4296_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4306_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4308_, lean_object* v_value_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4308_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4337_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4318_ = v___x_4315_;
v_isShared_4319_ = v_isSharedCheck_4337_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4315_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4337_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v_fst_4320_; lean_object* v_snd_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4336_; 
v_fst_4320_ = lean_ctor_get(v_a_4316_, 0);
v_snd_4321_ = lean_ctor_get(v_a_4316_, 1);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_a_4316_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4323_ = v_a_4316_;
v_isShared_4324_ = v_isSharedCheck_4336_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_snd_4321_);
lean_inc(v_fst_4320_);
lean_dec(v_a_4316_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4336_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v_lctx_4325_; lean_object* v_localInstances_4326_; lean_object* v___x_4328_; 
v_lctx_4325_ = lean_ctor_get(v_a_4310_, 2);
v_localInstances_4326_ = lean_ctor_get(v_a_4310_, 3);
lean_inc_ref(v_localInstances_4326_);
lean_inc_ref(v_lctx_4325_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 1, v_localInstances_4326_);
lean_ctor_set(v___x_4323_, 0, v_lctx_4325_);
v___x_4328_ = v___x_4323_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_lctx_4325_);
lean_ctor_set(v_reuseFailAlloc_4335_, 1, v_localInstances_4326_);
v___x_4328_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
lean_ctor_set(v___x_4329_, 1, v_value_4309_);
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v_snd_4321_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4331_, 0, v_fst_4320_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 0, v___x_4331_);
v___x_4333_ = v___x_4318_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
lean_dec(v_value_4309_);
v_a_4338_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4315_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4315_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4346_, lean_object* v_value_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4346_, v_value_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4354_, lean_object* v_expr_4355_, lean_object* v_value_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4355_, v_value_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4363_, lean_object* v_expr_4364_, lean_object* v_value_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4363_, v_expr_4364_, v_value_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4372_, lean_object* v_idx_4373_, lean_object* v_value_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v_entry_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4426_; 
v_entry_4380_ = lean_ctor_get(v_e_4372_, 1);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_e_4372_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v_e_4372_, 0);
lean_dec(v_unused_4427_);
v___x_4382_ = v_e_4372_;
v_isShared_4383_ = v_isSharedCheck_4426_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_entry_4380_);
lean_dec(v_e_4372_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4426_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v_snd_4384_; lean_object* v_fst_4385_; lean_object* v_fst_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4424_; 
v_snd_4384_ = lean_ctor_get(v_entry_4380_, 1);
lean_inc(v_snd_4384_);
v_fst_4385_ = lean_ctor_get(v_entry_4380_, 0);
lean_inc(v_fst_4385_);
lean_dec_ref(v_entry_4380_);
v_fst_4386_ = lean_ctor_get(v_snd_4384_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_snd_4384_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v_snd_4384_, 1);
lean_dec(v_unused_4425_);
v___x_4388_ = v_snd_4384_;
v_isShared_4389_ = v_isSharedCheck_4424_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_fst_4386_);
lean_dec(v_snd_4384_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4424_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = l_Lean_instInhabitedExpr;
v___x_4391_ = lean_array_get(v___x_4390_, v_fst_4385_, v_idx_4373_);
lean_dec(v_fst_4385_);
v___x_4392_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4391_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4415_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4395_ = v___x_4392_;
v_isShared_4396_ = v_isSharedCheck_4415_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4415_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v_fst_4397_; lean_object* v_snd_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4414_; 
v_fst_4397_ = lean_ctor_get(v_a_4393_, 0);
v_snd_4398_ = lean_ctor_get(v_a_4393_, 1);
v_isSharedCheck_4414_ = !lean_is_exclusive(v_a_4393_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4400_ = v_a_4393_;
v_isShared_4401_ = v_isSharedCheck_4414_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_snd_4398_);
lean_inc(v_fst_4397_);
lean_dec(v_a_4393_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4414_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 1, v_value_4374_);
lean_ctor_set(v___x_4400_, 0, v_fst_4386_);
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_fst_4386_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_value_4374_);
v___x_4403_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4405_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 1, v___x_4403_);
lean_ctor_set(v___x_4388_, 0, v_snd_4398_);
v___x_4405_ = v___x_4388_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_snd_4398_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
lean_object* v___x_4407_; 
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 1, v___x_4405_);
lean_ctor_set(v___x_4382_, 0, v_fst_4397_);
v___x_4407_ = v___x_4382_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_fst_4397_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4409_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4407_);
v___x_4409_ = v___x_4395_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_del_object(v___x_4388_);
lean_dec(v_fst_4386_);
lean_del_object(v___x_4382_);
lean_dec(v_value_4374_);
v_a_4416_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4392_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4392_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4428_, lean_object* v_idx_4429_, lean_object* v_value_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4428_, v_idx_4429_, v_value_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_);
lean_dec(v_a_4434_);
lean_dec_ref(v_a_4433_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
lean_dec(v_idx_4429_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4437_, lean_object* v_e_4438_, lean_object* v_idx_4439_, lean_object* v_value_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4438_, v_idx_4439_, v_value_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4447_, lean_object* v_e_4448_, lean_object* v_idx_4449_, lean_object* v_value_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4447_, v_e_4448_, v_idx_4449_, v_value_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
lean_dec(v_a_4454_);
lean_dec_ref(v_a_4453_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_idx_4449_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4460_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4461_ = lean_st_mk_ref(v___x_4460_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4463_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4464_; 
v___x_4464_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4464_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
return v___x_4466_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
return v___x_4468_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4470_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
lean_ctor_set(v___x_4470_, 2, v___x_4469_);
lean_ctor_set(v___x_4470_, 3, v___x_4469_);
lean_ctor_set(v___x_4470_, 4, v___x_4469_);
lean_ctor_set(v___x_4470_, 5, v___x_4469_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4471_){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4473_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4474_, 0, v_ngen_4471_);
lean_ctor_set(v___x_4474_, 1, v___x_4472_);
lean_ctor_set(v___x_4474_, 2, v___x_4473_);
return v___x_4474_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4475_, lean_object* v_declName_4476_){
_start:
{
uint8_t v___x_4477_; 
v___x_4477_ = l_Lean_isPrivateName(v_declName_4476_);
if (v___x_4477_ == 0)
{
return v___x_4477_;
}
else
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4475_, v_declName_4476_);
if (lean_obj_tag(v___x_4478_) == 0)
{
return v___x_4477_;
}
else
{
lean_object* v_val_4479_; lean_object* v___x_4480_; uint8_t v_isModule_4481_; lean_object* v_modules_4482_; uint8_t v___x_4483_; 
v_val_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_val_4479_);
lean_dec_ref_known(v___x_4478_, 1);
v___x_4480_ = l_Lean_Environment_header(v_env_4475_);
v_isModule_4481_ = lean_ctor_get_uint8(v___x_4480_, sizeof(void*)*7 + 4);
v_modules_4482_ = lean_ctor_get(v___x_4480_, 3);
lean_inc_ref(v_modules_4482_);
lean_dec_ref(v___x_4480_);
v___x_4483_ = 0;
if (v_isModule_4481_ == 0)
{
lean_dec_ref(v_modules_4482_);
lean_dec(v_val_4479_);
return v___x_4483_;
}
else
{
lean_object* v___x_4484_; uint8_t v___x_4485_; 
v___x_4484_ = lean_array_get_size(v_modules_4482_);
v___x_4485_ = lean_nat_dec_lt(v_val_4479_, v___x_4484_);
if (v___x_4485_ == 0)
{
lean_dec_ref(v_modules_4482_);
lean_dec(v_val_4479_);
return v___x_4483_;
}
else
{
lean_object* v___x_4486_; lean_object* v_toImport_4487_; uint8_t v_importAll_4488_; 
v___x_4486_ = lean_array_fget(v_modules_4482_, v_val_4479_);
lean_dec(v_val_4479_);
lean_dec_ref(v_modules_4482_);
v_toImport_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc_ref(v_toImport_4487_);
lean_dec(v___x_4486_);
v_importAll_4488_ = lean_ctor_get_uint8(v_toImport_4487_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4487_);
return v_importAll_4488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4489_, lean_object* v_declName_4490_){
_start:
{
uint8_t v_res_4491_; lean_object* v_r_4492_; 
v_res_4491_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4489_, v_declName_4490_);
lean_dec(v_declName_4490_);
lean_dec_ref(v_env_4489_);
v_r_4492_ = lean_box(v_res_4491_);
return v_r_4492_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4498_, lean_object* v_declName_4499_){
_start:
{
uint8_t v___x_4500_; 
lean_inc(v_declName_4499_);
lean_inc_ref(v_env_4498_);
v___x_4500_ = l_Lean_Meta_allowCompletion(v_env_4498_, v_declName_4499_);
if (v___x_4500_ == 0)
{
uint8_t v___x_4501_; 
lean_dec(v_declName_4499_);
lean_dec_ref(v_env_4498_);
v___x_4501_ = 1;
return v___x_4501_;
}
else
{
lean_object* v___x_4502_; uint8_t v___x_4503_; uint8_t v___y_4513_; 
v___x_4502_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4503_ = lean_name_eq(v_declName_4499_, v___x_4502_);
if (v___x_4503_ == 0)
{
uint8_t v___x_4514_; 
lean_inc(v_declName_4499_);
v___x_4514_ = l_Lean_Name_isInternalDetail(v_declName_4499_);
if (v___x_4514_ == 0)
{
lean_dec_ref(v_env_4498_);
v___y_4513_ = v___x_4514_;
goto v___jp_4512_;
}
else
{
uint8_t v___x_4515_; 
v___x_4515_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4498_, v_declName_4499_);
lean_dec_ref(v_env_4498_);
if (v___x_4515_ == 0)
{
v___y_4513_ = v___x_4514_;
goto v___jp_4512_;
}
else
{
goto v___jp_4508_;
}
}
}
else
{
lean_dec(v_declName_4499_);
lean_dec_ref(v_env_4498_);
return v___x_4503_;
}
v___jp_4504_:
{
if (lean_obj_tag(v_declName_4499_) == 1)
{
lean_object* v_str_4505_; lean_object* v___x_4506_; uint8_t v___x_4507_; 
v_str_4505_ = lean_ctor_get(v_declName_4499_, 1);
lean_inc_ref(v_str_4505_);
lean_dec_ref_known(v_declName_4499_, 2);
v___x_4506_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4507_ = lean_string_dec_eq(v_str_4505_, v___x_4506_);
lean_dec_ref(v_str_4505_);
return v___x_4507_;
}
else
{
lean_dec(v_declName_4499_);
return v___x_4503_;
}
}
v___jp_4508_:
{
if (lean_obj_tag(v_declName_4499_) == 1)
{
lean_object* v_str_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v_str_4509_ = lean_ctor_get(v_declName_4499_, 1);
v___x_4510_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4511_ = lean_string_dec_eq(v_str_4509_, v___x_4510_);
if (v___x_4511_ == 0)
{
goto v___jp_4504_;
}
else
{
lean_dec_ref_known(v_declName_4499_, 2);
return v___x_4511_;
}
}
else
{
goto v___jp_4504_;
}
}
v___jp_4512_:
{
if (v___y_4513_ == 0)
{
goto v___jp_4508_;
}
else
{
lean_dec(v_declName_4499_);
return v___y_4513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4516_, lean_object* v_declName_4517_){
_start:
{
uint8_t v_res_4518_; lean_object* v_r_4519_; 
v_res_4518_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4516_, v_declName_4517_);
v_r_4519_ = lean_box(v_res_4518_);
return v_r_4519_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4520_, lean_object* v_opt_4521_){
_start:
{
lean_object* v_name_4522_; lean_object* v_defValue_4523_; lean_object* v_map_4524_; lean_object* v___x_4525_; 
v_name_4522_ = lean_ctor_get(v_opt_4521_, 0);
v_defValue_4523_ = lean_ctor_get(v_opt_4521_, 1);
v_map_4524_ = lean_ctor_get(v_opts_4520_, 0);
v___x_4525_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4524_, v_name_4522_);
if (lean_obj_tag(v___x_4525_) == 0)
{
uint8_t v___x_4526_; 
v___x_4526_ = lean_unbox(v_defValue_4523_);
return v___x_4526_;
}
else
{
lean_object* v_val_4527_; 
v_val_4527_ = lean_ctor_get(v___x_4525_, 0);
lean_inc(v_val_4527_);
lean_dec_ref_known(v___x_4525_, 1);
if (lean_obj_tag(v_val_4527_) == 1)
{
uint8_t v_v_4528_; 
v_v_4528_ = lean_ctor_get_uint8(v_val_4527_, 0);
lean_dec_ref_known(v_val_4527_, 0);
return v_v_4528_;
}
else
{
uint8_t v___x_4529_; 
lean_dec(v_val_4527_);
v___x_4529_ = lean_unbox(v_defValue_4523_);
return v___x_4529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4530_, lean_object* v_opt_4531_){
_start:
{
uint8_t v_res_4532_; lean_object* v_r_4533_; 
v_res_4532_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4530_, v_opt_4531_);
lean_dec_ref(v_opt_4531_);
lean_dec_ref(v_opts_4530_);
v_r_4533_ = lean_box(v_res_4532_);
return v_r_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4534_, lean_object* v_opt_4535_){
_start:
{
lean_object* v_name_4536_; lean_object* v_defValue_4537_; lean_object* v_map_4538_; lean_object* v___x_4539_; 
v_name_4536_ = lean_ctor_get(v_opt_4535_, 0);
v_defValue_4537_ = lean_ctor_get(v_opt_4535_, 1);
v_map_4538_ = lean_ctor_get(v_opts_4534_, 0);
v___x_4539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4538_, v_name_4536_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_inc(v_defValue_4537_);
return v_defValue_4537_;
}
else
{
lean_object* v_val_4540_; 
v_val_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_val_4540_);
lean_dec_ref_known(v___x_4539_, 1);
if (lean_obj_tag(v_val_4540_) == 3)
{
lean_object* v_v_4541_; 
v_v_4541_ = lean_ctor_get(v_val_4540_, 0);
lean_inc(v_v_4541_);
lean_dec_ref_known(v_val_4540_, 1);
return v_v_4541_;
}
else
{
lean_dec(v_val_4540_);
lean_inc(v_defValue_4537_);
return v_defValue_4537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4542_, lean_object* v_opt_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4542_, v_opt_4543_);
lean_dec_ref(v_opt_4543_);
lean_dec_ref(v_opts_4542_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4545_, size_t v_i_4546_, size_t v_stop_4547_, lean_object* v_b_4548_){
_start:
{
uint8_t v___x_4549_; 
v___x_4549_ = lean_usize_dec_eq(v_i_4546_, v_stop_4547_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; lean_object* v_key_4551_; lean_object* v_entry_4552_; lean_object* v___x_4553_; size_t v___x_4554_; size_t v___x_4555_; 
v___x_4550_ = lean_array_uget_borrowed(v_as_4545_, v_i_4546_);
v_key_4551_ = lean_ctor_get(v___x_4550_, 0);
v_entry_4552_ = lean_ctor_get(v___x_4550_, 1);
lean_inc_ref(v_entry_4552_);
lean_inc(v_key_4551_);
v___x_4553_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4548_, v_key_4551_, v_entry_4552_);
v___x_4554_ = ((size_t)1ULL);
v___x_4555_ = lean_usize_add(v_i_4546_, v___x_4554_);
v_i_4546_ = v___x_4555_;
v_b_4548_ = v___x_4553_;
goto _start;
}
else
{
return v_b_4548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4557_, lean_object* v_i_4558_, lean_object* v_stop_4559_, lean_object* v_b_4560_){
_start:
{
size_t v_i_boxed_4561_; size_t v_stop_boxed_4562_; lean_object* v_res_4563_; 
v_i_boxed_4561_ = lean_unbox_usize(v_i_4558_);
lean_dec(v_i_4558_);
v_stop_boxed_4562_ = lean_unbox_usize(v_stop_4559_);
lean_dec(v_stop_4559_);
v_res_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4557_, v_i_boxed_4561_, v_stop_boxed_4562_, v_b_4560_);
lean_dec_ref(v_as_4557_);
return v_res_4563_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4564_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4565_);
return v___x_4566_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4567_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4568_ = lean_unsigned_to_nat(0u);
v___x_4569_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
lean_ctor_set(v___x_4569_, 2, v___x_4568_);
lean_ctor_set(v___x_4569_, 3, v___x_4568_);
lean_ctor_set(v___x_4569_, 4, v___x_4567_);
lean_ctor_set(v___x_4569_, 5, v___x_4567_);
lean_ctor_set(v___x_4569_, 6, v___x_4567_);
lean_ctor_set(v___x_4569_, 7, v___x_4567_);
lean_ctor_set(v___x_4569_, 8, v___x_4567_);
lean_ctor_set(v___x_4569_, 9, v___x_4567_);
lean_ctor_set(v___x_4569_, 10, v___x_4567_);
return v___x_4569_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = lean_unsigned_to_nat(32u);
v___x_4571_ = lean_mk_empty_array_with_capacity(v___x_4570_);
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
return v___x_4572_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4573_ = ((size_t)5ULL);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = lean_unsigned_to_nat(32u);
v___x_4576_ = lean_mk_empty_array_with_capacity(v___x_4575_);
v___x_4577_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4578_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v___x_4576_);
lean_ctor_set(v___x_4578_, 2, v___x_4574_);
lean_ctor_set(v___x_4578_, 3, v___x_4574_);
lean_ctor_set_usize(v___x_4578_, 4, v___x_4573_);
return v___x_4578_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
lean_ctor_set(v___x_4580_, 2, v___x_4579_);
lean_ctor_set(v___x_4580_, 3, v___x_4579_);
lean_ctor_set(v___x_4580_, 4, v___x_4579_);
return v___x_4580_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4581_ = lean_box(1);
v___x_4582_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4583_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
lean_ctor_set(v___x_4584_, 1, v___x_4582_);
lean_ctor_set(v___x_4584_, 2, v___x_4581_);
return v___x_4584_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4587_ = lean_unsigned_to_nat(1u);
v___x_4588_ = l_Lean_firstFrontendMacroScope;
v___x_4589_ = lean_nat_add(v___x_4588_, v___x_4587_);
return v___x_4589_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4594_; uint64_t v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4595_ = 0ULL;
v___x_4596_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4596_, 0, v___x_4594_);
lean_ctor_set_uint64(v___x_4596_, sizeof(void*)*1, v___x_4595_);
return v___x_4596_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4597_ = l_Lean_NameSet_empty;
v___x_4598_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
lean_ctor_set(v___x_4599_, 2, v___x_4597_);
return v___x_4599_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; uint8_t v___x_4602_; lean_object* v___x_4603_; 
v___x_4600_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4601_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4602_ = 1;
v___x_4603_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4603_, 0, v___x_4601_);
lean_ctor_set(v___x_4603_, 1, v___x_4601_);
lean_ctor_set(v___x_4603_, 2, v___x_4600_);
lean_ctor_set_uint8(v___x_4603_, sizeof(void*)*3, v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4606_, lean_object* v_env_4607_, lean_object* v_modName_4608_, lean_object* v_d_4609_, lean_object* v_cacheRef_4610_, lean_object* v_tree_4611_, lean_object* v_act_4612_, lean_object* v_c_4613_){
_start:
{
uint8_t v___x_4615_; 
lean_inc_ref(v_c_4613_);
v___x_4615_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4613_);
if (v___x_4615_ == 0)
{
lean_object* v_name_4616_; uint8_t v___x_4617_; 
v_name_4616_ = lean_ctor_get(v_c_4613_, 0);
lean_inc_n(v_name_4616_, 2);
lean_inc_ref(v_env_4607_);
v___x_4617_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4607_, v_name_4616_);
if (v___x_4617_ == 0)
{
lean_object* v___x_4618_; lean_object* v_ngen_4619_; lean_object* v_core_4620_; lean_object* v_meta_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4755_; 
v___x_4618_ = lean_st_ref_get(v_cacheRef_4610_);
v_ngen_4619_ = lean_ctor_get(v___x_4618_, 0);
v_core_4620_ = lean_ctor_get(v___x_4618_, 1);
v_meta_4621_ = lean_ctor_get(v___x_4618_, 2);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4623_ = v___x_4618_;
v_isShared_4624_ = v_isSharedCheck_4755_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_meta_4621_);
lean_inc(v_core_4620_);
lean_inc(v_ngen_4619_);
lean_dec(v___x_4618_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4755_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; uint8_t v___x_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v_fileName_4653_; lean_object* v_fileMap_4654_; lean_object* v_options_4655_; lean_object* v_currRecDepth_4656_; lean_object* v_maxRecDepth_4657_; lean_object* v_ref_4658_; lean_object* v_currNamespace_4659_; lean_object* v_openDecls_4660_; lean_object* v_initHeartbeats_4661_; lean_object* v_maxHeartbeats_4662_; lean_object* v_quotContext_4663_; lean_object* v_currMacroScope_4664_; uint8_t v_diag_4665_; lean_object* v_cancelTk_x3f_4666_; uint8_t v_suppressElabErrors_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4753_; 
v___x_4625_ = lean_unsigned_to_nat(0u);
v___x_4626_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4627_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4628_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4619_);
v___x_4629_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4619_);
v___x_4630_ = lean_st_ref_swap(v_cacheRef_4610_, v___x_4629_);
lean_dec(v___x_4630_);
v___x_4631_ = lean_box(1);
v___x_4632_ = 1;
v___x_4633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4626_);
lean_ctor_set(v___x_4633_, 1, v_meta_4621_);
lean_ctor_set(v___x_4633_, 2, v___x_4631_);
lean_ctor_set(v___x_4633_, 3, v___x_4627_);
lean_ctor_set(v___x_4633_, 4, v___x_4628_);
v___x_4634_ = 2;
v___x_4635_ = 0;
v___x_4636_ = 2;
v___x_4637_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4637_, 0, v___x_4617_);
lean_ctor_set_uint8(v___x_4637_, 1, v___x_4617_);
lean_ctor_set_uint8(v___x_4637_, 2, v___x_4617_);
lean_ctor_set_uint8(v___x_4637_, 3, v___x_4617_);
lean_ctor_set_uint8(v___x_4637_, 4, v___x_4617_);
lean_ctor_set_uint8(v___x_4637_, 5, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 6, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 7, v___x_4617_);
lean_ctor_set_uint8(v___x_4637_, 8, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 9, v___x_4634_);
lean_ctor_set_uint8(v___x_4637_, 10, v___x_4635_);
lean_ctor_set_uint8(v___x_4637_, 11, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 12, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 13, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 14, v___x_4636_);
lean_ctor_set_uint8(v___x_4637_, 15, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 16, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 17, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 18, v___x_4632_);
lean_ctor_set_uint8(v___x_4637_, 19, v___x_4617_);
v___x_4638_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4637_);
v___x_4639_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4640_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4641_ = lean_box(0);
v___x_4642_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4642_, 0, v___x_4638_);
lean_ctor_set(v___x_4642_, 1, v___x_4631_);
lean_ctor_set(v___x_4642_, 2, v___x_4639_);
lean_ctor_set(v___x_4642_, 3, v___x_4640_);
lean_ctor_set(v___x_4642_, 4, v___x_4641_);
lean_ctor_set(v___x_4642_, 5, v___x_4625_);
lean_ctor_set(v___x_4642_, 6, v___x_4641_);
lean_ctor_set_uint8(v___x_4642_, sizeof(void*)*7, v___x_4617_);
lean_ctor_set_uint8(v___x_4642_, sizeof(void*)*7 + 1, v___x_4617_);
lean_ctor_set_uint8(v___x_4642_, sizeof(void*)*7 + 2, v___x_4617_);
lean_ctor_set_uint8(v___x_4642_, sizeof(void*)*7 + 3, v___x_4632_);
v___x_4643_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4644_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4645_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4646_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4647_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4648_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4648_, 0, v_env_4607_);
lean_ctor_set(v___x_4648_, 1, v___x_4643_);
lean_ctor_set(v___x_4648_, 2, v_ngen_4619_);
lean_ctor_set(v___x_4648_, 3, v___x_4644_);
lean_ctor_set(v___x_4648_, 4, v___x_4645_);
lean_ctor_set(v___x_4648_, 5, v_core_4620_);
lean_ctor_set(v___x_4648_, 6, v___x_4646_);
lean_ctor_set(v___x_4648_, 7, v___x_4647_);
lean_ctor_set(v___x_4648_, 8, v___x_4640_);
v___x_4649_ = lean_st_mk_ref(v___x_4648_);
v___x_4650_ = l_Lean_inheritedTraceOptions;
v___x_4651_ = lean_st_ref_get(v___x_4650_);
v___x_4652_ = lean_st_ref_get(v___x_4649_);
v_fileName_4653_ = lean_ctor_get(v_cctx_4606_, 0);
v_fileMap_4654_ = lean_ctor_get(v_cctx_4606_, 1);
v_options_4655_ = lean_ctor_get(v_cctx_4606_, 2);
v_currRecDepth_4656_ = lean_ctor_get(v_cctx_4606_, 3);
v_maxRecDepth_4657_ = lean_ctor_get(v_cctx_4606_, 4);
v_ref_4658_ = lean_ctor_get(v_cctx_4606_, 5);
v_currNamespace_4659_ = lean_ctor_get(v_cctx_4606_, 6);
v_openDecls_4660_ = lean_ctor_get(v_cctx_4606_, 7);
v_initHeartbeats_4661_ = lean_ctor_get(v_cctx_4606_, 8);
v_maxHeartbeats_4662_ = lean_ctor_get(v_cctx_4606_, 9);
v_quotContext_4663_ = lean_ctor_get(v_cctx_4606_, 10);
v_currMacroScope_4664_ = lean_ctor_get(v_cctx_4606_, 11);
v_diag_4665_ = lean_ctor_get_uint8(v_cctx_4606_, sizeof(void*)*14);
v_cancelTk_x3f_4666_ = lean_ctor_get(v_cctx_4606_, 12);
v_suppressElabErrors_4667_ = lean_ctor_get_uint8(v_cctx_4606_, sizeof(void*)*14 + 1);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_cctx_4606_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v_cctx_4606_, 13);
lean_dec(v_unused_4754_);
v___x_4669_ = v_cctx_4606_;
v_isShared_4670_ = v_isSharedCheck_4753_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_cancelTk_x3f_4666_);
lean_inc(v_currMacroScope_4664_);
lean_inc(v_quotContext_4663_);
lean_inc(v_maxHeartbeats_4662_);
lean_inc(v_initHeartbeats_4661_);
lean_inc(v_openDecls_4660_);
lean_inc(v_currNamespace_4659_);
lean_inc(v_ref_4658_);
lean_inc(v_maxRecDepth_4657_);
lean_inc(v_currRecDepth_4656_);
lean_inc(v_options_4655_);
lean_inc(v_fileMap_4654_);
lean_inc(v_fileName_4653_);
lean_dec(v_cctx_4606_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4753_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v_env_4671_; lean_object* v___x_4673_; 
v_env_4671_ = lean_ctor_get(v___x_4652_, 0);
lean_inc_ref(v_env_4671_);
lean_dec(v___x_4652_);
lean_inc_ref(v_options_4655_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 13, v___x_4651_);
v___x_4673_ = v___x_4669_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_fileName_4653_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_fileMap_4654_);
lean_ctor_set(v_reuseFailAlloc_4752_, 2, v_options_4655_);
lean_ctor_set(v_reuseFailAlloc_4752_, 3, v_currRecDepth_4656_);
lean_ctor_set(v_reuseFailAlloc_4752_, 4, v_maxRecDepth_4657_);
lean_ctor_set(v_reuseFailAlloc_4752_, 5, v_ref_4658_);
lean_ctor_set(v_reuseFailAlloc_4752_, 6, v_currNamespace_4659_);
lean_ctor_set(v_reuseFailAlloc_4752_, 7, v_openDecls_4660_);
lean_ctor_set(v_reuseFailAlloc_4752_, 8, v_initHeartbeats_4661_);
lean_ctor_set(v_reuseFailAlloc_4752_, 9, v_maxHeartbeats_4662_);
lean_ctor_set(v_reuseFailAlloc_4752_, 10, v_quotContext_4663_);
lean_ctor_set(v_reuseFailAlloc_4752_, 11, v_currMacroScope_4664_);
lean_ctor_set(v_reuseFailAlloc_4752_, 12, v_cancelTk_x3f_4666_);
lean_ctor_set(v_reuseFailAlloc_4752_, 13, v___x_4651_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, sizeof(void*)*14, v_diag_4665_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, sizeof(void*)*14 + 1, v_suppressElabErrors_4667_);
v___x_4673_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4674_; uint8_t v___x_4675_; lean_object* v___y_4677_; lean_object* v___y_4678_; uint8_t v___y_4730_; uint8_t v___x_4751_; 
v___x_4674_ = l_Lean_diagnostics;
v___x_4675_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4655_, v___x_4674_);
v___x_4751_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4671_);
lean_dec_ref(v_env_4671_);
if (v___x_4675_ == 0)
{
if (v___x_4751_ == 0)
{
lean_inc(v___x_4649_);
v___y_4677_ = v___x_4673_;
v___y_4678_ = v___x_4649_;
goto v___jp_4676_;
}
else
{
v___y_4730_ = v___x_4675_;
goto v___jp_4729_;
}
}
else
{
v___y_4730_ = v___x_4751_;
goto v___jp_4729_;
}
v___jp_4676_:
{
lean_object* v___x_4679_; lean_object* v_fileName_4680_; lean_object* v_fileMap_4681_; lean_object* v_currRecDepth_4682_; lean_object* v_ref_4683_; lean_object* v_currNamespace_4684_; lean_object* v_openDecls_4685_; lean_object* v_initHeartbeats_4686_; lean_object* v_maxHeartbeats_4687_; lean_object* v_quotContext_4688_; lean_object* v_currMacroScope_4689_; lean_object* v_cancelTk_x3f_4690_; uint8_t v_suppressElabErrors_4691_; lean_object* v_inheritedTraceOptions_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4726_; 
v___x_4679_ = lean_st_mk_ref(v___x_4633_);
v_fileName_4680_ = lean_ctor_get(v___y_4677_, 0);
v_fileMap_4681_ = lean_ctor_get(v___y_4677_, 1);
v_currRecDepth_4682_ = lean_ctor_get(v___y_4677_, 3);
v_ref_4683_ = lean_ctor_get(v___y_4677_, 5);
v_currNamespace_4684_ = lean_ctor_get(v___y_4677_, 6);
v_openDecls_4685_ = lean_ctor_get(v___y_4677_, 7);
v_initHeartbeats_4686_ = lean_ctor_get(v___y_4677_, 8);
v_maxHeartbeats_4687_ = lean_ctor_get(v___y_4677_, 9);
v_quotContext_4688_ = lean_ctor_get(v___y_4677_, 10);
v_currMacroScope_4689_ = lean_ctor_get(v___y_4677_, 11);
v_cancelTk_x3f_4690_ = lean_ctor_get(v___y_4677_, 12);
v_suppressElabErrors_4691_ = lean_ctor_get_uint8(v___y_4677_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4692_ = lean_ctor_get(v___y_4677_, 13);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___y_4677_);
if (v_isSharedCheck_4726_ == 0)
{
lean_object* v_unused_4727_; lean_object* v_unused_4728_; 
v_unused_4727_ = lean_ctor_get(v___y_4677_, 4);
lean_dec(v_unused_4727_);
v_unused_4728_ = lean_ctor_get(v___y_4677_, 2);
lean_dec(v_unused_4728_);
v___x_4694_ = v___y_4677_;
v_isShared_4695_ = v_isSharedCheck_4726_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_inheritedTraceOptions_4692_);
lean_inc(v_cancelTk_x3f_4690_);
lean_inc(v_currMacroScope_4689_);
lean_inc(v_quotContext_4688_);
lean_inc(v_maxHeartbeats_4687_);
lean_inc(v_initHeartbeats_4686_);
lean_inc(v_openDecls_4685_);
lean_inc(v_currNamespace_4684_);
lean_inc(v_ref_4683_);
lean_inc(v_currRecDepth_4682_);
lean_inc(v_fileMap_4681_);
lean_inc(v_fileName_4680_);
lean_dec(v___y_4677_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4726_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4696_ = l_Lean_maxRecDepth;
v___x_4697_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4655_, v___x_4696_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 4, v___x_4697_);
lean_ctor_set(v___x_4694_, 2, v_options_4655_);
v___x_4699_ = v___x_4694_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_fileName_4680_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_fileMap_4681_);
lean_ctor_set(v_reuseFailAlloc_4725_, 2, v_options_4655_);
lean_ctor_set(v_reuseFailAlloc_4725_, 3, v_currRecDepth_4682_);
lean_ctor_set(v_reuseFailAlloc_4725_, 4, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4725_, 5, v_ref_4683_);
lean_ctor_set(v_reuseFailAlloc_4725_, 6, v_currNamespace_4684_);
lean_ctor_set(v_reuseFailAlloc_4725_, 7, v_openDecls_4685_);
lean_ctor_set(v_reuseFailAlloc_4725_, 8, v_initHeartbeats_4686_);
lean_ctor_set(v_reuseFailAlloc_4725_, 9, v_maxHeartbeats_4687_);
lean_ctor_set(v_reuseFailAlloc_4725_, 10, v_quotContext_4688_);
lean_ctor_set(v_reuseFailAlloc_4725_, 11, v_currMacroScope_4689_);
lean_ctor_set(v_reuseFailAlloc_4725_, 12, v_cancelTk_x3f_4690_);
lean_ctor_set(v_reuseFailAlloc_4725_, 13, v_inheritedTraceOptions_4692_);
lean_ctor_set_uint8(v_reuseFailAlloc_4725_, sizeof(void*)*14 + 1, v_suppressElabErrors_4691_);
v___x_4699_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; 
lean_ctor_set_uint8(v___x_4699_, sizeof(void*)*14, v___x_4675_);
lean_inc(v___x_4679_);
lean_inc(v_name_4616_);
v___x_4700_ = lean_apply_7(v_act_4612_, v_name_4616_, v_c_4613_, v___x_4642_, v___x_4679_, v___x_4699_, v___y_4678_, lean_box(0));
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v_ngen_4704_; lean_object* v_cache_4705_; lean_object* v_cache_4706_; lean_object* v___x_4708_; 
lean_dec(v_name_4616_);
lean_dec(v_modName_4608_);
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
v___x_4702_ = lean_st_ref_get(v___x_4679_);
lean_dec(v___x_4679_);
v___x_4703_ = lean_st_ref_get(v___x_4649_);
lean_dec(v___x_4649_);
v_ngen_4704_ = lean_ctor_get(v___x_4703_, 2);
lean_inc_ref(v_ngen_4704_);
v_cache_4705_ = lean_ctor_get(v___x_4703_, 5);
lean_inc_ref(v_cache_4705_);
lean_dec(v___x_4703_);
v_cache_4706_ = lean_ctor_get(v___x_4702_, 1);
lean_inc_ref(v_cache_4706_);
lean_dec(v___x_4702_);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 2, v_cache_4706_);
lean_ctor_set(v___x_4623_, 1, v_cache_4705_);
lean_ctor_set(v___x_4623_, 0, v_ngen_4704_);
v___x_4708_ = v___x_4623_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_ngen_4704_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_cache_4705_);
lean_ctor_set(v_reuseFailAlloc_4719_, 2, v_cache_4706_);
v___x_4708_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; 
v___x_4709_ = lean_st_ref_swap(v_cacheRef_4610_, v___x_4708_);
lean_dec(v___x_4709_);
v___x_4710_ = lean_array_get_size(v_a_4701_);
v___x_4711_ = lean_nat_dec_lt(v___x_4625_, v___x_4710_);
if (v___x_4711_ == 0)
{
lean_dec(v_a_4701_);
return v_tree_4611_;
}
else
{
uint8_t v___x_4712_; 
v___x_4712_ = lean_nat_dec_le(v___x_4710_, v___x_4710_);
if (v___x_4712_ == 0)
{
if (v___x_4711_ == 0)
{
lean_dec(v_a_4701_);
return v_tree_4611_;
}
else
{
size_t v___x_4713_; size_t v___x_4714_; lean_object* v___x_4715_; 
v___x_4713_ = ((size_t)0ULL);
v___x_4714_ = lean_usize_of_nat(v___x_4710_);
v___x_4715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4701_, v___x_4713_, v___x_4714_, v_tree_4611_);
lean_dec(v_a_4701_);
return v___x_4715_;
}
}
else
{
size_t v___x_4716_; size_t v___x_4717_; lean_object* v___x_4718_; 
v___x_4716_ = ((size_t)0ULL);
v___x_4717_ = lean_usize_of_nat(v___x_4710_);
v___x_4718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4701_, v___x_4716_, v___x_4717_, v_tree_4611_);
lean_dec(v_a_4701_);
return v___x_4718_;
}
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
lean_dec(v___x_4679_);
lean_dec(v___x_4649_);
lean_del_object(v___x_4623_);
v_a_4720_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4720_);
lean_dec_ref_known(v___x_4700_, 1);
v___x_4721_ = lean_st_ref_take(v_d_4609_);
v___x_4722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4722_, 0, v_modName_4608_);
lean_ctor_set(v___x_4722_, 1, v_name_4616_);
lean_ctor_set(v___x_4722_, 2, v_a_4720_);
v___x_4723_ = lean_array_push(v___x_4721_, v___x_4722_);
v___x_4724_ = lean_st_ref_put(v_d_4609_, v___x_4723_);
return v_tree_4611_;
}
}
}
}
v___jp_4729_:
{
if (v___y_4730_ == 0)
{
lean_object* v___x_4731_; lean_object* v_env_4732_; lean_object* v_nextMacroScope_4733_; lean_object* v_ngen_4734_; lean_object* v_auxDeclNGen_4735_; lean_object* v_traceState_4736_; lean_object* v_messages_4737_; lean_object* v_infoState_4738_; lean_object* v_snapshotTasks_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4749_; 
v___x_4731_ = lean_st_ref_take(v___x_4649_);
v_env_4732_ = lean_ctor_get(v___x_4731_, 0);
v_nextMacroScope_4733_ = lean_ctor_get(v___x_4731_, 1);
v_ngen_4734_ = lean_ctor_get(v___x_4731_, 2);
v_auxDeclNGen_4735_ = lean_ctor_get(v___x_4731_, 3);
v_traceState_4736_ = lean_ctor_get(v___x_4731_, 4);
v_messages_4737_ = lean_ctor_get(v___x_4731_, 6);
v_infoState_4738_ = lean_ctor_get(v___x_4731_, 7);
v_snapshotTasks_4739_ = lean_ctor_get(v___x_4731_, 8);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4749_ == 0)
{
lean_object* v_unused_4750_; 
v_unused_4750_ = lean_ctor_get(v___x_4731_, 5);
lean_dec(v_unused_4750_);
v___x_4741_ = v___x_4731_;
v_isShared_4742_ = v_isSharedCheck_4749_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_snapshotTasks_4739_);
lean_inc(v_infoState_4738_);
lean_inc(v_messages_4737_);
lean_inc(v_traceState_4736_);
lean_inc(v_auxDeclNGen_4735_);
lean_inc(v_ngen_4734_);
lean_inc(v_nextMacroScope_4733_);
lean_inc(v_env_4732_);
lean_dec(v___x_4731_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4749_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
v___x_4743_ = l_Lean_Kernel_enableDiag(v_env_4732_, v___x_4675_);
v___x_4744_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 5, v___x_4744_);
lean_ctor_set(v___x_4741_, 0, v___x_4743_);
v___x_4746_ = v___x_4741_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v_nextMacroScope_4733_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_ngen_4734_);
lean_ctor_set(v_reuseFailAlloc_4748_, 3, v_auxDeclNGen_4735_);
lean_ctor_set(v_reuseFailAlloc_4748_, 4, v_traceState_4736_);
lean_ctor_set(v_reuseFailAlloc_4748_, 5, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4748_, 6, v_messages_4737_);
lean_ctor_set(v_reuseFailAlloc_4748_, 7, v_infoState_4738_);
lean_ctor_set(v_reuseFailAlloc_4748_, 8, v_snapshotTasks_4739_);
v___x_4746_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4747_; 
v___x_4747_ = lean_st_ref_put(v___x_4649_, v___x_4746_);
lean_inc(v___x_4649_);
v___y_4677_ = v___x_4673_;
v___y_4678_ = v___x_4649_;
goto v___jp_4676_;
}
}
}
else
{
lean_inc(v___x_4649_);
v___y_4677_ = v___x_4673_;
v___y_4678_ = v___x_4649_;
goto v___jp_4676_;
}
}
}
}
}
}
else
{
lean_dec(v_name_4616_);
lean_dec_ref(v_c_4613_);
lean_dec_ref(v_act_4612_);
lean_dec(v_modName_4608_);
lean_dec_ref(v_env_4607_);
lean_dec_ref(v_cctx_4606_);
return v_tree_4611_;
}
}
else
{
lean_dec_ref(v_c_4613_);
lean_dec_ref(v_act_4612_);
lean_dec(v_modName_4608_);
lean_dec_ref(v_env_4607_);
lean_dec_ref(v_cctx_4606_);
return v_tree_4611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4756_, lean_object* v_env_4757_, lean_object* v_modName_4758_, lean_object* v_d_4759_, lean_object* v_cacheRef_4760_, lean_object* v_tree_4761_, lean_object* v_act_4762_, lean_object* v_c_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4756_, v_env_4757_, v_modName_4758_, v_d_4759_, v_cacheRef_4760_, v_tree_4761_, v_act_4762_, v_c_4763_);
lean_dec(v_cacheRef_4760_);
lean_dec(v_d_4759_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4766_, lean_object* v_cctx_4767_, lean_object* v_env_4768_, lean_object* v_modName_4769_, lean_object* v_d_4770_, lean_object* v_cacheRef_4771_, lean_object* v_tree_4772_, lean_object* v_act_4773_, lean_object* v_c_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4767_, v_env_4768_, v_modName_4769_, v_d_4770_, v_cacheRef_4771_, v_tree_4772_, v_act_4773_, v_c_4774_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4777_, lean_object* v_cctx_4778_, lean_object* v_env_4779_, lean_object* v_modName_4780_, lean_object* v_d_4781_, lean_object* v_cacheRef_4782_, lean_object* v_tree_4783_, lean_object* v_act_4784_, lean_object* v_c_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4777_, v_cctx_4778_, v_env_4779_, v_modName_4780_, v_d_4781_, v_cacheRef_4782_, v_tree_4783_, v_act_4784_, v_c_4785_);
lean_dec(v_cacheRef_4782_);
lean_dec(v_d_4781_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4788_, lean_object* v_as_4789_, size_t v_i_4790_, size_t v_stop_4791_, lean_object* v_b_4792_){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4789_, v_i_4790_, v_stop_4791_, v_b_4792_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4794_, lean_object* v_as_4795_, lean_object* v_i_4796_, lean_object* v_stop_4797_, lean_object* v_b_4798_){
_start:
{
size_t v_i_boxed_4799_; size_t v_stop_boxed_4800_; lean_object* v_res_4801_; 
v_i_boxed_4799_ = lean_unbox_usize(v_i_4796_);
lean_dec(v_i_4796_);
v_stop_boxed_4800_ = lean_unbox_usize(v_stop_4797_);
lean_dec(v_stop_4797_);
v_res_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4794_, v_as_4795_, v_i_boxed_4799_, v_stop_boxed_4800_, v_b_4798_);
lean_dec_ref(v_as_4795_);
return v_res_4801_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4802_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4803_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_4804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
lean_ctor_set(v___x_4804_, 1, v___x_4802_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4805_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4807_, lean_object* v_y_4808_){
_start:
{
lean_object* v_tree_4809_; lean_object* v_errors_4810_; lean_object* v_tree_4811_; lean_object* v_errors_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4821_; 
v_tree_4809_ = lean_ctor_get(v_x_4807_, 0);
lean_inc_ref(v_tree_4809_);
v_errors_4810_ = lean_ctor_get(v_x_4807_, 1);
lean_inc_ref(v_errors_4810_);
lean_dec_ref(v_x_4807_);
v_tree_4811_ = lean_ctor_get(v_y_4808_, 0);
v_errors_4812_ = lean_ctor_get(v_y_4808_, 1);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_y_4808_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4814_ = v_y_4808_;
v_isShared_4815_ = v_isSharedCheck_4821_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_errors_4812_);
lean_inc(v_tree_4811_);
lean_dec(v_y_4808_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4821_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4819_; 
v___x_4816_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4809_, v_tree_4811_);
v___x_4817_ = l_Array_append___redArg(v_errors_4810_, v_errors_4812_);
lean_dec_ref(v_errors_4812_);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 1, v___x_4817_);
lean_ctor_set(v___x_4814_, 0, v___x_4816_);
v___x_4819_ = v___x_4814_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4820_, 1, v___x_4817_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4822_, lean_object* v_x_4823_, lean_object* v_y_4824_){
_start:
{
lean_object* v___x_4825_; 
v___x_4825_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4823_, v_y_4824_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4827_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4829_, lean_object* v_tree_4830_){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4832_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4833_ = lean_st_ref_swap(v_d_4829_, v___x_4832_);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v_tree_4830_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4835_, lean_object* v_tree_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4835_, v_tree_4836_);
lean_dec(v_d_4835_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4839_, lean_object* v_d_4840_, lean_object* v_tree_4841_){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4840_, v_tree_4841_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4844_, lean_object* v_d_4845_, lean_object* v_tree_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4844_, v_d_4845_, v_tree_4846_);
lean_dec(v_d_4845_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4849_, lean_object* v_env_4850_, lean_object* v_act_4851_, lean_object* v_d_4852_, lean_object* v_cacheRef_4853_, lean_object* v_tree_4854_, lean_object* v_mname_4855_, lean_object* v_mdata_4856_, lean_object* v_i_4857_){
_start:
{
lean_object* v_constants_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v_constants_4859_ = lean_ctor_get(v_mdata_4856_, 2);
v___x_4860_ = lean_array_get_size(v_constants_4859_);
v___x_4861_ = lean_nat_dec_lt(v_i_4857_, v___x_4860_);
if (v___x_4861_ == 0)
{
lean_dec(v_i_4857_);
lean_dec(v_mname_4855_);
lean_dec_ref(v_act_4851_);
lean_dec_ref(v_env_4850_);
lean_dec_ref(v_cctx_4849_);
return v_tree_4854_;
}
else
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4862_ = lean_array_fget_borrowed(v_constants_4859_, v_i_4857_);
lean_inc(v___x_4862_);
v___x_4863_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4862_);
lean_inc_ref(v_act_4851_);
lean_inc(v_mname_4855_);
lean_inc_ref(v_env_4850_);
lean_inc_ref(v_cctx_4849_);
v___x_4864_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4849_, v_env_4850_, v_mname_4855_, v_d_4852_, v_cacheRef_4853_, v_tree_4854_, v_act_4851_, v___x_4863_);
v___x_4865_ = lean_unsigned_to_nat(1u);
v___x_4866_ = lean_nat_add(v_i_4857_, v___x_4865_);
lean_dec(v_i_4857_);
v_tree_4854_ = v___x_4864_;
v_i_4857_ = v___x_4866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4868_, lean_object* v_env_4869_, lean_object* v_act_4870_, lean_object* v_d_4871_, lean_object* v_cacheRef_4872_, lean_object* v_tree_4873_, lean_object* v_mname_4874_, lean_object* v_mdata_4875_, lean_object* v_i_4876_, lean_object* v_a_4877_){
_start:
{
lean_object* v_res_4878_; 
v_res_4878_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4868_, v_env_4869_, v_act_4870_, v_d_4871_, v_cacheRef_4872_, v_tree_4873_, v_mname_4874_, v_mdata_4875_, v_i_4876_);
lean_dec_ref(v_mdata_4875_);
lean_dec(v_cacheRef_4872_);
lean_dec(v_d_4871_);
return v_res_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4879_, lean_object* v_cctx_4880_, lean_object* v_env_4881_, lean_object* v_act_4882_, lean_object* v_d_4883_, lean_object* v_cacheRef_4884_, lean_object* v_tree_4885_, lean_object* v_mname_4886_, lean_object* v_mdata_4887_, lean_object* v_i_4888_){
_start:
{
lean_object* v___x_4890_; 
v___x_4890_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4880_, v_env_4881_, v_act_4882_, v_d_4883_, v_cacheRef_4884_, v_tree_4885_, v_mname_4886_, v_mdata_4887_, v_i_4888_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4891_, lean_object* v_cctx_4892_, lean_object* v_env_4893_, lean_object* v_act_4894_, lean_object* v_d_4895_, lean_object* v_cacheRef_4896_, lean_object* v_tree_4897_, lean_object* v_mname_4898_, lean_object* v_mdata_4899_, lean_object* v_i_4900_, lean_object* v_a_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4891_, v_cctx_4892_, v_env_4893_, v_act_4894_, v_d_4895_, v_cacheRef_4896_, v_tree_4897_, v_mname_4898_, v_mdata_4899_, v_i_4900_);
lean_dec_ref(v_mdata_4899_);
lean_dec(v_cacheRef_4896_);
lean_dec(v_d_4895_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4903_, lean_object* v_env_4904_, lean_object* v_act_4905_, lean_object* v_d_4906_, lean_object* v_cacheRef_4907_, lean_object* v_tree_4908_, lean_object* v_start_4909_, lean_object* v_stop_4910_){
_start:
{
uint8_t v___x_4912_; 
v___x_4912_ = lean_nat_dec_lt(v_start_4909_, v_stop_4910_);
if (v___x_4912_ == 0)
{
lean_object* v___x_4913_; 
lean_dec(v_start_4909_);
lean_dec_ref(v_act_4905_);
lean_dec_ref(v_env_4904_);
lean_dec_ref(v_cctx_4903_);
v___x_4913_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4906_, v_tree_4908_);
return v___x_4913_;
}
else
{
lean_object* v___x_4914_; lean_object* v_moduleData_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v_mname_4919_; lean_object* v_mdata_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4914_ = l_Lean_Environment_header(v_env_4904_);
v_moduleData_4915_ = lean_ctor_get(v___x_4914_, 6);
lean_inc_ref(v_moduleData_4915_);
v___x_4916_ = lean_box(0);
v___x_4917_ = l_Lean_instInhabitedModuleData_default;
v___x_4918_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4914_);
v_mname_4919_ = lean_array_get(v___x_4916_, v___x_4918_, v_start_4909_);
lean_dec_ref(v___x_4918_);
v_mdata_4920_ = lean_array_get(v___x_4917_, v_moduleData_4915_, v_start_4909_);
lean_dec_ref(v_moduleData_4915_);
v___x_4921_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4905_);
lean_inc_ref(v_env_4904_);
lean_inc_ref(v_cctx_4903_);
v___x_4922_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4903_, v_env_4904_, v_act_4905_, v_d_4906_, v_cacheRef_4907_, v_tree_4908_, v_mname_4919_, v_mdata_4920_, v___x_4921_);
lean_dec(v_mdata_4920_);
v___x_4923_ = lean_unsigned_to_nat(1u);
v___x_4924_ = lean_nat_add(v_start_4909_, v___x_4923_);
lean_dec(v_start_4909_);
v_tree_4908_ = v___x_4922_;
v_start_4909_ = v___x_4924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4926_, lean_object* v_env_4927_, lean_object* v_act_4928_, lean_object* v_d_4929_, lean_object* v_cacheRef_4930_, lean_object* v_tree_4931_, lean_object* v_start_4932_, lean_object* v_stop_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4926_, v_env_4927_, v_act_4928_, v_d_4929_, v_cacheRef_4930_, v_tree_4931_, v_start_4932_, v_stop_4933_);
lean_dec(v_stop_4933_);
lean_dec(v_cacheRef_4930_);
lean_dec(v_d_4929_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_4936_, lean_object* v_cctx_4937_, lean_object* v_env_4938_, lean_object* v_act_4939_, lean_object* v_d_4940_, lean_object* v_cacheRef_4941_, lean_object* v_tree_4942_, lean_object* v_start_4943_, lean_object* v_stop_4944_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4937_, v_env_4938_, v_act_4939_, v_d_4940_, v_cacheRef_4941_, v_tree_4942_, v_start_4943_, v_stop_4944_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_4947_, lean_object* v_cctx_4948_, lean_object* v_env_4949_, lean_object* v_act_4950_, lean_object* v_d_4951_, lean_object* v_cacheRef_4952_, lean_object* v_tree_4953_, lean_object* v_start_4954_, lean_object* v_stop_4955_, lean_object* v_a_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_4947_, v_cctx_4948_, v_env_4949_, v_act_4950_, v_d_4951_, v_cacheRef_4952_, v_tree_4953_, v_start_4954_, v_stop_4955_);
lean_dec(v_stop_4955_);
lean_dec(v_cacheRef_4952_);
lean_dec(v_d_4951_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_4958_, lean_object* v_ngen_4959_, lean_object* v_env_4960_, lean_object* v_act_4961_, lean_object* v_start_4962_, lean_object* v_stop_4963_){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4965_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4959_);
v___x_4966_ = lean_st_mk_ref(v___x_4965_);
v___x_4967_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_4968_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_4969_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4958_, v_env_4960_, v_act_4961_, v___x_4967_, v___x_4966_, v___x_4968_, v_start_4962_, v_stop_4963_);
lean_dec(v___x_4966_);
lean_dec(v___x_4967_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_4970_, lean_object* v_ngen_4971_, lean_object* v_env_4972_, lean_object* v_act_4973_, lean_object* v_start_4974_, lean_object* v_stop_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_4970_, v_ngen_4971_, v_env_4972_, v_act_4973_, v_start_4974_, v_stop_4975_);
lean_dec(v_stop_4975_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_4978_, lean_object* v_cctx_4979_, lean_object* v_ngen_4980_, lean_object* v_env_4981_, lean_object* v_act_4982_, lean_object* v_start_4983_, lean_object* v_stop_4984_){
_start:
{
lean_object* v___x_4986_; 
v___x_4986_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_4979_, v_ngen_4980_, v_env_4981_, v_act_4982_, v_start_4983_, v_stop_4984_);
return v___x_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_4987_, lean_object* v_cctx_4988_, lean_object* v_ngen_4989_, lean_object* v_env_4990_, lean_object* v_act_4991_, lean_object* v_start_4992_, lean_object* v_stop_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_4987_, v_cctx_4988_, v_ngen_4989_, v_env_4990_, v_act_4991_, v_start_4992_, v_stop_4993_);
lean_dec(v_stop_4993_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_4996_, lean_object* v_x1_4997_, lean_object* v_x2_4998_){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = lean_task_get_own(v_x2_4998_);
v___x_5000_ = lean_apply_2(v_inst_4996_, v_x1_4997_, v___x_4999_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5001_, lean_object* v_z_5002_, lean_object* v_tasks_5003_){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; 
v___x_5004_ = lean_unsigned_to_nat(0u);
v___x_5005_ = lean_array_get_size(v_tasks_5003_);
v___x_5006_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5007_ = lean_nat_dec_lt(v___x_5004_, v___x_5005_);
if (v___x_5007_ == 0)
{
lean_dec_ref(v_tasks_5003_);
lean_dec(v_inst_5001_);
return v_z_5002_;
}
else
{
lean_object* v___f_5008_; uint8_t v___x_5009_; 
v___f_5008_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5008_, 0, v_inst_5001_);
v___x_5009_ = lean_nat_dec_le(v___x_5005_, v___x_5005_);
if (v___x_5009_ == 0)
{
if (v___x_5007_ == 0)
{
lean_dec_ref(v___f_5008_);
lean_dec_ref(v_tasks_5003_);
return v_z_5002_;
}
else
{
size_t v___x_5010_; size_t v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = ((size_t)0ULL);
v___x_5011_ = lean_usize_of_nat(v___x_5005_);
v___x_5012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5006_, v___f_5008_, v_tasks_5003_, v___x_5010_, v___x_5011_, v_z_5002_);
return v___x_5012_;
}
}
else
{
size_t v___x_5013_; size_t v___x_5014_; lean_object* v___x_5015_; 
v___x_5013_ = ((size_t)0ULL);
v___x_5014_ = lean_usize_of_nat(v___x_5005_);
v___x_5015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5006_, v___f_5008_, v_tasks_5003_, v___x_5013_, v___x_5014_, v_z_5002_);
return v___x_5015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5016_, lean_object* v_inst_5017_, lean_object* v_z_5018_, lean_object* v_tasks_5019_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5017_, v_z_5018_, v_tasks_5019_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5021_, lean_object* v___x_5022_, lean_object* v_____r_5023_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = lean_apply_2(v_toPure_5021_, lean_box(0), v___x_5022_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5025_, lean_object* v_setNGen_5026_, lean_object* v_toBind_5027_, lean_object* v_ngen_5028_){
_start:
{
lean_object* v_namePrefix_5029_; lean_object* v_idx_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5044_; 
v_namePrefix_5029_ = lean_ctor_get(v_ngen_5028_, 0);
v_idx_5030_ = lean_ctor_get(v_ngen_5028_, 1);
v_isSharedCheck_5044_ = !lean_is_exclusive(v_ngen_5028_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5032_ = v_ngen_5028_;
v_isShared_5033_ = v_isSharedCheck_5044_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_idx_5030_);
lean_inc(v_namePrefix_5029_);
lean_dec(v_ngen_5028_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5044_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5037_; 
lean_inc(v_idx_5030_);
lean_inc(v_namePrefix_5029_);
v___x_5034_ = l_Lean_Name_num___override(v_namePrefix_5029_, v_idx_5030_);
v___x_5035_ = lean_unsigned_to_nat(1u);
if (v_isShared_5033_ == 0)
{
lean_ctor_set(v___x_5032_, 1, v___x_5035_);
lean_ctor_set(v___x_5032_, 0, v___x_5034_);
v___x_5037_ = v___x_5032_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_5034_);
lean_ctor_set(v_reuseFailAlloc_5043_, 1, v___x_5035_);
v___x_5037_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
lean_object* v___f_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___f_5038_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5038_, 0, v_toPure_5025_);
lean_closure_set(v___f_5038_, 1, v___x_5037_);
v___x_5039_ = lean_nat_add(v_idx_5030_, v___x_5035_);
lean_dec(v_idx_5030_);
v___x_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5040_, 0, v_namePrefix_5029_);
lean_ctor_set(v___x_5040_, 1, v___x_5039_);
v___x_5041_ = lean_apply_1(v_setNGen_5026_, v___x_5040_);
v___x_5042_ = lean_apply_4(v_toBind_5027_, lean_box(0), lean_box(0), v___x_5041_, v___f_5038_);
return v___x_5042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5045_, lean_object* v_inst_5046_){
_start:
{
lean_object* v_toApplicative_5047_; lean_object* v_toBind_5048_; lean_object* v_getNGen_5049_; lean_object* v_setNGen_5050_; lean_object* v_toPure_5051_; lean_object* v___f_5052_; lean_object* v___x_5053_; 
v_toApplicative_5047_ = lean_ctor_get(v_inst_5045_, 0);
lean_inc_ref(v_toApplicative_5047_);
v_toBind_5048_ = lean_ctor_get(v_inst_5045_, 1);
lean_inc_n(v_toBind_5048_, 2);
lean_dec_ref(v_inst_5045_);
v_getNGen_5049_ = lean_ctor_get(v_inst_5046_, 0);
lean_inc(v_getNGen_5049_);
v_setNGen_5050_ = lean_ctor_get(v_inst_5046_, 1);
lean_inc(v_setNGen_5050_);
lean_dec_ref(v_inst_5046_);
v_toPure_5051_ = lean_ctor_get(v_toApplicative_5047_, 1);
lean_inc(v_toPure_5051_);
lean_dec_ref(v_toApplicative_5047_);
v___f_5052_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5052_, 0, v_toPure_5051_);
lean_closure_set(v___f_5052_, 1, v_setNGen_5050_);
lean_closure_set(v___f_5052_, 2, v_toBind_5048_);
v___x_5053_ = lean_apply_4(v_toBind_5048_, lean_box(0), lean_box(0), v_getNGen_5049_, v___f_5052_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5054_, lean_object* v_inst_5055_, lean_object* v_inst_5056_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5055_, v_inst_5056_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5058_, lean_object* v_env_5059_, lean_object* v_modName_5060_, lean_object* v_d_5061_, lean_object* v_val_5062_, lean_object* v_act_5063_, lean_object* v_as_5064_, size_t v_sz_5065_, size_t v_i_5066_, lean_object* v_b_5067_){
_start:
{
uint8_t v___x_5069_; 
v___x_5069_ = lean_usize_dec_lt(v_i_5066_, v_sz_5065_);
if (v___x_5069_ == 0)
{
lean_dec_ref(v_act_5063_);
lean_dec(v_modName_5060_);
lean_dec_ref(v_env_5059_);
lean_dec_ref(v_cctx_5058_);
return v_b_5067_;
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5071_; size_t v___x_5072_; size_t v___x_5073_; 
v_a_5070_ = lean_array_uget_borrowed(v_as_5064_, v_i_5066_);
lean_inc(v_a_5070_);
lean_inc_ref(v_act_5063_);
lean_inc(v_modName_5060_);
lean_inc_ref(v_env_5059_);
lean_inc_ref(v_cctx_5058_);
v___x_5071_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5058_, v_env_5059_, v_modName_5060_, v_d_5061_, v_val_5062_, v_b_5067_, v_act_5063_, v_a_5070_);
v___x_5072_ = ((size_t)1ULL);
v___x_5073_ = lean_usize_add(v_i_5066_, v___x_5072_);
v_i_5066_ = v___x_5073_;
v_b_5067_ = v___x_5071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5075_, lean_object* v_env_5076_, lean_object* v_modName_5077_, lean_object* v_d_5078_, lean_object* v_val_5079_, lean_object* v_act_5080_, lean_object* v_as_5081_, lean_object* v_sz_5082_, lean_object* v_i_5083_, lean_object* v_b_5084_, lean_object* v___y_5085_){
_start:
{
size_t v_sz_boxed_5086_; size_t v_i_boxed_5087_; lean_object* v_res_5088_; 
v_sz_boxed_5086_ = lean_unbox_usize(v_sz_5082_);
lean_dec(v_sz_5082_);
v_i_boxed_5087_ = lean_unbox_usize(v_i_5083_);
lean_dec(v_i_5083_);
v_res_5088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5075_, v_env_5076_, v_modName_5077_, v_d_5078_, v_val_5079_, v_act_5080_, v_as_5081_, v_sz_boxed_5086_, v_i_boxed_5087_, v_b_5084_);
lean_dec_ref(v_as_5081_);
lean_dec(v_val_5079_);
lean_dec(v_d_5078_);
return v_res_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5089_, lean_object* v_ngen_5090_, lean_object* v_env_5091_, lean_object* v_d_5092_, lean_object* v_act_5093_){
_start:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v_mainModule_5100_; lean_object* v___x_5101_; size_t v_sz_5102_; size_t v___x_5103_; lean_object* v___x_5104_; 
v___x_5095_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5090_);
v___x_5096_ = lean_st_mk_ref(v___x_5095_);
v___x_5097_ = 1;
v___x_5098_ = l_Lean_Environment_getLocalConstantInfos(v_env_5091_, v___x_5097_);
v___x_5099_ = l_Lean_Environment_header(v_env_5091_);
v_mainModule_5100_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_mainModule_5100_);
lean_dec_ref(v___x_5099_);
v___x_5101_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v_sz_5102_ = lean_array_size(v___x_5098_);
v___x_5103_ = ((size_t)0ULL);
v___x_5104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5089_, v_env_5091_, v_mainModule_5100_, v_d_5092_, v___x_5096_, v_act_5093_, v___x_5098_, v_sz_5102_, v___x_5103_, v___x_5101_);
lean_dec_ref(v___x_5098_);
lean_dec(v___x_5096_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5105_, lean_object* v_ngen_5106_, lean_object* v_env_5107_, lean_object* v_d_5108_, lean_object* v_act_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5105_, v_ngen_5106_, v_env_5107_, v_d_5108_, v_act_5109_);
lean_dec(v_d_5108_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5112_, lean_object* v_cctx_5113_, lean_object* v_ngen_5114_, lean_object* v_env_5115_, lean_object* v_d_5116_, lean_object* v_act_5117_){
_start:
{
lean_object* v___x_5119_; 
v___x_5119_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5113_, v_ngen_5114_, v_env_5115_, v_d_5116_, v_act_5117_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5120_, lean_object* v_cctx_5121_, lean_object* v_ngen_5122_, lean_object* v_env_5123_, lean_object* v_d_5124_, lean_object* v_act_5125_, lean_object* v_a_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5120_, v_cctx_5121_, v_ngen_5122_, v_env_5123_, v_d_5124_, v_act_5125_);
lean_dec(v_d_5124_);
return v_res_5127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5128_, lean_object* v_cctx_5129_, lean_object* v_env_5130_, lean_object* v_modName_5131_, lean_object* v_d_5132_, lean_object* v_val_5133_, lean_object* v_act_5134_, lean_object* v_as_5135_, size_t v_sz_5136_, size_t v_i_5137_, lean_object* v_b_5138_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5129_, v_env_5130_, v_modName_5131_, v_d_5132_, v_val_5133_, v_act_5134_, v_as_5135_, v_sz_5136_, v_i_5137_, v_b_5138_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5141_, lean_object* v_cctx_5142_, lean_object* v_env_5143_, lean_object* v_modName_5144_, lean_object* v_d_5145_, lean_object* v_val_5146_, lean_object* v_act_5147_, lean_object* v_as_5148_, lean_object* v_sz_5149_, lean_object* v_i_5150_, lean_object* v_b_5151_, lean_object* v___y_5152_){
_start:
{
size_t v_sz_boxed_5153_; size_t v_i_boxed_5154_; lean_object* v_res_5155_; 
v_sz_boxed_5153_ = lean_unbox_usize(v_sz_5149_);
lean_dec(v_sz_5149_);
v_i_boxed_5154_ = lean_unbox_usize(v_i_5150_);
lean_dec(v_i_5150_);
v_res_5155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5141_, v_cctx_5142_, v_env_5143_, v_modName_5144_, v_d_5145_, v_val_5146_, v_act_5147_, v_as_5148_, v_sz_boxed_5153_, v_i_boxed_5154_, v_b_5151_);
lean_dec_ref(v_as_5148_);
lean_dec(v_val_5146_);
lean_dec(v_d_5145_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5156_, lean_object* v_x_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
if (lean_obj_tag(v_x_5157_) == 0)
{
lean_object* v___x_5163_; 
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v_x_5156_);
return v___x_5163_;
}
else
{
lean_object* v_head_5164_; lean_object* v_tail_5165_; lean_object* v___x_5166_; 
v_head_5164_ = lean_ctor_get(v_x_5157_, 0);
lean_inc(v_head_5164_);
v_tail_5165_ = lean_ctor_get(v_x_5157_, 1);
lean_inc(v_tail_5165_);
lean_dec_ref_known(v_x_5157_, 2);
v___x_5166_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5156_, v_head_5164_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
v_x_5156_ = v_a_5167_;
v_x_5157_ = v_tail_5165_;
goto _start;
}
else
{
lean_dec(v_tail_5165_);
return v___x_5166_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5169_, lean_object* v_x_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5169_, v_x_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5177_, lean_object* v_keys_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5177_, v_keys_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5185_, lean_object* v_keys_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5185_, v_keys_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
lean_dec(v_a_5190_);
lean_dec_ref(v_a_5189_);
lean_dec(v_a_5188_);
lean_dec_ref(v_a_5187_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5193_, lean_object* v_t_5194_, lean_object* v_keys_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v___x_5201_; 
v___x_5201_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5194_, v_keys_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5202_, lean_object* v_t_5203_, lean_object* v_keys_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5202_, v_t_5203_, v_keys_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5207_);
lean_dec(v_a_5206_);
lean_dec_ref(v_a_5205_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5211_, lean_object* v_x_5212_, lean_object* v_x_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v___x_5219_; 
v___x_5219_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5212_, v_x_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5220_, lean_object* v_x_5221_, lean_object* v_x_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5220_, v_x_5221_, v_x_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5229_, size_t v_sz_5230_, size_t v_i_5231_, lean_object* v_b_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
uint8_t v___x_5239_; 
v___x_5239_ = lean_usize_dec_lt(v_i_5231_, v_sz_5230_);
if (v___x_5239_ == 0)
{
lean_object* v___x_5240_; 
v___x_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5240_, 0, v_b_5232_);
return v___x_5240_;
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5242_; 
v_a_5241_ = lean_array_uget_borrowed(v_as_5229_, v_i_5231_);
v___x_5242_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5241_, v_b_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5255_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5245_ = v___x_5242_;
v_isShared_5246_ = v_isSharedCheck_5255_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5255_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
if (lean_obj_tag(v_a_5243_) == 0)
{
lean_object* v_a_5247_; lean_object* v___x_5249_; 
v_a_5247_ = lean_ctor_get(v_a_5243_, 0);
lean_inc(v_a_5247_);
lean_dec_ref_known(v_a_5243_, 1);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v_a_5247_);
v___x_5249_ = v___x_5245_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v_a_5247_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
else
{
lean_object* v_a_5251_; size_t v___x_5252_; size_t v___x_5253_; 
lean_del_object(v___x_5245_);
v_a_5251_ = lean_ctor_get(v_a_5243_, 0);
lean_inc(v_a_5251_);
lean_dec_ref_known(v_a_5243_, 1);
v___x_5252_ = ((size_t)1ULL);
v___x_5253_ = lean_usize_add(v_i_5231_, v___x_5252_);
v_i_5231_ = v___x_5253_;
v_b_5232_ = v_a_5251_;
goto _start;
}
}
}
else
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
v_a_5256_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5242_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5242_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_){
_start:
{
lean_object* v___x_5271_; uint8_t v___x_5272_; 
v___x_5271_ = lean_unsigned_to_nat(0u);
v___x_5272_ = lean_nat_dec_eq(v_next_5264_, v___x_5271_);
if (v___x_5272_ == 0)
{
lean_object* v___x_5273_; 
v___x_5273_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_a_5274_; lean_object* v_snd_5275_; lean_object* v_fst_5276_; lean_object* v_fst_5277_; lean_object* v_snd_5278_; lean_object* v___x_5279_; 
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
lean_inc(v_a_5274_);
lean_dec_ref_known(v___x_5273_, 1);
v_snd_5275_ = lean_ctor_get(v_a_5274_, 1);
lean_inc(v_snd_5275_);
v_fst_5276_ = lean_ctor_get(v_a_5274_, 0);
lean_inc(v_fst_5276_);
lean_dec(v_a_5274_);
v_fst_5277_ = lean_ctor_get(v_snd_5275_, 0);
lean_inc(v_fst_5277_);
v_snd_5278_ = lean_ctor_get(v_snd_5275_, 1);
lean_inc(v_snd_5278_);
lean_dec(v_snd_5275_);
v___x_5279_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5277_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; lean_object* v_buckets_5281_; lean_object* v___x_5282_; size_t v_sz_5283_; size_t v___x_5284_; lean_object* v___x_5285_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref_known(v___x_5279_, 1);
v_buckets_5281_ = lean_ctor_get(v_snd_5278_, 1);
v___x_5282_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5283_ = lean_array_size(v_buckets_5281_);
v___x_5284_ = ((size_t)0ULL);
v___x_5285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5281_, v_sz_5283_, v___x_5284_, v___x_5282_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5299_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5299_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5288_ = v___x_5285_;
v_isShared_5289_ = v_isSharedCheck_5299_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5285_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5299_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5297_; 
v___x_5290_ = lean_st_ref_take(v_a_5265_);
v___x_5291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5282_);
lean_ctor_set(v___x_5291_, 1, v_fst_5277_);
lean_ctor_set(v___x_5291_, 2, v_snd_5278_);
lean_ctor_set(v___x_5291_, 3, v___x_5282_);
v___x_5292_ = lean_array_set(v___x_5290_, v_next_5264_, v___x_5291_);
v___x_5293_ = lean_st_ref_put(v_a_5265_, v___x_5292_);
v___x_5294_ = l_Array_append___redArg(v_fst_5276_, v_a_5280_);
lean_dec(v_a_5280_);
v___x_5295_ = l_Array_append___redArg(v___x_5294_, v_a_5286_);
lean_dec(v_a_5286_);
if (v_isShared_5289_ == 0)
{
lean_ctor_set(v___x_5288_, 0, v___x_5295_);
v___x_5297_ = v___x_5288_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5295_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
else
{
lean_dec(v_a_5280_);
lean_dec(v_snd_5278_);
lean_dec(v_fst_5277_);
lean_dec(v_fst_5276_);
return v___x_5285_;
}
}
else
{
lean_dec(v_snd_5278_);
lean_dec(v_fst_5277_);
lean_dec(v_fst_5276_);
return v___x_5279_;
}
}
else
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5307_; 
v_a_5300_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5302_ = v___x_5273_;
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5273_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5305_; 
if (v_isShared_5303_ == 0)
{
v___x_5305_ = v___x_5302_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
else
{
lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5308_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5309_, 0, v___x_5308_);
return v___x_5309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_){
_start:
{
if (lean_obj_tag(v_a_5310_) == 0)
{
lean_object* v___x_5318_; lean_object* v___x_5319_; 
v___x_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5318_, 0, v_a_5311_);
v___x_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5318_);
return v___x_5319_;
}
else
{
lean_object* v_value_5320_; lean_object* v_tail_5321_; lean_object* v___x_5322_; 
v_value_5320_ = lean_ctor_get(v_a_5310_, 1);
v_tail_5321_ = lean_ctor_get(v_a_5310_, 2);
v___x_5322_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5320_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; lean_object* v___x_5324_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref_known(v___x_5322_, 1);
v___x_5324_ = l_Array_append___redArg(v_a_5311_, v_a_5323_);
lean_dec(v_a_5323_);
v_a_5310_ = v_tail_5321_;
v_a_5311_ = v___x_5324_;
goto _start;
}
else
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5333_; 
lean_dec_ref(v_a_5311_);
v_a_5326_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5328_ = v___x_5322_;
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5322_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___x_5331_; 
if (v_isShared_5329_ == 0)
{
v___x_5331_ = v___x_5328_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5334_, v_a_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v___y_5338_);
lean_dec_ref(v___y_5337_);
lean_dec(v___y_5336_);
lean_dec(v_a_5334_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5343_, lean_object* v_sz_5344_, lean_object* v_i_5345_, lean_object* v_b_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
size_t v_sz_boxed_5353_; size_t v_i_boxed_5354_; lean_object* v_res_5355_; 
v_sz_boxed_5353_ = lean_unbox_usize(v_sz_5344_);
lean_dec(v_sz_5344_);
v_i_boxed_5354_ = lean_unbox_usize(v_i_5345_);
lean_dec(v_i_5345_);
v_res_5355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5343_, v_sz_boxed_5353_, v_i_boxed_5354_, v_b_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec(v___y_5349_);
lean_dec_ref(v___y_5348_);
lean_dec(v___y_5347_);
lean_dec_ref(v_as_5343_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5356_, lean_object* v_a_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_);
lean_dec(v_a_5361_);
lean_dec_ref(v_a_5360_);
lean_dec(v_a_5359_);
lean_dec_ref(v_a_5358_);
lean_dec(v_a_5357_);
lean_dec(v_next_5356_);
return v_res_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5364_, lean_object* v_next_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v___x_5372_; 
v___x_5372_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_);
return v___x_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5373_, lean_object* v_next_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5373_, v_next_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_);
lean_dec(v_a_5379_);
lean_dec_ref(v_a_5378_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
lean_dec(v_a_5375_);
lean_dec(v_next_5374_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v___x_5391_; 
v___x_5391_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5383_, v_a_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5392_, v_a_5393_, v_a_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_);
lean_dec(v___y_5399_);
lean_dec_ref(v___y_5398_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
lean_dec(v___y_5395_);
lean_dec(v_a_5393_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5402_, lean_object* v_as_5403_, size_t v_sz_5404_, size_t v_i_5405_, lean_object* v_b_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v___x_5413_; 
v___x_5413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5403_, v_sz_5404_, v_i_5405_, v_b_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5414_, lean_object* v_as_5415_, lean_object* v_sz_5416_, lean_object* v_i_5417_, lean_object* v_b_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_){
_start:
{
size_t v_sz_boxed_5425_; size_t v_i_boxed_5426_; lean_object* v_res_5427_; 
v_sz_boxed_5425_ = lean_unbox_usize(v_sz_5416_);
lean_dec(v_sz_5416_);
v_i_boxed_5426_ = lean_unbox_usize(v_i_5417_);
lean_dec(v_i_5417_);
v_res_5427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5414_, v_as_5415_, v_sz_boxed_5425_, v_i_boxed_5426_, v_b_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v_as_5415_);
return v_res_5427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5428_, lean_object* v_rest_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_){
_start:
{
lean_object* v___x_5436_; uint8_t v___x_5437_; 
v___x_5436_ = lean_unsigned_to_nat(0u);
v___x_5437_ = lean_nat_dec_eq(v_next_5428_, v___x_5436_);
if (v___x_5437_ == 0)
{
lean_object* v___x_5438_; 
v___x_5438_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5428_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v_snd_5440_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
lean_inc(v_a_5439_);
lean_dec_ref_known(v___x_5438_, 1);
v_snd_5440_ = lean_ctor_get(v_a_5439_, 1);
lean_inc(v_snd_5440_);
lean_dec(v_a_5439_);
if (lean_obj_tag(v_rest_5429_) == 0)
{
lean_object* v___x_5441_; 
lean_dec(v_snd_5440_);
v___x_5441_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5428_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
lean_dec(v_next_5428_);
return v___x_5441_;
}
else
{
lean_object* v_fst_5442_; lean_object* v_snd_5443_; lean_object* v_head_5444_; lean_object* v_tail_5445_; lean_object* v___x_5446_; uint8_t v___x_5447_; 
lean_dec(v_next_5428_);
v_fst_5442_ = lean_ctor_get(v_snd_5440_, 0);
lean_inc(v_fst_5442_);
v_snd_5443_ = lean_ctor_get(v_snd_5440_, 1);
lean_inc(v_snd_5443_);
lean_dec(v_snd_5440_);
v_head_5444_ = lean_ctor_get(v_rest_5429_, 0);
v_tail_5445_ = lean_ctor_get(v_rest_5429_, 1);
v___x_5446_ = lean_box(3);
v___x_5447_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5444_, v___x_5446_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; 
lean_dec(v_fst_5442_);
v___x_5448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5443_, v_head_5444_, v___x_5436_);
lean_dec(v_snd_5443_);
v_next_5428_ = v___x_5448_;
v_rest_5429_ = v_tail_5445_;
goto _start;
}
else
{
lean_dec(v_snd_5443_);
v_next_5428_ = v_fst_5442_;
v_rest_5429_ = v_tail_5445_;
goto _start;
}
}
}
else
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec(v_next_5428_);
v_a_5451_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5438_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5438_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5454_ == 0)
{
v___x_5456_ = v___x_5453_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
else
{
lean_object* v___x_5459_; lean_object* v___x_5460_; 
lean_dec(v_next_5428_);
v___x_5459_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5460_, 0, v___x_5459_);
return v___x_5460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5461_, lean_object* v_rest_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5461_, v_rest_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
lean_dec(v_a_5467_);
lean_dec_ref(v_a_5466_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec(v_rest_5462_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5470_, lean_object* v_next_5471_, lean_object* v_rest_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5471_, v_rest_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5480_, lean_object* v_next_5481_, lean_object* v_rest_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_){
_start:
{
lean_object* v_res_5489_; 
v_res_5489_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5480_, v_next_5481_, v_rest_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_);
lean_dec(v_a_5487_);
lean_dec_ref(v_a_5486_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
lean_dec(v_a_5483_);
lean_dec(v_rest_5482_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5490_, lean_object* v_path_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_){
_start:
{
if (lean_obj_tag(v_path_5491_) == 0)
{
lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v___x_5497_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5497_);
lean_ctor_set(v___x_5498_, 1, v_t_5490_);
v___x_5499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5498_);
return v___x_5499_;
}
else
{
lean_object* v_head_5500_; lean_object* v_tail_5501_; lean_object* v_roots_5502_; lean_object* v___x_5503_; lean_object* v_idx_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
v_head_5500_ = lean_ctor_get(v_path_5491_, 0);
lean_inc(v_head_5500_);
v_tail_5501_ = lean_ctor_get(v_path_5491_, 1);
lean_inc(v_tail_5501_);
lean_dec_ref_known(v_path_5491_, 2);
v_roots_5502_ = lean_ctor_get(v_t_5490_, 1);
v___x_5503_ = lean_unsigned_to_nat(0u);
v_idx_5504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5502_, v_head_5500_, v___x_5503_);
lean_dec(v_head_5500_);
v___x_5505_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5505_, 0, lean_box(0));
lean_closure_set(v___x_5505_, 1, v_idx_5504_);
lean_closure_set(v___x_5505_, 2, v_tail_5501_);
v___x_5506_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5490_, v___x_5505_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_);
return v___x_5506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5507_, lean_object* v_path_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_){
_start:
{
lean_object* v_res_5514_; 
v_res_5514_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5507_, v_path_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_);
lean_dec(v_a_5512_);
lean_dec_ref(v_a_5511_);
lean_dec(v_a_5510_);
lean_dec_ref(v_a_5509_);
return v_res_5514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5515_, lean_object* v_t_5516_, lean_object* v_path_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_){
_start:
{
lean_object* v___x_5523_; 
v___x_5523_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5516_, v_path_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_);
return v___x_5523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5524_, lean_object* v_t_5525_, lean_object* v_path_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_){
_start:
{
lean_object* v_res_5532_; 
v_res_5532_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5524_, v_t_5525_, v_path_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_);
lean_dec(v_a_5530_);
lean_dec_ref(v_a_5529_);
lean_dec(v_a_5528_);
lean_dec_ref(v_a_5527_);
return v_res_5532_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5533_, lean_object* v_b_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_){
_start:
{
if (lean_obj_tag(v_as_x27_5533_) == 0)
{
lean_object* v___x_5540_; 
v___x_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5540_, 0, v_b_5534_);
return v___x_5540_;
}
else
{
lean_object* v_head_5541_; lean_object* v_tail_5542_; lean_object* v_fst_5543_; lean_object* v_snd_5544_; lean_object* v___x_5545_; 
v_head_5541_ = lean_ctor_get(v_as_x27_5533_, 0);
v_tail_5542_ = lean_ctor_get(v_as_x27_5533_, 1);
v_fst_5543_ = lean_ctor_get(v_b_5534_, 0);
lean_inc(v_fst_5543_);
v_snd_5544_ = lean_ctor_get(v_b_5534_, 1);
lean_inc(v_snd_5544_);
lean_dec_ref(v_b_5534_);
lean_inc(v_head_5541_);
v___x_5545_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5544_, v_head_5541_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_object* v_a_5546_; lean_object* v_fst_5547_; lean_object* v_snd_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5557_; 
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_a_5546_);
lean_dec_ref_known(v___x_5545_, 1);
v_fst_5547_ = lean_ctor_get(v_a_5546_, 0);
v_snd_5548_ = lean_ctor_get(v_a_5546_, 1);
v_isSharedCheck_5557_ = !lean_is_exclusive(v_a_5546_);
if (v_isSharedCheck_5557_ == 0)
{
v___x_5550_ = v_a_5546_;
v_isShared_5551_ = v_isSharedCheck_5557_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_snd_5548_);
lean_inc(v_fst_5547_);
lean_dec(v_a_5546_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5557_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5552_; lean_object* v___x_5554_; 
v___x_5552_ = l_Array_append___redArg(v_fst_5543_, v_fst_5547_);
lean_dec(v_fst_5547_);
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 0, v___x_5552_);
v___x_5554_ = v___x_5550_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v_snd_5548_);
v___x_5554_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
v_as_x27_5533_ = v_tail_5542_;
v_b_5534_ = v___x_5554_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5543_);
return v___x_5545_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5558_, lean_object* v_b_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_){
_start:
{
lean_object* v_res_5565_; 
v_res_5565_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5558_, v_b_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_);
lean_dec(v___y_5563_);
lean_dec_ref(v___y_5562_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v_as_x27_5558_);
return v_res_5565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5566_, lean_object* v_keys_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_){
_start:
{
lean_object* v_allExtracted_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; 
v_allExtracted_5573_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5574_, 0, v_allExtracted_5573_);
lean_ctor_set(v___x_5574_, 1, v_t_5566_);
v___x_5575_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5567_, v___x_5574_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v_a_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5592_; 
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5578_ = v___x_5575_;
v_isShared_5579_ = v_isSharedCheck_5592_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_a_5576_);
lean_dec(v___x_5575_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5592_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v_fst_5580_; lean_object* v_snd_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5591_; 
v_fst_5580_ = lean_ctor_get(v_a_5576_, 0);
v_snd_5581_ = lean_ctor_get(v_a_5576_, 1);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_a_5576_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5583_ = v_a_5576_;
v_isShared_5584_ = v_isSharedCheck_5591_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_snd_5581_);
lean_inc(v_fst_5580_);
lean_dec(v_a_5576_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5591_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5584_ == 0)
{
v___x_5586_ = v___x_5583_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_fst_5580_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v_snd_5581_);
v___x_5586_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
lean_object* v___x_5588_; 
if (v_isShared_5579_ == 0)
{
lean_ctor_set(v___x_5578_, 0, v___x_5586_);
v___x_5588_ = v___x_5578_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5586_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
}
}
else
{
return v___x_5575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5593_, lean_object* v_keys_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_){
_start:
{
lean_object* v_res_5600_; 
v_res_5600_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5593_, v_keys_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_);
lean_dec(v_a_5598_);
lean_dec_ref(v_a_5597_);
lean_dec(v_a_5596_);
lean_dec_ref(v_a_5595_);
lean_dec(v_keys_5594_);
return v_res_5600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5601_, lean_object* v_t_5602_, lean_object* v_keys_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_){
_start:
{
lean_object* v___x_5609_; 
v___x_5609_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5602_, v_keys_5603_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_);
return v___x_5609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5610_, lean_object* v_t_5611_, lean_object* v_keys_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_){
_start:
{
lean_object* v_res_5618_; 
v_res_5618_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5610_, v_t_5611_, v_keys_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_);
lean_dec(v_a_5616_);
lean_dec_ref(v_a_5615_);
lean_dec(v_a_5614_);
lean_dec_ref(v_a_5613_);
lean_dec(v_keys_5612_);
return v_res_5618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5619_, lean_object* v_as_5620_, lean_object* v_as_x27_5621_, lean_object* v_b_5622_, lean_object* v_a_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
lean_object* v___x_5629_; 
v___x_5629_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5621_, v_b_5622_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_);
return v___x_5629_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5630_, lean_object* v_as_5631_, lean_object* v_as_x27_5632_, lean_object* v_b_5633_, lean_object* v_a_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5630_, v_as_5631_, v_as_x27_5632_, v_b_5633_, v_a_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec(v_as_x27_5632_);
lean_dec(v_as_5631_);
return v_res_5640_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5642_; lean_object* v___x_5643_; 
v___x_5642_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5643_ = l_Lean_stringToMessageData(v___x_5642_);
return v___x_5643_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5645_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5646_ = l_Lean_stringToMessageData(v___x_5645_);
return v___x_5646_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5648_; lean_object* v___x_5649_; 
v___x_5648_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5649_ = l_Lean_stringToMessageData(v___x_5648_);
return v___x_5649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5650_, lean_object* v_inst_5651_, lean_object* v_inst_5652_, lean_object* v_inst_5653_, lean_object* v_f_5654_){
_start:
{
lean_object* v_module_5655_; lean_object* v_const_5656_; lean_object* v_exception_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; 
v_module_5655_ = lean_ctor_get(v_f_5654_, 0);
lean_inc(v_module_5655_);
v_const_5656_ = lean_ctor_get(v_f_5654_, 1);
lean_inc(v_const_5656_);
v_exception_5657_ = lean_ctor_get(v_f_5654_, 2);
lean_inc_ref(v_exception_5657_);
lean_dec_ref(v_f_5654_);
v___x_5658_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5659_ = l_Lean_MessageData_ofName(v_const_5656_);
v___x_5660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5660_, 0, v___x_5658_);
lean_ctor_set(v___x_5660_, 1, v___x_5659_);
v___x_5661_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5660_);
lean_ctor_set(v___x_5662_, 1, v___x_5661_);
v___x_5663_ = l_Lean_MessageData_ofName(v_module_5655_);
v___x_5664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5662_);
lean_ctor_set(v___x_5664_, 1, v___x_5663_);
v___x_5665_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5664_);
lean_ctor_set(v___x_5666_, 1, v___x_5665_);
v___x_5667_ = l_Lean_Exception_toMessageData(v_exception_5657_);
v___x_5668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5666_);
lean_ctor_set(v___x_5668_, 1, v___x_5667_);
v___x_5669_ = l_Lean_logError___redArg(v_inst_5650_, v_inst_5651_, v_inst_5652_, v_inst_5653_, v___x_5668_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5670_, lean_object* v_inst_5671_, lean_object* v_inst_5672_, lean_object* v_inst_5673_, lean_object* v_inst_5674_, lean_object* v_f_5675_){
_start:
{
lean_object* v___x_5676_; 
v___x_5676_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5671_, v_inst_5672_, v_inst_5673_, v_inst_5674_, v_f_5675_);
return v___x_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5677_, lean_object* v_toPure_5678_, lean_object* v_t_5679_){
_start:
{
lean_object* v___x_5680_; lean_object* v___x_5681_; 
v___x_5680_ = lean_array_push(v_tasks_5677_, v_t_5679_);
v___x_5681_ = lean_apply_2(v_toPure_5678_, lean_box(0), v___x_5680_);
return v___x_5681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5682_, lean_object* v_inst_5683_, lean_object* v_cctx_5684_, lean_object* v_env_5685_, lean_object* v_act_5686_, lean_object* v_constantsPerTask_5687_, lean_object* v_n_5688_, lean_object* v_ngen_5689_, lean_object* v_tasks_5690_, lean_object* v_start_5691_, lean_object* v_cnt_5692_, lean_object* v_idx_5693_){
_start:
{
lean_object* v___x_5694_; lean_object* v_toApplicative_5695_; lean_object* v_moduleData_5696_; lean_object* v_toBind_5697_; lean_object* v_toPure_5698_; lean_object* v___x_5699_; uint8_t v___x_5700_; 
v___x_5694_ = l_Lean_Environment_header(v_env_5685_);
v_toApplicative_5695_ = lean_ctor_get(v_inst_5682_, 0);
v_moduleData_5696_ = lean_ctor_get(v___x_5694_, 6);
lean_inc_ref(v_moduleData_5696_);
lean_dec_ref(v___x_5694_);
v_toBind_5697_ = lean_ctor_get(v_inst_5682_, 1);
v_toPure_5698_ = lean_ctor_get(v_toApplicative_5695_, 1);
v___x_5699_ = lean_array_get_size(v_moduleData_5696_);
v___x_5700_ = lean_nat_dec_lt(v_idx_5693_, v___x_5699_);
if (v___x_5700_ == 0)
{
uint8_t v___x_5701_; 
lean_inc(v_toPure_5698_);
lean_inc(v_toBind_5697_);
lean_dec_ref(v_moduleData_5696_);
lean_dec(v_idx_5693_);
lean_dec(v_cnt_5692_);
lean_dec(v_constantsPerTask_5687_);
lean_dec_ref(v_inst_5682_);
v___x_5701_ = lean_nat_dec_lt(v_start_5691_, v_n_5688_);
if (v___x_5701_ == 0)
{
lean_object* v___x_5702_; 
lean_dec(v_toBind_5697_);
lean_dec(v_start_5691_);
lean_dec_ref(v_ngen_5689_);
lean_dec(v_n_5688_);
lean_dec_ref(v_act_5686_);
lean_dec_ref(v_env_5685_);
lean_dec_ref(v_cctx_5684_);
lean_dec(v_inst_5683_);
v___x_5702_ = lean_apply_2(v_toPure_5698_, lean_box(0), v_tasks_5690_);
return v___x_5702_;
}
else
{
lean_object* v_namePrefix_5703_; lean_object* v_idx_5704_; lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5719_; 
v_namePrefix_5703_ = lean_ctor_get(v_ngen_5689_, 0);
v_idx_5704_ = lean_ctor_get(v_ngen_5689_, 1);
v_isSharedCheck_5719_ = !lean_is_exclusive(v_ngen_5689_);
if (v_isSharedCheck_5719_ == 0)
{
v___x_5706_ = v_ngen_5689_;
v_isShared_5707_ = v_isSharedCheck_5719_;
goto v_resetjp_5705_;
}
else
{
lean_inc(v_idx_5704_);
lean_inc(v_namePrefix_5703_);
lean_dec(v_ngen_5689_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5719_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v___f_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5712_; 
v___f_5708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5708_, 0, v_tasks_5690_);
lean_closure_set(v___f_5708_, 1, v_toPure_5698_);
v___x_5709_ = l_Lean_Name_num___override(v_namePrefix_5703_, v_idx_5704_);
v___x_5710_ = lean_unsigned_to_nat(1u);
if (v_isShared_5707_ == 0)
{
lean_ctor_set(v___x_5706_, 1, v___x_5710_);
lean_ctor_set(v___x_5706_, 0, v___x_5709_);
v___x_5712_ = v___x_5706_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v___x_5709_);
lean_ctor_set(v_reuseFailAlloc_5718_, 1, v___x_5710_);
v___x_5712_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; 
v___x_5713_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5713_, 0, lean_box(0));
lean_closure_set(v___x_5713_, 1, v_cctx_5684_);
lean_closure_set(v___x_5713_, 2, v___x_5712_);
lean_closure_set(v___x_5713_, 3, v_env_5685_);
lean_closure_set(v___x_5713_, 4, v_act_5686_);
lean_closure_set(v___x_5713_, 5, v_start_5691_);
lean_closure_set(v___x_5713_, 6, v_n_5688_);
v___x_5714_ = lean_unsigned_to_nat(0u);
v___x_5715_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5715_, 0, lean_box(0));
lean_closure_set(v___x_5715_, 1, v___x_5713_);
lean_closure_set(v___x_5715_, 2, v___x_5714_);
v___x_5716_ = lean_apply_2(v_inst_5683_, lean_box(0), v___x_5715_);
v___x_5717_ = lean_apply_4(v_toBind_5697_, lean_box(0), lean_box(0), v___x_5716_, v___f_5708_);
return v___x_5717_;
}
}
}
}
else
{
lean_object* v_mdata_5720_; lean_object* v_constants_5721_; lean_object* v___x_5722_; lean_object* v_cnt_5723_; uint8_t v___x_5724_; 
v_mdata_5720_ = lean_array_fget(v_moduleData_5696_, v_idx_5693_);
lean_dec_ref(v_moduleData_5696_);
v_constants_5721_ = lean_ctor_get(v_mdata_5720_, 2);
lean_inc_ref(v_constants_5721_);
lean_dec(v_mdata_5720_);
v___x_5722_ = lean_array_get_size(v_constants_5721_);
lean_dec_ref(v_constants_5721_);
v_cnt_5723_ = lean_nat_add(v_cnt_5692_, v___x_5722_);
lean_dec(v_cnt_5692_);
v___x_5724_ = lean_nat_dec_lt(v_constantsPerTask_5687_, v_cnt_5723_);
if (v___x_5724_ == 0)
{
lean_object* v___x_5725_; lean_object* v___x_5726_; 
v___x_5725_ = lean_unsigned_to_nat(1u);
v___x_5726_ = lean_nat_add(v_idx_5693_, v___x_5725_);
lean_dec(v_idx_5693_);
v_cnt_5692_ = v_cnt_5723_;
v_idx_5693_ = v___x_5726_;
goto _start;
}
else
{
lean_object* v_namePrefix_5728_; lean_object* v_idx_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5747_; 
lean_inc(v_toBind_5697_);
lean_dec(v_cnt_5723_);
v_namePrefix_5728_ = lean_ctor_get(v_ngen_5689_, 0);
v_idx_5729_ = lean_ctor_get(v_ngen_5689_, 1);
v_isSharedCheck_5747_ = !lean_is_exclusive(v_ngen_5689_);
if (v_isSharedCheck_5747_ == 0)
{
v___x_5731_ = v_ngen_5689_;
v_isShared_5732_ = v_isSharedCheck_5747_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_idx_5729_);
lean_inc(v_namePrefix_5728_);
lean_dec(v_ngen_5689_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5747_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5736_; 
lean_inc(v_idx_5729_);
lean_inc(v_namePrefix_5728_);
v___x_5733_ = l_Lean_Name_num___override(v_namePrefix_5728_, v_idx_5729_);
v___x_5734_ = lean_unsigned_to_nat(1u);
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5734_);
lean_ctor_set(v___x_5731_, 0, v___x_5733_);
v___x_5736_ = v___x_5731_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v___x_5733_);
lean_ctor_set(v_reuseFailAlloc_5746_, 1, v___x_5734_);
v___x_5736_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___f_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5737_ = lean_nat_add(v_idx_5729_, v___x_5734_);
lean_dec(v_idx_5729_);
v___x_5738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5738_, 0, v_namePrefix_5728_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_nat_add(v_idx_5693_, v___x_5734_);
lean_dec(v_idx_5693_);
lean_inc(v___x_5739_);
lean_inc_ref(v_act_5686_);
lean_inc_ref(v_env_5685_);
lean_inc_ref(v_cctx_5684_);
lean_inc(v_inst_5683_);
v___f_5740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5740_, 0, v_tasks_5690_);
lean_closure_set(v___f_5740_, 1, v_inst_5682_);
lean_closure_set(v___f_5740_, 2, v_inst_5683_);
lean_closure_set(v___f_5740_, 3, v_cctx_5684_);
lean_closure_set(v___f_5740_, 4, v_env_5685_);
lean_closure_set(v___f_5740_, 5, v_act_5686_);
lean_closure_set(v___f_5740_, 6, v_constantsPerTask_5687_);
lean_closure_set(v___f_5740_, 7, v_n_5688_);
lean_closure_set(v___f_5740_, 8, v___x_5738_);
lean_closure_set(v___f_5740_, 9, v___x_5739_);
v___x_5741_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5741_, 0, lean_box(0));
lean_closure_set(v___x_5741_, 1, v_cctx_5684_);
lean_closure_set(v___x_5741_, 2, v___x_5736_);
lean_closure_set(v___x_5741_, 3, v_env_5685_);
lean_closure_set(v___x_5741_, 4, v_act_5686_);
lean_closure_set(v___x_5741_, 5, v_start_5691_);
lean_closure_set(v___x_5741_, 6, v___x_5739_);
v___x_5742_ = lean_unsigned_to_nat(0u);
v___x_5743_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5743_, 0, lean_box(0));
lean_closure_set(v___x_5743_, 1, v___x_5741_);
lean_closure_set(v___x_5743_, 2, v___x_5742_);
v___x_5744_ = lean_apply_2(v_inst_5683_, lean_box(0), v___x_5743_);
v___x_5745_ = lean_apply_4(v_toBind_5697_, lean_box(0), lean_box(0), v___x_5744_, v___f_5740_);
return v___x_5745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5748_, lean_object* v_inst_5749_, lean_object* v_inst_5750_, lean_object* v_cctx_5751_, lean_object* v_env_5752_, lean_object* v_act_5753_, lean_object* v_constantsPerTask_5754_, lean_object* v_n_5755_, lean_object* v___x_5756_, lean_object* v___x_5757_, lean_object* v_t_5758_){
_start:
{
lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; 
v___x_5759_ = lean_array_push(v_tasks_5748_, v_t_5758_);
v___x_5760_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5757_);
v___x_5761_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5749_, v_inst_5750_, v_cctx_5751_, v_env_5752_, v_act_5753_, v_constantsPerTask_5754_, v_n_5755_, v___x_5756_, v___x_5759_, v___x_5757_, v___x_5760_, v___x_5757_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5762_, lean_object* v_00_u03b1_5763_, lean_object* v_inst_5764_, lean_object* v_inst_5765_, lean_object* v_cctx_5766_, lean_object* v_env_5767_, lean_object* v_act_5768_, lean_object* v_constantsPerTask_5769_, lean_object* v_n_5770_, lean_object* v_ngen_5771_, lean_object* v_tasks_5772_, lean_object* v_start_5773_, lean_object* v_cnt_5774_, lean_object* v_idx_5775_){
_start:
{
lean_object* v___x_5776_; 
v___x_5776_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5764_, v_inst_5765_, v_cctx_5766_, v_env_5767_, v_act_5768_, v_constantsPerTask_5769_, v_n_5770_, v_ngen_5771_, v_tasks_5772_, v_start_5773_, v_cnt_5774_, v_idx_5775_);
return v___x_5776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5777_, lean_object* v_h__1_5778_){
_start:
{
lean_object* v_fst_5779_; lean_object* v_snd_5780_; lean_object* v___x_5781_; 
v_fst_5779_ = lean_ctor_get(v_x_5777_, 0);
lean_inc(v_fst_5779_);
v_snd_5780_ = lean_ctor_get(v_x_5777_, 1);
lean_inc(v_snd_5780_);
lean_dec_ref(v_x_5777_);
v___x_5781_ = lean_apply_2(v_h__1_5778_, v_fst_5779_, v_snd_5780_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5782_, lean_object* v_x_5783_, lean_object* v_h__1_5784_){
_start:
{
lean_object* v_fst_5785_; lean_object* v_snd_5786_; lean_object* v___x_5787_; 
v_fst_5785_ = lean_ctor_get(v_x_5783_, 0);
lean_inc(v_fst_5785_);
v_snd_5786_ = lean_ctor_get(v_x_5783_, 1);
lean_inc(v_snd_5786_);
lean_dec_ref(v_x_5783_);
v___x_5787_ = lean_apply_2(v_h__1_5784_, v_fst_5785_, v_snd_5786_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5788_, lean_object* v_inst_5789_, lean_object* v_inst_5790_, lean_object* v_inst_5791_, lean_object* v_x_5792_, lean_object* v___y_5793_){
_start:
{
lean_object* v___x_5794_; 
v___x_5794_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5788_, v_inst_5789_, v_inst_5790_, v_inst_5791_, v___y_5793_);
return v___x_5794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5795_, lean_object* v_toPure_5796_, lean_object* v_____r_5797_){
_start:
{
lean_object* v_tree_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
v_tree_5798_ = lean_ctor_get(v_r_5795_, 0);
lean_inc_ref(v_tree_5798_);
lean_dec_ref(v_r_5795_);
v___x_5799_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5798_);
v___x_5800_ = lean_apply_2(v_toPure_5796_, lean_box(0), v___x_5799_);
return v___x_5800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5801_, lean_object* v___x_5802_, lean_object* v_toPure_5803_, lean_object* v_toBind_5804_, lean_object* v_inst_5805_, lean_object* v___f_5806_, lean_object* v_tasks_5807_){
_start:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v_r_5813_; lean_object* v_errors_5814_; lean_object* v___f_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; uint8_t v___x_5818_; 
v___x_5808_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5801_);
v___x_5809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5801_);
lean_ctor_set(v___x_5809_, 1, v___x_5808_);
v___x_5810_ = lean_mk_empty_array_with_capacity(v___x_5801_);
lean_inc_ref(v___x_5810_);
v___x_5811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5811_, 0, v___x_5809_);
lean_ctor_set(v___x_5811_, 1, v___x_5810_);
v___x_5812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5812_, 0, v___x_5811_);
lean_ctor_set(v___x_5812_, 1, v___x_5810_);
v_r_5813_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5802_, v___x_5812_, v_tasks_5807_);
v_errors_5814_ = lean_ctor_get(v_r_5813_, 1);
lean_inc_ref(v_errors_5814_);
lean_inc(v_toPure_5803_);
v___f_5815_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5815_, 0, v_r_5813_);
lean_closure_set(v___f_5815_, 1, v_toPure_5803_);
v___x_5816_ = lean_array_get_size(v_errors_5814_);
v___x_5817_ = lean_box(0);
v___x_5818_ = lean_nat_dec_lt(v___x_5801_, v___x_5816_);
lean_dec(v___x_5801_);
if (v___x_5818_ == 0)
{
lean_object* v___x_5819_; lean_object* v___x_5820_; 
lean_dec_ref(v_errors_5814_);
lean_dec(v___f_5806_);
lean_dec_ref(v_inst_5805_);
v___x_5819_ = lean_apply_2(v_toPure_5803_, lean_box(0), v___x_5817_);
v___x_5820_ = lean_apply_4(v_toBind_5804_, lean_box(0), lean_box(0), v___x_5819_, v___f_5815_);
return v___x_5820_;
}
else
{
uint8_t v___x_5821_; 
v___x_5821_ = lean_nat_dec_le(v___x_5816_, v___x_5816_);
if (v___x_5821_ == 0)
{
if (v___x_5818_ == 0)
{
lean_object* v___x_5822_; lean_object* v___x_5823_; 
lean_dec_ref(v_errors_5814_);
lean_dec(v___f_5806_);
lean_dec_ref(v_inst_5805_);
v___x_5822_ = lean_apply_2(v_toPure_5803_, lean_box(0), v___x_5817_);
v___x_5823_ = lean_apply_4(v_toBind_5804_, lean_box(0), lean_box(0), v___x_5822_, v___f_5815_);
return v___x_5823_;
}
else
{
size_t v___x_5824_; size_t v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; 
lean_dec(v_toPure_5803_);
v___x_5824_ = ((size_t)0ULL);
v___x_5825_ = lean_usize_of_nat(v___x_5816_);
v___x_5826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5805_, v___f_5806_, v_errors_5814_, v___x_5824_, v___x_5825_, v___x_5817_);
v___x_5827_ = lean_apply_4(v_toBind_5804_, lean_box(0), lean_box(0), v___x_5826_, v___f_5815_);
return v___x_5827_;
}
}
else
{
size_t v___x_5828_; size_t v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; 
lean_dec(v_toPure_5803_);
v___x_5828_ = ((size_t)0ULL);
v___x_5829_ = lean_usize_of_nat(v___x_5816_);
v___x_5830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5805_, v___f_5806_, v_errors_5814_, v___x_5828_, v___x_5829_, v___x_5817_);
v___x_5831_ = lean_apply_4(v_toBind_5804_, lean_box(0), lean_box(0), v___x_5830_, v___f_5815_);
return v___x_5831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5834_, lean_object* v_inst_5835_, lean_object* v_inst_5836_, lean_object* v_inst_5837_, lean_object* v_inst_5838_, lean_object* v_cctx_5839_, lean_object* v_ngen_5840_, lean_object* v_env_5841_, lean_object* v_act_5842_, lean_object* v_constantsPerTask_5843_){
_start:
{
lean_object* v___x_5844_; lean_object* v_moduleData_5845_; lean_object* v_toApplicative_5846_; lean_object* v_toBind_5847_; lean_object* v_n_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v_toPure_5852_; lean_object* v___f_5853_; lean_object* v___x_5854_; lean_object* v___f_5855_; lean_object* v___x_5856_; 
v___x_5844_ = l_Lean_Environment_header(v_env_5841_);
v_moduleData_5845_ = lean_ctor_get(v___x_5844_, 6);
lean_inc_ref(v_moduleData_5845_);
lean_dec_ref(v___x_5844_);
v_toApplicative_5846_ = lean_ctor_get(v_inst_5834_, 0);
v_toBind_5847_ = lean_ctor_get(v_inst_5834_, 1);
lean_inc_n(v_toBind_5847_, 2);
v_n_5848_ = lean_array_get_size(v_moduleData_5845_);
lean_dec_ref(v_moduleData_5845_);
v___x_5849_ = lean_unsigned_to_nat(0u);
v___x_5850_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5834_, 2);
v___x_5851_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5834_, v_inst_5838_, v_cctx_5839_, v_env_5841_, v_act_5842_, v_constantsPerTask_5843_, v_n_5848_, v_ngen_5840_, v___x_5850_, v___x_5849_, v___x_5849_, v___x_5849_);
v_toPure_5852_ = lean_ctor_get(v_toApplicative_5846_, 1);
lean_inc(v_toPure_5852_);
v___f_5853_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5853_, 0, v_inst_5834_);
lean_closure_set(v___f_5853_, 1, v_inst_5835_);
lean_closure_set(v___f_5853_, 2, v_inst_5836_);
lean_closure_set(v___f_5853_, 3, v_inst_5837_);
v___x_5854_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_5855_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5855_, 0, v___x_5849_);
lean_closure_set(v___f_5855_, 1, v___x_5854_);
lean_closure_set(v___f_5855_, 2, v_toPure_5852_);
lean_closure_set(v___f_5855_, 3, v_toBind_5847_);
lean_closure_set(v___f_5855_, 4, v_inst_5834_);
lean_closure_set(v___f_5855_, 5, v___f_5853_);
v___x_5856_ = lean_apply_4(v_toBind_5847_, lean_box(0), lean_box(0), v___x_5851_, v___f_5855_);
return v___x_5856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5857_, lean_object* v_00_u03b1_5858_, lean_object* v_inst_5859_, lean_object* v_inst_5860_, lean_object* v_inst_5861_, lean_object* v_inst_5862_, lean_object* v_inst_5863_, lean_object* v_cctx_5864_, lean_object* v_ngen_5865_, lean_object* v_env_5866_, lean_object* v_act_5867_, lean_object* v_constantsPerTask_5868_){
_start:
{
lean_object* v___x_5869_; 
v___x_5869_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5859_, v_inst_5860_, v_inst_5861_, v_inst_5862_, v_inst_5863_, v_cctx_5864_, v_ngen_5865_, v_env_5866_, v_act_5867_, v_constantsPerTask_5868_);
return v___x_5869_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5870_ = lean_box(0);
v___x_5871_ = lean_unsigned_to_nat(16u);
v___x_5872_ = lean_mk_array(v___x_5871_, v___x_5870_);
return v___x_5872_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; 
v___x_5873_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5874_ = lean_unsigned_to_nat(0u);
v___x_5875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
lean_ctor_set(v___x_5875_, 1, v___x_5873_);
return v___x_5875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5876_){
_start:
{
lean_object* v_fileName_5877_; lean_object* v_fileMap_5878_; lean_object* v_options_5879_; lean_object* v_maxRecDepth_5880_; lean_object* v_ref_5881_; lean_object* v___x_5883_; uint8_t v_isShared_5884_; uint8_t v_isSharedCheck_5896_; 
v_fileName_5877_ = lean_ctor_get(v_ctx_5876_, 0);
v_fileMap_5878_ = lean_ctor_get(v_ctx_5876_, 1);
v_options_5879_ = lean_ctor_get(v_ctx_5876_, 2);
v_maxRecDepth_5880_ = lean_ctor_get(v_ctx_5876_, 4);
v_ref_5881_ = lean_ctor_get(v_ctx_5876_, 5);
v_isSharedCheck_5896_ = !lean_is_exclusive(v_ctx_5876_);
if (v_isSharedCheck_5896_ == 0)
{
lean_object* v_unused_5897_; lean_object* v_unused_5898_; lean_object* v_unused_5899_; lean_object* v_unused_5900_; lean_object* v_unused_5901_; lean_object* v_unused_5902_; lean_object* v_unused_5903_; lean_object* v_unused_5904_; lean_object* v_unused_5905_; 
v_unused_5897_ = lean_ctor_get(v_ctx_5876_, 13);
lean_dec(v_unused_5897_);
v_unused_5898_ = lean_ctor_get(v_ctx_5876_, 12);
lean_dec(v_unused_5898_);
v_unused_5899_ = lean_ctor_get(v_ctx_5876_, 11);
lean_dec(v_unused_5899_);
v_unused_5900_ = lean_ctor_get(v_ctx_5876_, 10);
lean_dec(v_unused_5900_);
v_unused_5901_ = lean_ctor_get(v_ctx_5876_, 9);
lean_dec(v_unused_5901_);
v_unused_5902_ = lean_ctor_get(v_ctx_5876_, 8);
lean_dec(v_unused_5902_);
v_unused_5903_ = lean_ctor_get(v_ctx_5876_, 7);
lean_dec(v_unused_5903_);
v_unused_5904_ = lean_ctor_get(v_ctx_5876_, 6);
lean_dec(v_unused_5904_);
v_unused_5905_ = lean_ctor_get(v_ctx_5876_, 3);
lean_dec(v_unused_5905_);
v___x_5883_ = v_ctx_5876_;
v_isShared_5884_ = v_isSharedCheck_5896_;
goto v_resetjp_5882_;
}
else
{
lean_inc(v_ref_5881_);
lean_inc(v_maxRecDepth_5880_);
lean_inc(v_options_5879_);
lean_inc(v_fileMap_5878_);
lean_inc(v_fileName_5877_);
lean_dec(v_ctx_5876_);
v___x_5883_ = lean_box(0);
v_isShared_5884_ = v_isSharedCheck_5896_;
goto v_resetjp_5882_;
}
v_resetjp_5882_:
{
lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; uint8_t v___x_5889_; lean_object* v___x_5890_; uint8_t v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5894_; 
v___x_5885_ = lean_unsigned_to_nat(0u);
v___x_5886_ = lean_box(0);
v___x_5887_ = lean_box(0);
v___x_5888_ = l_Lean_firstFrontendMacroScope;
v___x_5889_ = l_Lean_getDiag(v_options_5879_);
v___x_5890_ = lean_box(0);
v___x_5891_ = 0;
v___x_5892_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_5884_ == 0)
{
lean_ctor_set(v___x_5883_, 13, v___x_5892_);
lean_ctor_set(v___x_5883_, 12, v___x_5890_);
lean_ctor_set(v___x_5883_, 11, v___x_5888_);
lean_ctor_set(v___x_5883_, 10, v___x_5886_);
lean_ctor_set(v___x_5883_, 9, v___x_5885_);
lean_ctor_set(v___x_5883_, 8, v___x_5885_);
lean_ctor_set(v___x_5883_, 7, v___x_5887_);
lean_ctor_set(v___x_5883_, 6, v___x_5886_);
lean_ctor_set(v___x_5883_, 3, v___x_5885_);
v___x_5894_ = v___x_5883_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_fileName_5877_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v_fileMap_5878_);
lean_ctor_set(v_reuseFailAlloc_5895_, 2, v_options_5879_);
lean_ctor_set(v_reuseFailAlloc_5895_, 3, v___x_5885_);
lean_ctor_set(v_reuseFailAlloc_5895_, 4, v_maxRecDepth_5880_);
lean_ctor_set(v_reuseFailAlloc_5895_, 5, v_ref_5881_);
lean_ctor_set(v_reuseFailAlloc_5895_, 6, v___x_5886_);
lean_ctor_set(v_reuseFailAlloc_5895_, 7, v___x_5887_);
lean_ctor_set(v_reuseFailAlloc_5895_, 8, v___x_5885_);
lean_ctor_set(v_reuseFailAlloc_5895_, 9, v___x_5885_);
lean_ctor_set(v_reuseFailAlloc_5895_, 10, v___x_5886_);
lean_ctor_set(v_reuseFailAlloc_5895_, 11, v___x_5888_);
lean_ctor_set(v_reuseFailAlloc_5895_, 12, v___x_5890_);
lean_ctor_set(v_reuseFailAlloc_5895_, 13, v___x_5892_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
lean_ctor_set_uint8(v___x_5894_, sizeof(void*)*14, v___x_5889_);
lean_ctor_set_uint8(v___x_5894_, sizeof(void*)*14 + 1, v___x_5891_);
return v___x_5894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5906_, lean_object* v_opts_5907_, lean_object* v_act_5908_, lean_object* v_decl_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; 
lean_inc(v___y_5913_);
lean_inc_ref(v___y_5912_);
lean_inc(v___y_5911_);
lean_inc_ref(v___y_5910_);
v___x_5915_ = lean_apply_4(v_act_5908_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_);
v___x_5916_ = l_Lean_profileitIOUnsafe___redArg(v_category_5906_, v_opts_5907_, v___x_5915_, v_decl_5909_);
return v___x_5916_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5917_, lean_object* v_opts_5918_, lean_object* v_act_5919_, lean_object* v_decl_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_){
_start:
{
lean_object* v_res_5926_; 
v_res_5926_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5917_, v_opts_5918_, v_act_5919_, v_decl_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_);
lean_dec(v___y_5924_);
lean_dec_ref(v___y_5923_);
lean_dec(v___y_5922_);
lean_dec_ref(v___y_5921_);
lean_dec_ref(v_opts_5918_);
lean_dec_ref(v_category_5917_);
return v_res_5926_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_5927_, lean_object* v_category_5928_, lean_object* v_opts_5929_, lean_object* v_act_5930_, lean_object* v_decl_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_){
_start:
{
lean_object* v___x_5937_; 
v___x_5937_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5928_, v_opts_5929_, v_act_5930_, v_decl_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
return v___x_5937_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_5938_, lean_object* v_category_5939_, lean_object* v_opts_5940_, lean_object* v_act_5941_, lean_object* v_decl_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_){
_start:
{
lean_object* v_res_5948_; 
v_res_5948_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_5938_, v_category_5939_, v_opts_5940_, v_act_5941_, v_decl_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_);
lean_dec(v___y_5946_);
lean_dec_ref(v___y_5945_);
lean_dec(v___y_5944_);
lean_dec_ref(v___y_5943_);
lean_dec_ref(v_opts_5940_);
lean_dec_ref(v_category_5939_);
return v_res_5948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_5949_, lean_object* v_env_5950_, lean_object* v_act_5951_, lean_object* v_constantsPerTask_5952_, lean_object* v_n_5953_, lean_object* v_ngen_5954_, lean_object* v_tasks_5955_, lean_object* v_start_5956_, lean_object* v_cnt_5957_, lean_object* v_idx_5958_){
_start:
{
lean_object* v___x_5960_; lean_object* v_moduleData_5961_; lean_object* v___x_5962_; uint8_t v___x_5963_; 
v___x_5960_ = l_Lean_Environment_header(v_env_5950_);
v_moduleData_5961_ = lean_ctor_get(v___x_5960_, 6);
lean_inc_ref(v_moduleData_5961_);
lean_dec_ref(v___x_5960_);
v___x_5962_ = lean_array_get_size(v_moduleData_5961_);
v___x_5963_ = lean_nat_dec_lt(v_idx_5958_, v___x_5962_);
if (v___x_5963_ == 0)
{
uint8_t v___x_5964_; 
lean_dec_ref(v_moduleData_5961_);
lean_dec(v_idx_5958_);
lean_dec(v_cnt_5957_);
v___x_5964_ = lean_nat_dec_lt(v_start_5956_, v_n_5953_);
if (v___x_5964_ == 0)
{
lean_object* v___x_5965_; 
lean_dec(v_start_5956_);
lean_dec_ref(v_ngen_5954_);
lean_dec(v_n_5953_);
lean_dec_ref(v_act_5951_);
lean_dec_ref(v_env_5950_);
lean_dec_ref(v_cctx_5949_);
v___x_5965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5965_, 0, v_tasks_5955_);
return v___x_5965_;
}
else
{
lean_object* v_namePrefix_5966_; lean_object* v_idx_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5981_; 
v_namePrefix_5966_ = lean_ctor_get(v_ngen_5954_, 0);
v_idx_5967_ = lean_ctor_get(v_ngen_5954_, 1);
v_isSharedCheck_5981_ = !lean_is_exclusive(v_ngen_5954_);
if (v_isSharedCheck_5981_ == 0)
{
v___x_5969_ = v_ngen_5954_;
v_isShared_5970_ = v_isSharedCheck_5981_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_idx_5967_);
lean_inc(v_namePrefix_5966_);
lean_dec(v_ngen_5954_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5981_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5974_; 
v___x_5971_ = l_Lean_Name_num___override(v_namePrefix_5966_, v_idx_5967_);
v___x_5972_ = lean_unsigned_to_nat(1u);
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 1, v___x_5972_);
lean_ctor_set(v___x_5969_, 0, v___x_5971_);
v___x_5974_ = v___x_5969_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v___x_5971_);
lean_ctor_set(v_reuseFailAlloc_5980_, 1, v___x_5972_);
v___x_5974_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; 
v___x_5975_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5975_, 0, lean_box(0));
lean_closure_set(v___x_5975_, 1, v_cctx_5949_);
lean_closure_set(v___x_5975_, 2, v___x_5974_);
lean_closure_set(v___x_5975_, 3, v_env_5950_);
lean_closure_set(v___x_5975_, 4, v_act_5951_);
lean_closure_set(v___x_5975_, 5, v_start_5956_);
lean_closure_set(v___x_5975_, 6, v_n_5953_);
v___x_5976_ = lean_unsigned_to_nat(0u);
v___x_5977_ = lean_io_as_task(v___x_5975_, v___x_5976_);
v___x_5978_ = lean_array_push(v_tasks_5955_, v___x_5977_);
v___x_5979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5978_);
return v___x_5979_;
}
}
}
}
else
{
lean_object* v_mdata_5982_; lean_object* v_constants_5983_; lean_object* v___x_5984_; lean_object* v_cnt_5985_; uint8_t v___x_5986_; 
v_mdata_5982_ = lean_array_fget(v_moduleData_5961_, v_idx_5958_);
lean_dec_ref(v_moduleData_5961_);
v_constants_5983_ = lean_ctor_get(v_mdata_5982_, 2);
lean_inc_ref(v_constants_5983_);
lean_dec(v_mdata_5982_);
v___x_5984_ = lean_array_get_size(v_constants_5983_);
lean_dec_ref(v_constants_5983_);
v_cnt_5985_ = lean_nat_add(v_cnt_5957_, v___x_5984_);
lean_dec(v_cnt_5957_);
v___x_5986_ = lean_nat_dec_lt(v_constantsPerTask_5952_, v_cnt_5985_);
if (v___x_5986_ == 0)
{
lean_object* v___x_5987_; lean_object* v___x_5988_; 
v___x_5987_ = lean_unsigned_to_nat(1u);
v___x_5988_ = lean_nat_add(v_idx_5958_, v___x_5987_);
lean_dec(v_idx_5958_);
v_cnt_5957_ = v_cnt_5985_;
v_idx_5958_ = v___x_5988_;
goto _start;
}
else
{
lean_object* v_namePrefix_5990_; lean_object* v_idx_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_6008_; 
lean_dec(v_cnt_5985_);
v_namePrefix_5990_ = lean_ctor_get(v_ngen_5954_, 0);
v_idx_5991_ = lean_ctor_get(v_ngen_5954_, 1);
v_isSharedCheck_6008_ = !lean_is_exclusive(v_ngen_5954_);
if (v_isSharedCheck_6008_ == 0)
{
v___x_5993_ = v_ngen_5954_;
v_isShared_5994_ = v_isSharedCheck_6008_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_idx_5991_);
lean_inc(v_namePrefix_5990_);
lean_dec(v_ngen_5954_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_6008_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5998_; 
lean_inc(v_idx_5991_);
lean_inc(v_namePrefix_5990_);
v___x_5995_ = l_Lean_Name_num___override(v_namePrefix_5990_, v_idx_5991_);
v___x_5996_ = lean_unsigned_to_nat(1u);
if (v_isShared_5994_ == 0)
{
lean_ctor_set(v___x_5993_, 1, v___x_5996_);
lean_ctor_set(v___x_5993_, 0, v___x_5995_);
v___x_5998_ = v___x_5993_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v___x_5995_);
lean_ctor_set(v_reuseFailAlloc_6007_, 1, v___x_5996_);
v___x_5998_ = v_reuseFailAlloc_6007_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_5999_ = lean_nat_add(v_idx_5958_, v___x_5996_);
lean_dec(v_idx_5958_);
lean_inc_n(v___x_5999_, 2);
lean_inc_ref(v_act_5951_);
lean_inc_ref(v_env_5950_);
lean_inc_ref(v_cctx_5949_);
v___x_6000_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6000_, 0, lean_box(0));
lean_closure_set(v___x_6000_, 1, v_cctx_5949_);
lean_closure_set(v___x_6000_, 2, v___x_5998_);
lean_closure_set(v___x_6000_, 3, v_env_5950_);
lean_closure_set(v___x_6000_, 4, v_act_5951_);
lean_closure_set(v___x_6000_, 5, v_start_5956_);
lean_closure_set(v___x_6000_, 6, v___x_5999_);
v___x_6001_ = lean_unsigned_to_nat(0u);
v___x_6002_ = lean_io_as_task(v___x_6000_, v___x_6001_);
v___x_6003_ = lean_nat_add(v_idx_5991_, v___x_5996_);
lean_dec(v_idx_5991_);
v___x_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6004_, 0, v_namePrefix_5990_);
lean_ctor_set(v___x_6004_, 1, v___x_6003_);
v___x_6005_ = lean_array_push(v_tasks_5955_, v___x_6002_);
v_ngen_5954_ = v___x_6004_;
v_tasks_5955_ = v___x_6005_;
v_start_5956_ = v___x_5999_;
v_cnt_5957_ = v___x_6001_;
v_idx_5958_ = v___x_5999_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6009_, lean_object* v_env_6010_, lean_object* v_act_6011_, lean_object* v_constantsPerTask_6012_, lean_object* v_n_6013_, lean_object* v_ngen_6014_, lean_object* v_tasks_6015_, lean_object* v_start_6016_, lean_object* v_cnt_6017_, lean_object* v_idx_6018_, lean_object* v___y_6019_){
_start:
{
lean_object* v_res_6020_; 
v_res_6020_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6009_, v_env_6010_, v_act_6011_, v_constantsPerTask_6012_, v_n_6013_, v_ngen_6014_, v_tasks_6015_, v_start_6016_, v_cnt_6017_, v_idx_6018_);
lean_dec(v_constantsPerTask_6012_);
return v_res_6020_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6029_, uint8_t v___y_6030_, lean_object* v_x_6031_){
_start:
{
if (lean_obj_tag(v_x_6031_) == 1)
{
lean_object* v_pre_6032_; 
v_pre_6032_ = lean_ctor_get(v_x_6031_, 0);
switch(lean_obj_tag(v_pre_6032_))
{
case 1:
{
lean_object* v_pre_6033_; 
v_pre_6033_ = lean_ctor_get(v_pre_6032_, 0);
switch(lean_obj_tag(v_pre_6033_))
{
case 0:
{
lean_object* v_str_6034_; lean_object* v_str_6035_; lean_object* v___x_6036_; uint8_t v___x_6037_; 
v_str_6034_ = lean_ctor_get(v_x_6031_, 1);
v_str_6035_ = lean_ctor_get(v_pre_6032_, 1);
v___x_6036_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6037_ = lean_string_dec_eq(v_str_6035_, v___x_6036_);
if (v___x_6037_ == 0)
{
lean_object* v___x_6038_; uint8_t v___x_6039_; 
v___x_6038_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6039_ = lean_string_dec_eq(v_str_6035_, v___x_6038_);
if (v___x_6039_ == 0)
{
return v___x_6039_;
}
else
{
lean_object* v___x_6040_; uint8_t v___x_6041_; 
v___x_6040_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6041_ = lean_string_dec_eq(v_str_6034_, v___x_6040_);
if (v___x_6041_ == 0)
{
return v___x_6041_;
}
else
{
return v_suppressElabErrors_6029_;
}
}
}
else
{
lean_object* v___x_6042_; uint8_t v___x_6043_; 
v___x_6042_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6043_ = lean_string_dec_eq(v_str_6034_, v___x_6042_);
if (v___x_6043_ == 0)
{
return v___x_6043_;
}
else
{
return v_suppressElabErrors_6029_;
}
}
}
case 1:
{
lean_object* v_pre_6044_; 
v_pre_6044_ = lean_ctor_get(v_pre_6033_, 0);
if (lean_obj_tag(v_pre_6044_) == 0)
{
lean_object* v_str_6045_; lean_object* v_str_6046_; lean_object* v_str_6047_; lean_object* v___x_6048_; uint8_t v___x_6049_; 
v_str_6045_ = lean_ctor_get(v_x_6031_, 1);
v_str_6046_ = lean_ctor_get(v_pre_6032_, 1);
v_str_6047_ = lean_ctor_get(v_pre_6033_, 1);
v___x_6048_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6049_ = lean_string_dec_eq(v_str_6047_, v___x_6048_);
if (v___x_6049_ == 0)
{
return v___x_6049_;
}
else
{
lean_object* v___x_6050_; uint8_t v___x_6051_; 
v___x_6050_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6051_ = lean_string_dec_eq(v_str_6046_, v___x_6050_);
if (v___x_6051_ == 0)
{
return v___x_6051_;
}
else
{
lean_object* v___x_6052_; uint8_t v___x_6053_; 
v___x_6052_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6053_ = lean_string_dec_eq(v_str_6045_, v___x_6052_);
if (v___x_6053_ == 0)
{
return v___x_6053_;
}
else
{
return v_suppressElabErrors_6029_;
}
}
}
}
else
{
return v___y_6030_;
}
}
default: 
{
return v___y_6030_;
}
}
}
case 0:
{
lean_object* v_str_6054_; lean_object* v___x_6055_; uint8_t v___x_6056_; 
v_str_6054_ = lean_ctor_get(v_x_6031_, 1);
v___x_6055_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6056_ = lean_string_dec_eq(v_str_6054_, v___x_6055_);
if (v___x_6056_ == 0)
{
return v___x_6056_;
}
else
{
return v_suppressElabErrors_6029_;
}
}
default: 
{
return v___y_6030_;
}
}
}
else
{
return v___y_6030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6057_, lean_object* v___y_6058_, lean_object* v_x_6059_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6060_; uint8_t v___y_8028__boxed_6061_; uint8_t v_res_6062_; lean_object* v_r_6063_; 
v_suppressElabErrors_boxed_6060_ = lean_unbox(v_suppressElabErrors_6057_);
v___y_8028__boxed_6061_ = lean_unbox(v___y_6058_);
v_res_6062_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6060_, v___y_8028__boxed_6061_, v_x_6059_);
lean_dec(v_x_6059_);
v_r_6063_ = lean_box(v_res_6062_);
return v_r_6063_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6065_, lean_object* v_msgData_6066_, uint8_t v_severity_6067_, uint8_t v_isSilent_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_){
_start:
{
lean_object* v___y_6075_; uint8_t v___y_6076_; lean_object* v___y_6077_; lean_object* v___y_6078_; lean_object* v___y_6079_; lean_object* v___y_6080_; uint8_t v___y_6081_; lean_object* v___y_6082_; lean_object* v___y_6083_; lean_object* v___y_6111_; lean_object* v___y_6112_; uint8_t v___y_6113_; lean_object* v___y_6114_; lean_object* v___y_6115_; uint8_t v___y_6116_; uint8_t v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6136_; uint8_t v___y_6137_; lean_object* v___y_6138_; lean_object* v___y_6139_; uint8_t v___y_6140_; uint8_t v___y_6141_; lean_object* v___y_6142_; lean_object* v___y_6143_; lean_object* v___y_6147_; lean_object* v___y_6148_; uint8_t v___y_6149_; lean_object* v___y_6150_; lean_object* v___y_6151_; uint8_t v___y_6152_; uint8_t v___y_6153_; uint8_t v___x_6158_; lean_object* v___y_6160_; lean_object* v___y_6161_; lean_object* v___y_6162_; uint8_t v___y_6163_; lean_object* v___y_6164_; uint8_t v___y_6165_; uint8_t v___y_6166_; uint8_t v___y_6168_; uint8_t v___x_6183_; 
v___x_6158_ = 2;
v___x_6183_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6067_, v___x_6158_);
if (v___x_6183_ == 0)
{
v___y_6168_ = v___x_6183_;
goto v___jp_6167_;
}
else
{
uint8_t v___x_6184_; 
lean_inc_ref(v_msgData_6066_);
v___x_6184_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6066_);
v___y_6168_ = v___x_6184_;
goto v___jp_6167_;
}
v___jp_6074_:
{
lean_object* v___x_6084_; lean_object* v_currNamespace_6085_; lean_object* v_openDecls_6086_; lean_object* v_env_6087_; lean_object* v_nextMacroScope_6088_; lean_object* v_ngen_6089_; lean_object* v_auxDeclNGen_6090_; lean_object* v_traceState_6091_; lean_object* v_cache_6092_; lean_object* v_messages_6093_; lean_object* v_infoState_6094_; lean_object* v_snapshotTasks_6095_; lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6109_; 
v___x_6084_ = lean_st_ref_take(v___y_6083_);
v_currNamespace_6085_ = lean_ctor_get(v___y_6082_, 6);
v_openDecls_6086_ = lean_ctor_get(v___y_6082_, 7);
v_env_6087_ = lean_ctor_get(v___x_6084_, 0);
v_nextMacroScope_6088_ = lean_ctor_get(v___x_6084_, 1);
v_ngen_6089_ = lean_ctor_get(v___x_6084_, 2);
v_auxDeclNGen_6090_ = lean_ctor_get(v___x_6084_, 3);
v_traceState_6091_ = lean_ctor_get(v___x_6084_, 4);
v_cache_6092_ = lean_ctor_get(v___x_6084_, 5);
v_messages_6093_ = lean_ctor_get(v___x_6084_, 6);
v_infoState_6094_ = lean_ctor_get(v___x_6084_, 7);
v_snapshotTasks_6095_ = lean_ctor_get(v___x_6084_, 8);
v_isSharedCheck_6109_ = !lean_is_exclusive(v___x_6084_);
if (v_isSharedCheck_6109_ == 0)
{
v___x_6097_ = v___x_6084_;
v_isShared_6098_ = v_isSharedCheck_6109_;
goto v_resetjp_6096_;
}
else
{
lean_inc(v_snapshotTasks_6095_);
lean_inc(v_infoState_6094_);
lean_inc(v_messages_6093_);
lean_inc(v_cache_6092_);
lean_inc(v_traceState_6091_);
lean_inc(v_auxDeclNGen_6090_);
lean_inc(v_ngen_6089_);
lean_inc(v_nextMacroScope_6088_);
lean_inc(v_env_6087_);
lean_dec(v___x_6084_);
v___x_6097_ = lean_box(0);
v_isShared_6098_ = v_isSharedCheck_6109_;
goto v_resetjp_6096_;
}
v_resetjp_6096_:
{
lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6104_; 
lean_inc(v_openDecls_6086_);
lean_inc(v_currNamespace_6085_);
v___x_6099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6099_, 0, v_currNamespace_6085_);
lean_ctor_set(v___x_6099_, 1, v_openDecls_6086_);
v___x_6100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___y_6075_);
lean_inc_ref(v___y_6079_);
lean_inc_ref(v___y_6077_);
v___x_6101_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6101_, 0, v___y_6077_);
lean_ctor_set(v___x_6101_, 1, v___y_6078_);
lean_ctor_set(v___x_6101_, 2, v___y_6080_);
lean_ctor_set(v___x_6101_, 3, v___y_6079_);
lean_ctor_set(v___x_6101_, 4, v___x_6100_);
lean_ctor_set_uint8(v___x_6101_, sizeof(void*)*5, v___y_6076_);
lean_ctor_set_uint8(v___x_6101_, sizeof(void*)*5 + 1, v___y_6081_);
lean_ctor_set_uint8(v___x_6101_, sizeof(void*)*5 + 2, v_isSilent_6068_);
v___x_6102_ = l_Lean_MessageLog_add(v___x_6101_, v_messages_6093_);
if (v_isShared_6098_ == 0)
{
lean_ctor_set(v___x_6097_, 6, v___x_6102_);
v___x_6104_ = v___x_6097_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_env_6087_);
lean_ctor_set(v_reuseFailAlloc_6108_, 1, v_nextMacroScope_6088_);
lean_ctor_set(v_reuseFailAlloc_6108_, 2, v_ngen_6089_);
lean_ctor_set(v_reuseFailAlloc_6108_, 3, v_auxDeclNGen_6090_);
lean_ctor_set(v_reuseFailAlloc_6108_, 4, v_traceState_6091_);
lean_ctor_set(v_reuseFailAlloc_6108_, 5, v_cache_6092_);
lean_ctor_set(v_reuseFailAlloc_6108_, 6, v___x_6102_);
lean_ctor_set(v_reuseFailAlloc_6108_, 7, v_infoState_6094_);
lean_ctor_set(v_reuseFailAlloc_6108_, 8, v_snapshotTasks_6095_);
v___x_6104_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6105_ = lean_st_ref_put(v___y_6083_, v___x_6104_);
v___x_6106_ = lean_box(0);
v___x_6107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
return v___x_6107_;
}
}
}
v___jp_6110_:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v_a_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6134_; 
v___x_6119_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6066_);
v___x_6120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6119_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
v_a_6121_ = lean_ctor_get(v___x_6120_, 0);
v_isSharedCheck_6134_ = !lean_is_exclusive(v___x_6120_);
if (v_isSharedCheck_6134_ == 0)
{
v___x_6123_ = v___x_6120_;
v_isShared_6124_ = v_isSharedCheck_6134_;
goto v_resetjp_6122_;
}
else
{
lean_inc(v_a_6121_);
lean_dec(v___x_6120_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6134_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
lean_inc_ref_n(v___y_6115_, 2);
v___x_6125_ = l_Lean_FileMap_toPosition(v___y_6115_, v___y_6114_);
lean_dec(v___y_6114_);
v___x_6126_ = l_Lean_FileMap_toPosition(v___y_6115_, v___y_6118_);
lean_dec(v___y_6118_);
v___x_6127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
v___x_6128_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6116_ == 0)
{
lean_del_object(v___x_6123_);
lean_dec_ref(v___y_6111_);
v___y_6075_ = v_a_6121_;
v___y_6076_ = v___y_6113_;
v___y_6077_ = v___y_6112_;
v___y_6078_ = v___x_6125_;
v___y_6079_ = v___x_6128_;
v___y_6080_ = v___x_6127_;
v___y_6081_ = v___y_6117_;
v___y_6082_ = v___y_6071_;
v___y_6083_ = v___y_6072_;
goto v___jp_6074_;
}
else
{
uint8_t v___x_6129_; 
lean_inc(v_a_6121_);
v___x_6129_ = l_Lean_MessageData_hasTag(v___y_6111_, v_a_6121_);
if (v___x_6129_ == 0)
{
lean_object* v___x_6130_; lean_object* v___x_6132_; 
lean_dec_ref_known(v___x_6127_, 1);
lean_dec_ref(v___x_6125_);
lean_dec(v_a_6121_);
v___x_6130_ = lean_box(0);
if (v_isShared_6124_ == 0)
{
lean_ctor_set(v___x_6123_, 0, v___x_6130_);
v___x_6132_ = v___x_6123_;
goto v_reusejp_6131_;
}
else
{
lean_object* v_reuseFailAlloc_6133_; 
v_reuseFailAlloc_6133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6133_, 0, v___x_6130_);
v___x_6132_ = v_reuseFailAlloc_6133_;
goto v_reusejp_6131_;
}
v_reusejp_6131_:
{
return v___x_6132_;
}
}
else
{
lean_del_object(v___x_6123_);
v___y_6075_ = v_a_6121_;
v___y_6076_ = v___y_6113_;
v___y_6077_ = v___y_6112_;
v___y_6078_ = v___x_6125_;
v___y_6079_ = v___x_6128_;
v___y_6080_ = v___x_6127_;
v___y_6081_ = v___y_6117_;
v___y_6082_ = v___y_6071_;
v___y_6083_ = v___y_6072_;
goto v___jp_6074_;
}
}
}
}
v___jp_6135_:
{
lean_object* v___x_6144_; 
v___x_6144_ = l_Lean_Syntax_getTailPos_x3f(v___y_6142_, v___y_6137_);
lean_dec(v___y_6142_);
if (lean_obj_tag(v___x_6144_) == 0)
{
lean_inc(v___y_6143_);
v___y_6111_ = v___y_6136_;
v___y_6112_ = v___y_6138_;
v___y_6113_ = v___y_6137_;
v___y_6114_ = v___y_6143_;
v___y_6115_ = v___y_6139_;
v___y_6116_ = v___y_6140_;
v___y_6117_ = v___y_6141_;
v___y_6118_ = v___y_6143_;
goto v___jp_6110_;
}
else
{
lean_object* v_val_6145_; 
v_val_6145_ = lean_ctor_get(v___x_6144_, 0);
lean_inc(v_val_6145_);
lean_dec_ref_known(v___x_6144_, 1);
v___y_6111_ = v___y_6136_;
v___y_6112_ = v___y_6138_;
v___y_6113_ = v___y_6137_;
v___y_6114_ = v___y_6143_;
v___y_6115_ = v___y_6139_;
v___y_6116_ = v___y_6140_;
v___y_6117_ = v___y_6141_;
v___y_6118_ = v_val_6145_;
goto v___jp_6110_;
}
}
v___jp_6146_:
{
lean_object* v_ref_6154_; lean_object* v___x_6155_; 
v_ref_6154_ = l_Lean_replaceRef(v_ref_6065_, v___y_6150_);
v___x_6155_ = l_Lean_Syntax_getPos_x3f(v_ref_6154_, v___y_6149_);
if (lean_obj_tag(v___x_6155_) == 0)
{
lean_object* v___x_6156_; 
v___x_6156_ = lean_unsigned_to_nat(0u);
v___y_6136_ = v___y_6147_;
v___y_6137_ = v___y_6149_;
v___y_6138_ = v___y_6148_;
v___y_6139_ = v___y_6151_;
v___y_6140_ = v___y_6152_;
v___y_6141_ = v___y_6153_;
v___y_6142_ = v_ref_6154_;
v___y_6143_ = v___x_6156_;
goto v___jp_6135_;
}
else
{
lean_object* v_val_6157_; 
v_val_6157_ = lean_ctor_get(v___x_6155_, 0);
lean_inc(v_val_6157_);
lean_dec_ref_known(v___x_6155_, 1);
v___y_6136_ = v___y_6147_;
v___y_6137_ = v___y_6149_;
v___y_6138_ = v___y_6148_;
v___y_6139_ = v___y_6151_;
v___y_6140_ = v___y_6152_;
v___y_6141_ = v___y_6153_;
v___y_6142_ = v_ref_6154_;
v___y_6143_ = v_val_6157_;
goto v___jp_6135_;
}
}
v___jp_6159_:
{
if (v___y_6166_ == 0)
{
v___y_6147_ = v___y_6164_;
v___y_6148_ = v___y_6161_;
v___y_6149_ = v___y_6165_;
v___y_6150_ = v___y_6160_;
v___y_6151_ = v___y_6162_;
v___y_6152_ = v___y_6163_;
v___y_6153_ = v_severity_6067_;
goto v___jp_6146_;
}
else
{
v___y_6147_ = v___y_6164_;
v___y_6148_ = v___y_6161_;
v___y_6149_ = v___y_6165_;
v___y_6150_ = v___y_6160_;
v___y_6151_ = v___y_6162_;
v___y_6152_ = v___y_6163_;
v___y_6153_ = v___x_6158_;
goto v___jp_6146_;
}
}
v___jp_6167_:
{
if (v___y_6168_ == 0)
{
lean_object* v_fileName_6169_; lean_object* v_fileMap_6170_; lean_object* v_options_6171_; lean_object* v_ref_6172_; uint8_t v_suppressElabErrors_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___f_6176_; uint8_t v___x_6177_; uint8_t v___x_6178_; 
v_fileName_6169_ = lean_ctor_get(v___y_6071_, 0);
v_fileMap_6170_ = lean_ctor_get(v___y_6071_, 1);
v_options_6171_ = lean_ctor_get(v___y_6071_, 2);
v_ref_6172_ = lean_ctor_get(v___y_6071_, 5);
v_suppressElabErrors_6173_ = lean_ctor_get_uint8(v___y_6071_, sizeof(void*)*14 + 1);
v___x_6174_ = lean_box(v_suppressElabErrors_6173_);
v___x_6175_ = lean_box(v___y_6168_);
v___f_6176_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6176_, 0, v___x_6174_);
lean_closure_set(v___f_6176_, 1, v___x_6175_);
v___x_6177_ = 1;
v___x_6178_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6067_, v___x_6177_);
if (v___x_6178_ == 0)
{
v___y_6160_ = v_ref_6172_;
v___y_6161_ = v_fileName_6169_;
v___y_6162_ = v_fileMap_6170_;
v___y_6163_ = v_suppressElabErrors_6173_;
v___y_6164_ = v___f_6176_;
v___y_6165_ = v___y_6168_;
v___y_6166_ = v___x_6178_;
goto v___jp_6159_;
}
else
{
lean_object* v___x_6179_; uint8_t v___x_6180_; 
v___x_6179_ = l_Lean_warningAsError;
v___x_6180_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6171_, v___x_6179_);
v___y_6160_ = v_ref_6172_;
v___y_6161_ = v_fileName_6169_;
v___y_6162_ = v_fileMap_6170_;
v___y_6163_ = v_suppressElabErrors_6173_;
v___y_6164_ = v___f_6176_;
v___y_6165_ = v___y_6168_;
v___y_6166_ = v___x_6180_;
goto v___jp_6159_;
}
}
else
{
lean_object* v___x_6181_; lean_object* v___x_6182_; 
lean_dec_ref(v_msgData_6066_);
v___x_6181_ = lean_box(0);
v___x_6182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6181_);
return v___x_6182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6185_, lean_object* v_msgData_6186_, lean_object* v_severity_6187_, lean_object* v_isSilent_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_){
_start:
{
uint8_t v_severity_boxed_6194_; uint8_t v_isSilent_boxed_6195_; lean_object* v_res_6196_; 
v_severity_boxed_6194_ = lean_unbox(v_severity_6187_);
v_isSilent_boxed_6195_ = lean_unbox(v_isSilent_6188_);
v_res_6196_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6185_, v_msgData_6186_, v_severity_boxed_6194_, v_isSilent_boxed_6195_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec(v_ref_6185_);
return v_res_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6197_, uint8_t v_severity_6198_, uint8_t v_isSilent_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_){
_start:
{
lean_object* v_ref_6205_; lean_object* v___x_6206_; 
v_ref_6205_ = lean_ctor_get(v___y_6202_, 5);
v___x_6206_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6205_, v_msgData_6197_, v_severity_6198_, v_isSilent_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_);
return v___x_6206_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6207_, lean_object* v_severity_6208_, lean_object* v_isSilent_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_){
_start:
{
uint8_t v_severity_boxed_6215_; uint8_t v_isSilent_boxed_6216_; lean_object* v_res_6217_; 
v_severity_boxed_6215_ = lean_unbox(v_severity_6208_);
v_isSilent_boxed_6216_ = lean_unbox(v_isSilent_6209_);
v_res_6217_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6207_, v_severity_boxed_6215_, v_isSilent_boxed_6216_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
lean_dec(v___y_6213_);
lean_dec_ref(v___y_6212_);
lean_dec(v___y_6211_);
lean_dec_ref(v___y_6210_);
return v_res_6217_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_){
_start:
{
uint8_t v___x_6224_; uint8_t v___x_6225_; lean_object* v___x_6226_; 
v___x_6224_ = 2;
v___x_6225_ = 0;
v___x_6226_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6218_, v___x_6224_, v___x_6225_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_){
_start:
{
lean_object* v_res_6233_; 
v_res_6233_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_);
lean_dec(v___y_6231_);
lean_dec_ref(v___y_6230_);
lean_dec(v___y_6229_);
lean_dec_ref(v___y_6228_);
return v_res_6233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_){
_start:
{
lean_object* v_module_6240_; lean_object* v_const_6241_; lean_object* v_exception_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; 
v_module_6240_ = lean_ctor_get(v_f_6234_, 0);
lean_inc(v_module_6240_);
v_const_6241_ = lean_ctor_get(v_f_6234_, 1);
lean_inc(v_const_6241_);
v_exception_6242_ = lean_ctor_get(v_f_6234_, 2);
lean_inc_ref(v_exception_6242_);
lean_dec_ref(v_f_6234_);
v___x_6243_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6244_ = l_Lean_MessageData_ofName(v_const_6241_);
v___x_6245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6245_, 0, v___x_6243_);
lean_ctor_set(v___x_6245_, 1, v___x_6244_);
v___x_6246_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6247_, 0, v___x_6245_);
lean_ctor_set(v___x_6247_, 1, v___x_6246_);
v___x_6248_ = l_Lean_MessageData_ofName(v_module_6240_);
v___x_6249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6249_, 0, v___x_6247_);
lean_ctor_set(v___x_6249_, 1, v___x_6248_);
v___x_6250_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6251_, 0, v___x_6249_);
lean_ctor_set(v___x_6251_, 1, v___x_6250_);
v___x_6252_ = l_Lean_Exception_toMessageData(v_exception_6242_);
v___x_6253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6253_, 0, v___x_6251_);
lean_ctor_set(v___x_6253_, 1, v___x_6252_);
v___x_6254_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6253_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
return v___x_6254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_){
_start:
{
lean_object* v_res_6261_; 
v_res_6261_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
lean_dec(v___y_6259_);
lean_dec_ref(v___y_6258_);
lean_dec(v___y_6257_);
lean_dec_ref(v___y_6256_);
return v_res_6261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6262_, size_t v_i_6263_, size_t v_stop_6264_, lean_object* v_b_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_){
_start:
{
uint8_t v___x_6271_; 
v___x_6271_ = lean_usize_dec_eq(v_i_6263_, v_stop_6264_);
if (v___x_6271_ == 0)
{
lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6272_ = lean_array_uget_borrowed(v_as_6262_, v_i_6263_);
lean_inc(v___x_6272_);
v___x_6273_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6272_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_);
if (lean_obj_tag(v___x_6273_) == 0)
{
lean_object* v_a_6274_; size_t v___x_6275_; size_t v___x_6276_; 
v_a_6274_ = lean_ctor_get(v___x_6273_, 0);
lean_inc(v_a_6274_);
lean_dec_ref_known(v___x_6273_, 1);
v___x_6275_ = ((size_t)1ULL);
v___x_6276_ = lean_usize_add(v_i_6263_, v___x_6275_);
v_i_6263_ = v___x_6276_;
v_b_6265_ = v_a_6274_;
goto _start;
}
else
{
return v___x_6273_;
}
}
else
{
lean_object* v___x_6278_; 
v___x_6278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6278_, 0, v_b_6265_);
return v___x_6278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6279_, lean_object* v_i_6280_, lean_object* v_stop_6281_, lean_object* v_b_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_){
_start:
{
size_t v_i_boxed_6288_; size_t v_stop_boxed_6289_; lean_object* v_res_6290_; 
v_i_boxed_6288_ = lean_unbox_usize(v_i_6280_);
lean_dec(v_i_6280_);
v_stop_boxed_6289_ = lean_unbox_usize(v_stop_6281_);
lean_dec(v_stop_6281_);
v_res_6290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6279_, v_i_boxed_6288_, v_stop_boxed_6289_, v_b_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_);
lean_dec(v___y_6286_);
lean_dec_ref(v___y_6285_);
lean_dec(v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec_ref(v_as_6279_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6291_, size_t v_i_6292_, size_t v_stop_6293_, lean_object* v_b_6294_){
_start:
{
uint8_t v___x_6295_; 
v___x_6295_ = lean_usize_dec_eq(v_i_6292_, v_stop_6293_);
if (v___x_6295_ == 0)
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; size_t v___x_6299_; size_t v___x_6300_; 
v___x_6296_ = lean_array_uget_borrowed(v_as_6291_, v_i_6292_);
lean_inc(v___x_6296_);
v___x_6297_ = lean_task_get_own(v___x_6296_);
v___x_6298_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6294_, v___x_6297_);
v___x_6299_ = ((size_t)1ULL);
v___x_6300_ = lean_usize_add(v_i_6292_, v___x_6299_);
v_i_6292_ = v___x_6300_;
v_b_6294_ = v___x_6298_;
goto _start;
}
else
{
return v_b_6294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6302_, lean_object* v_i_6303_, lean_object* v_stop_6304_, lean_object* v_b_6305_){
_start:
{
size_t v_i_boxed_6306_; size_t v_stop_boxed_6307_; lean_object* v_res_6308_; 
v_i_boxed_6306_ = lean_unbox_usize(v_i_6303_);
lean_dec(v_i_6303_);
v_stop_boxed_6307_ = lean_unbox_usize(v_stop_6304_);
lean_dec(v_stop_6304_);
v_res_6308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6302_, v_i_boxed_6306_, v_stop_boxed_6307_, v_b_6305_);
lean_dec_ref(v_as_6302_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6309_, lean_object* v_tasks_6310_){
_start:
{
lean_object* v___x_6311_; lean_object* v___x_6312_; uint8_t v___x_6313_; 
v___x_6311_ = lean_unsigned_to_nat(0u);
v___x_6312_ = lean_array_get_size(v_tasks_6310_);
v___x_6313_ = lean_nat_dec_lt(v___x_6311_, v___x_6312_);
if (v___x_6313_ == 0)
{
return v_z_6309_;
}
else
{
size_t v___x_6314_; size_t v___x_6315_; lean_object* v___x_6316_; 
v___x_6314_ = ((size_t)0ULL);
v___x_6315_ = lean_usize_of_nat(v___x_6312_);
v___x_6316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6310_, v___x_6314_, v___x_6315_, v_z_6309_);
return v___x_6316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6317_, lean_object* v_tasks_6318_){
_start:
{
lean_object* v_res_6319_; 
v_res_6319_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6317_, v_tasks_6318_);
lean_dec_ref(v_tasks_6318_);
return v_res_6319_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6320_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6321_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6322_, 0, v___x_6321_);
lean_ctor_set(v___x_6322_, 1, v___x_6320_);
return v___x_6322_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; 
v___x_6323_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6324_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6325_, 0, v___x_6324_);
lean_ctor_set(v___x_6325_, 1, v___x_6323_);
return v___x_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6326_, lean_object* v_ngen_6327_, lean_object* v_env_6328_, lean_object* v_act_6329_, lean_object* v_constantsPerTask_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_){
_start:
{
lean_object* v___x_6336_; lean_object* v_moduleData_6337_; lean_object* v_n_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v_a_6342_; lean_object* v___x_6344_; uint8_t v_isShared_6345_; uint8_t v_isSharedCheck_6377_; 
v___x_6336_ = l_Lean_Environment_header(v_env_6328_);
v_moduleData_6337_ = lean_ctor_get(v___x_6336_, 6);
lean_inc_ref(v_moduleData_6337_);
lean_dec_ref(v___x_6336_);
v_n_6338_ = lean_array_get_size(v_moduleData_6337_);
lean_dec_ref(v_moduleData_6337_);
v___x_6339_ = lean_unsigned_to_nat(0u);
v___x_6340_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6341_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6326_, v_env_6328_, v_act_6329_, v_constantsPerTask_6330_, v_n_6338_, v_ngen_6327_, v___x_6340_, v___x_6339_, v___x_6339_, v___x_6339_);
v_a_6342_ = lean_ctor_get(v___x_6341_, 0);
v_isSharedCheck_6377_ = !lean_is_exclusive(v___x_6341_);
if (v_isSharedCheck_6377_ == 0)
{
v___x_6344_ = v___x_6341_;
v_isShared_6345_ = v_isSharedCheck_6377_;
goto v_resetjp_6343_;
}
else
{
lean_inc(v_a_6342_);
lean_dec(v___x_6341_);
v___x_6344_ = lean_box(0);
v_isShared_6345_ = v_isSharedCheck_6377_;
goto v_resetjp_6343_;
}
v_resetjp_6343_:
{
lean_object* v___x_6346_; lean_object* v_r_6347_; lean_object* v_tree_6348_; lean_object* v_errors_6349_; lean_object* v___x_6350_; uint8_t v___x_6351_; 
v___x_6346_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6347_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6346_, v_a_6342_);
lean_dec(v_a_6342_);
v_tree_6348_ = lean_ctor_get(v_r_6347_, 0);
lean_inc_ref(v_tree_6348_);
v_errors_6349_ = lean_ctor_get(v_r_6347_, 1);
lean_inc_ref(v_errors_6349_);
lean_dec_ref(v_r_6347_);
v___x_6350_ = lean_array_get_size(v_errors_6349_);
v___x_6351_ = lean_nat_dec_lt(v___x_6339_, v___x_6350_);
if (v___x_6351_ == 0)
{
lean_object* v___x_6352_; lean_object* v___x_6354_; 
lean_dec_ref(v_errors_6349_);
v___x_6352_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6348_);
if (v_isShared_6345_ == 0)
{
lean_ctor_set(v___x_6344_, 0, v___x_6352_);
v___x_6354_ = v___x_6344_;
goto v_reusejp_6353_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v___x_6352_);
v___x_6354_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6353_;
}
v_reusejp_6353_:
{
return v___x_6354_;
}
}
else
{
lean_object* v___x_6356_; size_t v___x_6357_; size_t v___x_6358_; lean_object* v___x_6359_; 
lean_del_object(v___x_6344_);
v___x_6356_ = lean_box(0);
v___x_6357_ = ((size_t)0ULL);
v___x_6358_ = lean_usize_of_nat(v___x_6350_);
v___x_6359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6349_, v___x_6357_, v___x_6358_, v___x_6356_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
lean_dec_ref(v_errors_6349_);
if (lean_obj_tag(v___x_6359_) == 0)
{
lean_object* v___x_6361_; uint8_t v_isShared_6362_; uint8_t v_isSharedCheck_6367_; 
v_isSharedCheck_6367_ = !lean_is_exclusive(v___x_6359_);
if (v_isSharedCheck_6367_ == 0)
{
lean_object* v_unused_6368_; 
v_unused_6368_ = lean_ctor_get(v___x_6359_, 0);
lean_dec(v_unused_6368_);
v___x_6361_ = v___x_6359_;
v_isShared_6362_ = v_isSharedCheck_6367_;
goto v_resetjp_6360_;
}
else
{
lean_dec(v___x_6359_);
v___x_6361_ = lean_box(0);
v_isShared_6362_ = v_isSharedCheck_6367_;
goto v_resetjp_6360_;
}
v_resetjp_6360_:
{
lean_object* v___x_6363_; lean_object* v___x_6365_; 
v___x_6363_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6348_);
if (v_isShared_6362_ == 0)
{
lean_ctor_set(v___x_6361_, 0, v___x_6363_);
v___x_6365_ = v___x_6361_;
goto v_reusejp_6364_;
}
else
{
lean_object* v_reuseFailAlloc_6366_; 
v_reuseFailAlloc_6366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6366_, 0, v___x_6363_);
v___x_6365_ = v_reuseFailAlloc_6366_;
goto v_reusejp_6364_;
}
v_reusejp_6364_:
{
return v___x_6365_;
}
}
}
else
{
lean_object* v_a_6369_; lean_object* v___x_6371_; uint8_t v_isShared_6372_; uint8_t v_isSharedCheck_6376_; 
lean_dec_ref(v_tree_6348_);
v_a_6369_ = lean_ctor_get(v___x_6359_, 0);
v_isSharedCheck_6376_ = !lean_is_exclusive(v___x_6359_);
if (v_isSharedCheck_6376_ == 0)
{
v___x_6371_ = v___x_6359_;
v_isShared_6372_ = v_isSharedCheck_6376_;
goto v_resetjp_6370_;
}
else
{
lean_inc(v_a_6369_);
lean_dec(v___x_6359_);
v___x_6371_ = lean_box(0);
v_isShared_6372_ = v_isSharedCheck_6376_;
goto v_resetjp_6370_;
}
v_resetjp_6370_:
{
lean_object* v___x_6374_; 
if (v_isShared_6372_ == 0)
{
v___x_6374_ = v___x_6371_;
goto v_reusejp_6373_;
}
else
{
lean_object* v_reuseFailAlloc_6375_; 
v_reuseFailAlloc_6375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6375_, 0, v_a_6369_);
v___x_6374_ = v_reuseFailAlloc_6375_;
goto v_reusejp_6373_;
}
v_reusejp_6373_:
{
return v___x_6374_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6378_, lean_object* v_ngen_6379_, lean_object* v_env_6380_, lean_object* v_act_6381_, lean_object* v_constantsPerTask_6382_, lean_object* v___y_6383_, lean_object* v___y_6384_, lean_object* v___y_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_){
_start:
{
lean_object* v_res_6388_; 
v_res_6388_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6378_, v_ngen_6379_, v_env_6380_, v_act_6381_, v_constantsPerTask_6382_, v___y_6383_, v___y_6384_, v___y_6385_, v___y_6386_);
lean_dec(v___y_6386_);
lean_dec_ref(v___y_6385_);
lean_dec(v___y_6384_);
lean_dec_ref(v___y_6383_);
lean_dec(v_constantsPerTask_6382_);
return v_res_6388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6389_, lean_object* v___x_6390_, lean_object* v_addEntry_6391_, lean_object* v_constantsPerTask_6392_, lean_object* v_droppedEntriesRef_6393_, lean_object* v_droppedKeys_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_, lean_object* v___y_6397_, lean_object* v___y_6398_){
_start:
{
lean_object* v___x_6400_; lean_object* v_env_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; 
v___x_6400_ = lean_st_ref_get(v___y_6398_);
v_env_6401_ = lean_ctor_get(v___x_6400_, 0);
lean_inc_ref(v_env_6401_);
lean_dec(v___x_6400_);
lean_inc_ref(v_a_6389_);
v___x_6402_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6389_);
v___x_6403_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6402_, v___x_6390_, v_env_6401_, v_addEntry_6391_, v_constantsPerTask_6392_, v___y_6395_, v___y_6396_, v___y_6397_, v___y_6398_);
if (lean_obj_tag(v___x_6403_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6393_) == 1)
{
lean_object* v_a_6404_; lean_object* v_val_6405_; lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6438_; 
v_a_6404_ = lean_ctor_get(v___x_6403_, 0);
lean_inc(v_a_6404_);
lean_dec_ref_known(v___x_6403_, 1);
v_val_6405_ = lean_ctor_get(v_droppedEntriesRef_6393_, 0);
v_isSharedCheck_6438_ = !lean_is_exclusive(v_droppedEntriesRef_6393_);
if (v_isSharedCheck_6438_ == 0)
{
v___x_6407_ = v_droppedEntriesRef_6393_;
v_isShared_6408_ = v_isSharedCheck_6438_;
goto v_resetjp_6406_;
}
else
{
lean_inc(v_val_6405_);
lean_dec(v_droppedEntriesRef_6393_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6438_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___x_6409_; 
v___x_6409_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6404_, v_droppedKeys_6394_, v___y_6395_, v___y_6396_, v___y_6397_, v___y_6398_);
lean_dec(v_droppedKeys_6394_);
if (lean_obj_tag(v___x_6409_) == 0)
{
lean_object* v_a_6410_; lean_object* v___x_6412_; uint8_t v_isShared_6413_; uint8_t v_isSharedCheck_6429_; 
v_a_6410_ = lean_ctor_get(v___x_6409_, 0);
v_isSharedCheck_6429_ = !lean_is_exclusive(v___x_6409_);
if (v_isSharedCheck_6429_ == 0)
{
v___x_6412_ = v___x_6409_;
v_isShared_6413_ = v_isSharedCheck_6429_;
goto v_resetjp_6411_;
}
else
{
lean_inc(v_a_6410_);
lean_dec(v___x_6409_);
v___x_6412_ = lean_box(0);
v_isShared_6413_ = v_isSharedCheck_6429_;
goto v_resetjp_6411_;
}
v_resetjp_6411_:
{
lean_object* v_fst_6414_; lean_object* v_snd_6415_; lean_object* v___x_6416_; lean_object* v___y_6418_; 
v_fst_6414_ = lean_ctor_get(v_a_6410_, 0);
lean_inc(v_fst_6414_);
v_snd_6415_ = lean_ctor_get(v_a_6410_, 1);
lean_inc(v_snd_6415_);
lean_dec(v_a_6410_);
v___x_6416_ = lean_st_ref_get(v_val_6405_);
if (lean_obj_tag(v___x_6416_) == 0)
{
lean_object* v___x_6427_; 
v___x_6427_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6418_ = v___x_6427_;
goto v___jp_6417_;
}
else
{
lean_object* v_val_6428_; 
v_val_6428_ = lean_ctor_get(v___x_6416_, 0);
lean_inc(v_val_6428_);
lean_dec_ref_known(v___x_6416_, 1);
v___y_6418_ = v_val_6428_;
goto v___jp_6417_;
}
v___jp_6417_:
{
lean_object* v___x_6419_; lean_object* v___x_6421_; 
v___x_6419_ = l_Array_append___redArg(v___y_6418_, v_fst_6414_);
lean_dec(v_fst_6414_);
if (v_isShared_6408_ == 0)
{
lean_ctor_set(v___x_6407_, 0, v___x_6419_);
v___x_6421_ = v___x_6407_;
goto v_reusejp_6420_;
}
else
{
lean_object* v_reuseFailAlloc_6426_; 
v_reuseFailAlloc_6426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6426_, 0, v___x_6419_);
v___x_6421_ = v_reuseFailAlloc_6426_;
goto v_reusejp_6420_;
}
v_reusejp_6420_:
{
lean_object* v___x_6422_; lean_object* v___x_6424_; 
v___x_6422_ = lean_st_ref_swap(v_val_6405_, v___x_6421_);
lean_dec(v_val_6405_);
lean_dec(v___x_6422_);
if (v_isShared_6413_ == 0)
{
lean_ctor_set(v___x_6412_, 0, v_snd_6415_);
v___x_6424_ = v___x_6412_;
goto v_reusejp_6423_;
}
else
{
lean_object* v_reuseFailAlloc_6425_; 
v_reuseFailAlloc_6425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6425_, 0, v_snd_6415_);
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
else
{
lean_object* v_a_6430_; lean_object* v___x_6432_; uint8_t v_isShared_6433_; uint8_t v_isSharedCheck_6437_; 
lean_del_object(v___x_6407_);
lean_dec(v_val_6405_);
v_a_6430_ = lean_ctor_get(v___x_6409_, 0);
v_isSharedCheck_6437_ = !lean_is_exclusive(v___x_6409_);
if (v_isSharedCheck_6437_ == 0)
{
v___x_6432_ = v___x_6409_;
v_isShared_6433_ = v_isSharedCheck_6437_;
goto v_resetjp_6431_;
}
else
{
lean_inc(v_a_6430_);
lean_dec(v___x_6409_);
v___x_6432_ = lean_box(0);
v_isShared_6433_ = v_isSharedCheck_6437_;
goto v_resetjp_6431_;
}
v_resetjp_6431_:
{
lean_object* v___x_6435_; 
if (v_isShared_6433_ == 0)
{
v___x_6435_ = v___x_6432_;
goto v_reusejp_6434_;
}
else
{
lean_object* v_reuseFailAlloc_6436_; 
v_reuseFailAlloc_6436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_a_6430_);
v___x_6435_ = v_reuseFailAlloc_6436_;
goto v_reusejp_6434_;
}
v_reusejp_6434_:
{
return v___x_6435_;
}
}
}
}
}
else
{
lean_object* v_a_6439_; lean_object* v___x_6440_; 
lean_dec(v_droppedEntriesRef_6393_);
v_a_6439_ = lean_ctor_get(v___x_6403_, 0);
lean_inc(v_a_6439_);
lean_dec_ref_known(v___x_6403_, 1);
v___x_6440_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6439_, v_droppedKeys_6394_, v___y_6395_, v___y_6396_, v___y_6397_, v___y_6398_);
return v___x_6440_;
}
}
else
{
lean_dec(v_droppedKeys_6394_);
lean_dec(v_droppedEntriesRef_6393_);
return v___x_6403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6441_, lean_object* v___x_6442_, lean_object* v_addEntry_6443_, lean_object* v_constantsPerTask_6444_, lean_object* v_droppedEntriesRef_6445_, lean_object* v_droppedKeys_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_){
_start:
{
lean_object* v_res_6452_; 
v_res_6452_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6441_, v___x_6442_, v_addEntry_6443_, v_constantsPerTask_6444_, v_droppedEntriesRef_6445_, v_droppedKeys_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_);
lean_dec(v___y_6450_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6448_);
lean_dec_ref(v___y_6447_);
lean_dec(v_constantsPerTask_6444_);
lean_dec_ref(v_a_6441_);
return v_res_6452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6454_, lean_object* v_addEntry_6455_, lean_object* v_droppedKeys_6456_, lean_object* v_constantsPerTask_6457_, lean_object* v_droppedEntriesRef_6458_, lean_object* v_ty_6459_, lean_object* v_a_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_){
_start:
{
lean_object* v_a_6466_; lean_object* v___x_6488_; lean_object* v_ngen_6489_; lean_object* v_namePrefix_6490_; lean_object* v_idx_6491_; lean_object* v___x_6493_; uint8_t v_isShared_6494_; uint8_t v_isSharedCheck_6536_; 
v___x_6488_ = lean_st_ref_get(v_a_6463_);
v_ngen_6489_ = lean_ctor_get(v___x_6488_, 2);
lean_inc_ref(v_ngen_6489_);
lean_dec(v___x_6488_);
v_namePrefix_6490_ = lean_ctor_get(v_ngen_6489_, 0);
v_idx_6491_ = lean_ctor_get(v_ngen_6489_, 1);
v_isSharedCheck_6536_ = !lean_is_exclusive(v_ngen_6489_);
if (v_isSharedCheck_6536_ == 0)
{
v___x_6493_ = v_ngen_6489_;
v_isShared_6494_ = v_isSharedCheck_6536_;
goto v_resetjp_6492_;
}
else
{
lean_inc(v_idx_6491_);
lean_inc(v_namePrefix_6490_);
lean_dec(v_ngen_6489_);
v___x_6493_ = lean_box(0);
v_isShared_6494_ = v_isSharedCheck_6536_;
goto v_resetjp_6492_;
}
v___jp_6465_:
{
lean_object* v___x_6467_; 
v___x_6467_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6466_, v_ty_6459_, v_a_6460_, v_a_6461_, v_a_6462_, v_a_6463_);
if (lean_obj_tag(v___x_6467_) == 0)
{
lean_object* v_a_6468_; lean_object* v___x_6470_; uint8_t v_isShared_6471_; uint8_t v_isSharedCheck_6479_; 
v_a_6468_ = lean_ctor_get(v___x_6467_, 0);
v_isSharedCheck_6479_ = !lean_is_exclusive(v___x_6467_);
if (v_isSharedCheck_6479_ == 0)
{
v___x_6470_ = v___x_6467_;
v_isShared_6471_ = v_isSharedCheck_6479_;
goto v_resetjp_6469_;
}
else
{
lean_inc(v_a_6468_);
lean_dec(v___x_6467_);
v___x_6470_ = lean_box(0);
v_isShared_6471_ = v_isSharedCheck_6479_;
goto v_resetjp_6469_;
}
v_resetjp_6469_:
{
lean_object* v_fst_6472_; lean_object* v_snd_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6477_; 
v_fst_6472_ = lean_ctor_get(v_a_6468_, 0);
lean_inc(v_fst_6472_);
v_snd_6473_ = lean_ctor_get(v_a_6468_, 1);
lean_inc(v_snd_6473_);
lean_dec(v_a_6468_);
v___x_6474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6474_, 0, v_snd_6473_);
v___x_6475_ = lean_st_ref_swap(v_ref_6454_, v___x_6474_);
lean_dec(v___x_6475_);
if (v_isShared_6471_ == 0)
{
lean_ctor_set(v___x_6470_, 0, v_fst_6472_);
v___x_6477_ = v___x_6470_;
goto v_reusejp_6476_;
}
else
{
lean_object* v_reuseFailAlloc_6478_; 
v_reuseFailAlloc_6478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6478_, 0, v_fst_6472_);
v___x_6477_ = v_reuseFailAlloc_6478_;
goto v_reusejp_6476_;
}
v_reusejp_6476_:
{
return v___x_6477_;
}
}
}
else
{
lean_object* v_a_6480_; lean_object* v___x_6482_; uint8_t v_isShared_6483_; uint8_t v_isSharedCheck_6487_; 
v_a_6480_ = lean_ctor_get(v___x_6467_, 0);
v_isSharedCheck_6487_ = !lean_is_exclusive(v___x_6467_);
if (v_isSharedCheck_6487_ == 0)
{
v___x_6482_ = v___x_6467_;
v_isShared_6483_ = v_isSharedCheck_6487_;
goto v_resetjp_6481_;
}
else
{
lean_inc(v_a_6480_);
lean_dec(v___x_6467_);
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
v_resetjp_6492_:
{
lean_object* v___x_6495_; lean_object* v_env_6496_; lean_object* v_nextMacroScope_6497_; lean_object* v_auxDeclNGen_6498_; lean_object* v_traceState_6499_; lean_object* v_cache_6500_; lean_object* v_messages_6501_; lean_object* v_infoState_6502_; lean_object* v_snapshotTasks_6503_; lean_object* v___x_6505_; uint8_t v_isShared_6506_; uint8_t v_isSharedCheck_6534_; 
v___x_6495_ = lean_st_ref_take(v_a_6463_);
v_env_6496_ = lean_ctor_get(v___x_6495_, 0);
v_nextMacroScope_6497_ = lean_ctor_get(v___x_6495_, 1);
v_auxDeclNGen_6498_ = lean_ctor_get(v___x_6495_, 3);
v_traceState_6499_ = lean_ctor_get(v___x_6495_, 4);
v_cache_6500_ = lean_ctor_get(v___x_6495_, 5);
v_messages_6501_ = lean_ctor_get(v___x_6495_, 6);
v_infoState_6502_ = lean_ctor_get(v___x_6495_, 7);
v_snapshotTasks_6503_ = lean_ctor_get(v___x_6495_, 8);
v_isSharedCheck_6534_ = !lean_is_exclusive(v___x_6495_);
if (v_isSharedCheck_6534_ == 0)
{
lean_object* v_unused_6535_; 
v_unused_6535_ = lean_ctor_get(v___x_6495_, 2);
lean_dec(v_unused_6535_);
v___x_6505_ = v___x_6495_;
v_isShared_6506_ = v_isSharedCheck_6534_;
goto v_resetjp_6504_;
}
else
{
lean_inc(v_snapshotTasks_6503_);
lean_inc(v_infoState_6502_);
lean_inc(v_messages_6501_);
lean_inc(v_cache_6500_);
lean_inc(v_traceState_6499_);
lean_inc(v_auxDeclNGen_6498_);
lean_inc(v_nextMacroScope_6497_);
lean_inc(v_env_6496_);
lean_dec(v___x_6495_);
v___x_6505_ = lean_box(0);
v_isShared_6506_ = v_isSharedCheck_6534_;
goto v_resetjp_6504_;
}
v_resetjp_6504_:
{
lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6511_; 
lean_inc(v_idx_6491_);
lean_inc(v_namePrefix_6490_);
v___x_6507_ = l_Lean_Name_num___override(v_namePrefix_6490_, v_idx_6491_);
v___x_6508_ = lean_unsigned_to_nat(1u);
v___x_6509_ = lean_nat_add(v_idx_6491_, v___x_6508_);
lean_dec(v_idx_6491_);
if (v_isShared_6494_ == 0)
{
lean_ctor_set(v___x_6493_, 1, v___x_6509_);
v___x_6511_ = v___x_6493_;
goto v_reusejp_6510_;
}
else
{
lean_object* v_reuseFailAlloc_6533_; 
v_reuseFailAlloc_6533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6533_, 0, v_namePrefix_6490_);
lean_ctor_set(v_reuseFailAlloc_6533_, 1, v___x_6509_);
v___x_6511_ = v_reuseFailAlloc_6533_;
goto v_reusejp_6510_;
}
v_reusejp_6510_:
{
lean_object* v___x_6513_; 
if (v_isShared_6506_ == 0)
{
lean_ctor_set(v___x_6505_, 2, v___x_6511_);
v___x_6513_ = v___x_6505_;
goto v_reusejp_6512_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_env_6496_);
lean_ctor_set(v_reuseFailAlloc_6532_, 1, v_nextMacroScope_6497_);
lean_ctor_set(v_reuseFailAlloc_6532_, 2, v___x_6511_);
lean_ctor_set(v_reuseFailAlloc_6532_, 3, v_auxDeclNGen_6498_);
lean_ctor_set(v_reuseFailAlloc_6532_, 4, v_traceState_6499_);
lean_ctor_set(v_reuseFailAlloc_6532_, 5, v_cache_6500_);
lean_ctor_set(v_reuseFailAlloc_6532_, 6, v_messages_6501_);
lean_ctor_set(v_reuseFailAlloc_6532_, 7, v_infoState_6502_);
lean_ctor_set(v_reuseFailAlloc_6532_, 8, v_snapshotTasks_6503_);
v___x_6513_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6512_;
}
v_reusejp_6512_:
{
lean_object* v___x_6514_; lean_object* v___x_6515_; 
v___x_6514_ = lean_st_ref_put(v_a_6463_, v___x_6513_);
v___x_6515_ = lean_st_ref_get(v_ref_6454_);
if (lean_obj_tag(v___x_6515_) == 0)
{
lean_object* v_options_6516_; lean_object* v___x_6517_; lean_object* v___f_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; 
v_options_6516_ = lean_ctor_get(v_a_6462_, 2);
v___x_6517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6517_, 0, v___x_6507_);
lean_ctor_set(v___x_6517_, 1, v___x_6508_);
lean_inc_ref(v_a_6462_);
v___f_6518_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6518_, 0, v_a_6462_);
lean_closure_set(v___f_6518_, 1, v___x_6517_);
lean_closure_set(v___f_6518_, 2, v_addEntry_6455_);
lean_closure_set(v___f_6518_, 3, v_constantsPerTask_6457_);
lean_closure_set(v___f_6518_, 4, v_droppedEntriesRef_6458_);
lean_closure_set(v___f_6518_, 5, v_droppedKeys_6456_);
v___x_6519_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6520_ = lean_box(0);
v___x_6521_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6519_, v_options_6516_, v___f_6518_, v___x_6520_, v_a_6460_, v_a_6461_, v_a_6462_, v_a_6463_);
if (lean_obj_tag(v___x_6521_) == 0)
{
lean_object* v_a_6522_; 
v_a_6522_ = lean_ctor_get(v___x_6521_, 0);
lean_inc(v_a_6522_);
lean_dec_ref_known(v___x_6521_, 1);
v_a_6466_ = v_a_6522_;
goto v___jp_6465_;
}
else
{
lean_object* v_a_6523_; lean_object* v___x_6525_; uint8_t v_isShared_6526_; uint8_t v_isSharedCheck_6530_; 
lean_dec_ref(v_ty_6459_);
v_a_6523_ = lean_ctor_get(v___x_6521_, 0);
v_isSharedCheck_6530_ = !lean_is_exclusive(v___x_6521_);
if (v_isSharedCheck_6530_ == 0)
{
v___x_6525_ = v___x_6521_;
v_isShared_6526_ = v_isSharedCheck_6530_;
goto v_resetjp_6524_;
}
else
{
lean_inc(v_a_6523_);
lean_dec(v___x_6521_);
v___x_6525_ = lean_box(0);
v_isShared_6526_ = v_isSharedCheck_6530_;
goto v_resetjp_6524_;
}
v_resetjp_6524_:
{
lean_object* v___x_6528_; 
if (v_isShared_6526_ == 0)
{
v___x_6528_ = v___x_6525_;
goto v_reusejp_6527_;
}
else
{
lean_object* v_reuseFailAlloc_6529_; 
v_reuseFailAlloc_6529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6529_, 0, v_a_6523_);
v___x_6528_ = v_reuseFailAlloc_6529_;
goto v_reusejp_6527_;
}
v_reusejp_6527_:
{
return v___x_6528_;
}
}
}
}
else
{
lean_object* v_val_6531_; 
lean_dec(v___x_6507_);
lean_dec(v_droppedEntriesRef_6458_);
lean_dec(v_constantsPerTask_6457_);
lean_dec(v_droppedKeys_6456_);
lean_dec_ref(v_addEntry_6455_);
v_val_6531_ = lean_ctor_get(v___x_6515_, 0);
lean_inc(v_val_6531_);
lean_dec_ref_known(v___x_6515_, 1);
v_a_6466_ = v_val_6531_;
goto v___jp_6465_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6537_, lean_object* v_addEntry_6538_, lean_object* v_droppedKeys_6539_, lean_object* v_constantsPerTask_6540_, lean_object* v_droppedEntriesRef_6541_, lean_object* v_ty_6542_, lean_object* v_a_6543_, lean_object* v_a_6544_, lean_object* v_a_6545_, lean_object* v_a_6546_, lean_object* v_a_6547_){
_start:
{
lean_object* v_res_6548_; 
v_res_6548_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6537_, v_addEntry_6538_, v_droppedKeys_6539_, v_constantsPerTask_6540_, v_droppedEntriesRef_6541_, v_ty_6542_, v_a_6543_, v_a_6544_, v_a_6545_, v_a_6546_);
lean_dec(v_a_6546_);
lean_dec_ref(v_a_6545_);
lean_dec(v_a_6544_);
lean_dec_ref(v_a_6543_);
lean_dec(v_ref_6537_);
return v_res_6548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6549_, lean_object* v_ref_6550_, lean_object* v_addEntry_6551_, lean_object* v_droppedKeys_6552_, lean_object* v_constantsPerTask_6553_, lean_object* v_droppedEntriesRef_6554_, lean_object* v_ty_6555_, lean_object* v_a_6556_, lean_object* v_a_6557_, lean_object* v_a_6558_, lean_object* v_a_6559_){
_start:
{
lean_object* v___x_6561_; 
v___x_6561_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6550_, v_addEntry_6551_, v_droppedKeys_6552_, v_constantsPerTask_6553_, v_droppedEntriesRef_6554_, v_ty_6555_, v_a_6556_, v_a_6557_, v_a_6558_, v_a_6559_);
return v___x_6561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6562_, lean_object* v_ref_6563_, lean_object* v_addEntry_6564_, lean_object* v_droppedKeys_6565_, lean_object* v_constantsPerTask_6566_, lean_object* v_droppedEntriesRef_6567_, lean_object* v_ty_6568_, lean_object* v_a_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_){
_start:
{
lean_object* v_res_6574_; 
v_res_6574_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6562_, v_ref_6563_, v_addEntry_6564_, v_droppedKeys_6565_, v_constantsPerTask_6566_, v_droppedEntriesRef_6567_, v_ty_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_);
lean_dec(v_a_6572_);
lean_dec_ref(v_a_6571_);
lean_dec(v_a_6570_);
lean_dec_ref(v_a_6569_);
lean_dec(v_ref_6563_);
return v_res_6574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6575_, lean_object* v_cctx_6576_, lean_object* v_ngen_6577_, lean_object* v_env_6578_, lean_object* v_act_6579_, lean_object* v_constantsPerTask_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_, lean_object* v___y_6583_, lean_object* v___y_6584_){
_start:
{
lean_object* v___x_6586_; 
v___x_6586_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6576_, v_ngen_6577_, v_env_6578_, v_act_6579_, v_constantsPerTask_6580_, v___y_6581_, v___y_6582_, v___y_6583_, v___y_6584_);
return v___x_6586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6587_, lean_object* v_cctx_6588_, lean_object* v_ngen_6589_, lean_object* v_env_6590_, lean_object* v_act_6591_, lean_object* v_constantsPerTask_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_){
_start:
{
lean_object* v_res_6598_; 
v_res_6598_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6587_, v_cctx_6588_, v_ngen_6589_, v_env_6590_, v_act_6591_, v_constantsPerTask_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_);
lean_dec(v___y_6596_);
lean_dec_ref(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec_ref(v___y_6593_);
lean_dec(v_constantsPerTask_6592_);
return v_res_6598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6599_, lean_object* v_cctx_6600_, lean_object* v_env_6601_, lean_object* v_act_6602_, lean_object* v_constantsPerTask_6603_, lean_object* v_n_6604_, lean_object* v_ngen_6605_, lean_object* v_tasks_6606_, lean_object* v_start_6607_, lean_object* v_cnt_6608_, lean_object* v_idx_6609_, lean_object* v___y_6610_, lean_object* v___y_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_){
_start:
{
lean_object* v___x_6615_; 
v___x_6615_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6600_, v_env_6601_, v_act_6602_, v_constantsPerTask_6603_, v_n_6604_, v_ngen_6605_, v_tasks_6606_, v_start_6607_, v_cnt_6608_, v_idx_6609_);
return v___x_6615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6616_, lean_object* v_cctx_6617_, lean_object* v_env_6618_, lean_object* v_act_6619_, lean_object* v_constantsPerTask_6620_, lean_object* v_n_6621_, lean_object* v_ngen_6622_, lean_object* v_tasks_6623_, lean_object* v_start_6624_, lean_object* v_cnt_6625_, lean_object* v_idx_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_){
_start:
{
lean_object* v_res_6632_; 
v_res_6632_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6616_, v_cctx_6617_, v_env_6618_, v_act_6619_, v_constantsPerTask_6620_, v_n_6621_, v_ngen_6622_, v_tasks_6623_, v_start_6624_, v_cnt_6625_, v_idx_6626_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_);
lean_dec(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec(v___y_6628_);
lean_dec_ref(v___y_6627_);
lean_dec(v_constantsPerTask_6620_);
return v_res_6632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6633_, lean_object* v_z_6634_, lean_object* v_tasks_6635_){
_start:
{
lean_object* v___x_6636_; 
v___x_6636_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6634_, v_tasks_6635_);
return v___x_6636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6637_, lean_object* v_z_6638_, lean_object* v_tasks_6639_){
_start:
{
lean_object* v_res_6640_; 
v_res_6640_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6637_, v_z_6638_, v_tasks_6639_);
lean_dec_ref(v_tasks_6639_);
return v_res_6640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6641_, lean_object* v_as_6642_, size_t v_i_6643_, size_t v_stop_6644_, lean_object* v_b_6645_){
_start:
{
lean_object* v___x_6646_; 
v___x_6646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6642_, v_i_6643_, v_stop_6644_, v_b_6645_);
return v___x_6646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6647_, lean_object* v_as_6648_, lean_object* v_i_6649_, lean_object* v_stop_6650_, lean_object* v_b_6651_){
_start:
{
size_t v_i_boxed_6652_; size_t v_stop_boxed_6653_; lean_object* v_res_6654_; 
v_i_boxed_6652_ = lean_unbox_usize(v_i_6649_);
lean_dec(v_i_6649_);
v_stop_boxed_6653_ = lean_unbox_usize(v_stop_6650_);
lean_dec(v_stop_6650_);
v_res_6654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6647_, v_as_6648_, v_i_boxed_6652_, v_stop_boxed_6653_, v_b_6651_);
lean_dec_ref(v_as_6648_);
return v_res_6654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6655_){
_start:
{
lean_object* v___x_6657_; lean_object* v_ngen_6658_; lean_object* v_namePrefix_6659_; lean_object* v_idx_6660_; lean_object* v___x_6662_; uint8_t v_isShared_6663_; uint8_t v_isSharedCheck_6690_; 
v___x_6657_ = lean_st_ref_get(v___y_6655_);
v_ngen_6658_ = lean_ctor_get(v___x_6657_, 2);
lean_inc_ref(v_ngen_6658_);
lean_dec(v___x_6657_);
v_namePrefix_6659_ = lean_ctor_get(v_ngen_6658_, 0);
v_idx_6660_ = lean_ctor_get(v_ngen_6658_, 1);
v_isSharedCheck_6690_ = !lean_is_exclusive(v_ngen_6658_);
if (v_isSharedCheck_6690_ == 0)
{
v___x_6662_ = v_ngen_6658_;
v_isShared_6663_ = v_isSharedCheck_6690_;
goto v_resetjp_6661_;
}
else
{
lean_inc(v_idx_6660_);
lean_inc(v_namePrefix_6659_);
lean_dec(v_ngen_6658_);
v___x_6662_ = lean_box(0);
v_isShared_6663_ = v_isSharedCheck_6690_;
goto v_resetjp_6661_;
}
v_resetjp_6661_:
{
lean_object* v___x_6664_; lean_object* v_env_6665_; lean_object* v_nextMacroScope_6666_; lean_object* v_auxDeclNGen_6667_; lean_object* v_traceState_6668_; lean_object* v_cache_6669_; lean_object* v_messages_6670_; lean_object* v_infoState_6671_; lean_object* v_snapshotTasks_6672_; lean_object* v___x_6674_; uint8_t v_isShared_6675_; uint8_t v_isSharedCheck_6688_; 
v___x_6664_ = lean_st_ref_take(v___y_6655_);
v_env_6665_ = lean_ctor_get(v___x_6664_, 0);
v_nextMacroScope_6666_ = lean_ctor_get(v___x_6664_, 1);
v_auxDeclNGen_6667_ = lean_ctor_get(v___x_6664_, 3);
v_traceState_6668_ = lean_ctor_get(v___x_6664_, 4);
v_cache_6669_ = lean_ctor_get(v___x_6664_, 5);
v_messages_6670_ = lean_ctor_get(v___x_6664_, 6);
v_infoState_6671_ = lean_ctor_get(v___x_6664_, 7);
v_snapshotTasks_6672_ = lean_ctor_get(v___x_6664_, 8);
v_isSharedCheck_6688_ = !lean_is_exclusive(v___x_6664_);
if (v_isSharedCheck_6688_ == 0)
{
lean_object* v_unused_6689_; 
v_unused_6689_ = lean_ctor_get(v___x_6664_, 2);
lean_dec(v_unused_6689_);
v___x_6674_ = v___x_6664_;
v_isShared_6675_ = v_isSharedCheck_6688_;
goto v_resetjp_6673_;
}
else
{
lean_inc(v_snapshotTasks_6672_);
lean_inc(v_infoState_6671_);
lean_inc(v_messages_6670_);
lean_inc(v_cache_6669_);
lean_inc(v_traceState_6668_);
lean_inc(v_auxDeclNGen_6667_);
lean_inc(v_nextMacroScope_6666_);
lean_inc(v_env_6665_);
lean_dec(v___x_6664_);
v___x_6674_ = lean_box(0);
v_isShared_6675_ = v_isSharedCheck_6688_;
goto v_resetjp_6673_;
}
v_resetjp_6673_:
{
lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6680_; 
lean_inc(v_idx_6660_);
lean_inc(v_namePrefix_6659_);
v___x_6676_ = l_Lean_Name_num___override(v_namePrefix_6659_, v_idx_6660_);
v___x_6677_ = lean_unsigned_to_nat(1u);
v___x_6678_ = lean_nat_add(v_idx_6660_, v___x_6677_);
lean_dec(v_idx_6660_);
if (v_isShared_6663_ == 0)
{
lean_ctor_set(v___x_6662_, 1, v___x_6678_);
v___x_6680_ = v___x_6662_;
goto v_reusejp_6679_;
}
else
{
lean_object* v_reuseFailAlloc_6687_; 
v_reuseFailAlloc_6687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6687_, 0, v_namePrefix_6659_);
lean_ctor_set(v_reuseFailAlloc_6687_, 1, v___x_6678_);
v___x_6680_ = v_reuseFailAlloc_6687_;
goto v_reusejp_6679_;
}
v_reusejp_6679_:
{
lean_object* v___x_6682_; 
if (v_isShared_6675_ == 0)
{
lean_ctor_set(v___x_6674_, 2, v___x_6680_);
v___x_6682_ = v___x_6674_;
goto v_reusejp_6681_;
}
else
{
lean_object* v_reuseFailAlloc_6686_; 
v_reuseFailAlloc_6686_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_env_6665_);
lean_ctor_set(v_reuseFailAlloc_6686_, 1, v_nextMacroScope_6666_);
lean_ctor_set(v_reuseFailAlloc_6686_, 2, v___x_6680_);
lean_ctor_set(v_reuseFailAlloc_6686_, 3, v_auxDeclNGen_6667_);
lean_ctor_set(v_reuseFailAlloc_6686_, 4, v_traceState_6668_);
lean_ctor_set(v_reuseFailAlloc_6686_, 5, v_cache_6669_);
lean_ctor_set(v_reuseFailAlloc_6686_, 6, v_messages_6670_);
lean_ctor_set(v_reuseFailAlloc_6686_, 7, v_infoState_6671_);
lean_ctor_set(v_reuseFailAlloc_6686_, 8, v_snapshotTasks_6672_);
v___x_6682_ = v_reuseFailAlloc_6686_;
goto v_reusejp_6681_;
}
v_reusejp_6681_:
{
lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; 
v___x_6683_ = lean_st_ref_put(v___y_6655_, v___x_6682_);
v___x_6684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6684_, 0, v___x_6676_);
lean_ctor_set(v___x_6684_, 1, v___x_6677_);
v___x_6685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6685_, 0, v___x_6684_);
return v___x_6685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6691_, lean_object* v___y_6692_){
_start:
{
lean_object* v_res_6693_; 
v_res_6693_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6691_);
lean_dec(v___y_6691_);
return v_res_6693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6694_, lean_object* v___y_6695_){
_start:
{
lean_object* v___x_6697_; 
v___x_6697_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6695_);
return v___x_6697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6698_, lean_object* v___y_6699_, lean_object* v___y_6700_){
_start:
{
lean_object* v_res_6701_; 
v_res_6701_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6698_, v___y_6699_);
lean_dec(v___y_6699_);
lean_dec_ref(v___y_6698_);
return v_res_6701_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6702_; lean_object* v___x_6703_; lean_object* v___x_6704_; 
v___x_6702_ = lean_unsigned_to_nat(32u);
v___x_6703_ = lean_mk_empty_array_with_capacity(v___x_6702_);
v___x_6704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6704_, 0, v___x_6703_);
return v___x_6704_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; 
v___x_6705_ = ((size_t)5ULL);
v___x_6706_ = lean_unsigned_to_nat(0u);
v___x_6707_ = lean_unsigned_to_nat(32u);
v___x_6708_ = lean_mk_empty_array_with_capacity(v___x_6707_);
v___x_6709_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6710_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6710_, 0, v___x_6709_);
lean_ctor_set(v___x_6710_, 1, v___x_6708_);
lean_ctor_set(v___x_6710_, 2, v___x_6706_);
lean_ctor_set(v___x_6710_, 3, v___x_6706_);
lean_ctor_set_usize(v___x_6710_, 4, v___x_6705_);
return v___x_6710_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; lean_object* v___x_6714_; 
v___x_6711_ = lean_box(1);
v___x_6712_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6713_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6714_, 0, v___x_6713_);
lean_ctor_set(v___x_6714_, 1, v___x_6712_);
lean_ctor_set(v___x_6714_, 2, v___x_6711_);
return v___x_6714_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_){
_start:
{
lean_object* v___x_6719_; lean_object* v_env_6720_; lean_object* v_options_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; 
v___x_6719_ = lean_st_ref_get(v___y_6717_);
v_env_6720_ = lean_ctor_get(v___x_6719_, 0);
lean_inc_ref(v_env_6720_);
lean_dec(v___x_6719_);
v_options_6721_ = lean_ctor_get(v___y_6716_, 2);
v___x_6722_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6723_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6721_);
v___x_6724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6724_, 0, v_env_6720_);
lean_ctor_set(v___x_6724_, 1, v___x_6722_);
lean_ctor_set(v___x_6724_, 2, v___x_6723_);
lean_ctor_set(v___x_6724_, 3, v_options_6721_);
v___x_6725_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6725_, 0, v___x_6724_);
lean_ctor_set(v___x_6725_, 1, v_msgData_6715_);
v___x_6726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6726_, 0, v___x_6725_);
return v___x_6726_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6727_, lean_object* v___y_6728_, lean_object* v___y_6729_, lean_object* v___y_6730_){
_start:
{
lean_object* v_res_6731_; 
v_res_6731_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6727_, v___y_6728_, v___y_6729_);
lean_dec(v___y_6729_);
lean_dec_ref(v___y_6728_);
return v_res_6731_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6732_, lean_object* v_msgData_6733_, uint8_t v_severity_6734_, uint8_t v_isSilent_6735_, lean_object* v___y_6736_, lean_object* v___y_6737_){
_start:
{
lean_object* v___y_6740_; lean_object* v___y_6741_; uint8_t v___y_6742_; lean_object* v___y_6743_; uint8_t v___y_6744_; lean_object* v___y_6745_; lean_object* v___y_6746_; lean_object* v___y_6747_; lean_object* v___y_6748_; lean_object* v___y_6776_; uint8_t v___y_6777_; lean_object* v___y_6778_; lean_object* v___y_6779_; uint8_t v___y_6780_; lean_object* v___y_6781_; uint8_t v___y_6782_; lean_object* v___y_6783_; lean_object* v___y_6801_; lean_object* v___y_6802_; uint8_t v___y_6803_; lean_object* v___y_6804_; lean_object* v___y_6805_; uint8_t v___y_6806_; uint8_t v___y_6807_; lean_object* v___y_6808_; lean_object* v___y_6812_; uint8_t v___y_6813_; lean_object* v___y_6814_; lean_object* v___y_6815_; lean_object* v___y_6816_; uint8_t v___y_6817_; uint8_t v___y_6818_; uint8_t v___x_6823_; lean_object* v___y_6825_; uint8_t v___y_6826_; lean_object* v___y_6827_; lean_object* v___y_6828_; lean_object* v___y_6829_; uint8_t v___y_6830_; uint8_t v___y_6831_; uint8_t v___y_6833_; uint8_t v___x_6848_; 
v___x_6823_ = 2;
v___x_6848_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6734_, v___x_6823_);
if (v___x_6848_ == 0)
{
v___y_6833_ = v___x_6848_;
goto v___jp_6832_;
}
else
{
uint8_t v___x_6849_; 
lean_inc_ref(v_msgData_6733_);
v___x_6849_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6733_);
v___y_6833_ = v___x_6849_;
goto v___jp_6832_;
}
v___jp_6739_:
{
lean_object* v___x_6749_; lean_object* v_currNamespace_6750_; lean_object* v_openDecls_6751_; lean_object* v_env_6752_; lean_object* v_nextMacroScope_6753_; lean_object* v_ngen_6754_; lean_object* v_auxDeclNGen_6755_; lean_object* v_traceState_6756_; lean_object* v_cache_6757_; lean_object* v_messages_6758_; lean_object* v_infoState_6759_; lean_object* v_snapshotTasks_6760_; lean_object* v___x_6762_; uint8_t v_isShared_6763_; uint8_t v_isSharedCheck_6774_; 
v___x_6749_ = lean_st_ref_take(v___y_6748_);
v_currNamespace_6750_ = lean_ctor_get(v___y_6747_, 6);
v_openDecls_6751_ = lean_ctor_get(v___y_6747_, 7);
v_env_6752_ = lean_ctor_get(v___x_6749_, 0);
v_nextMacroScope_6753_ = lean_ctor_get(v___x_6749_, 1);
v_ngen_6754_ = lean_ctor_get(v___x_6749_, 2);
v_auxDeclNGen_6755_ = lean_ctor_get(v___x_6749_, 3);
v_traceState_6756_ = lean_ctor_get(v___x_6749_, 4);
v_cache_6757_ = lean_ctor_get(v___x_6749_, 5);
v_messages_6758_ = lean_ctor_get(v___x_6749_, 6);
v_infoState_6759_ = lean_ctor_get(v___x_6749_, 7);
v_snapshotTasks_6760_ = lean_ctor_get(v___x_6749_, 8);
v_isSharedCheck_6774_ = !lean_is_exclusive(v___x_6749_);
if (v_isSharedCheck_6774_ == 0)
{
v___x_6762_ = v___x_6749_;
v_isShared_6763_ = v_isSharedCheck_6774_;
goto v_resetjp_6761_;
}
else
{
lean_inc(v_snapshotTasks_6760_);
lean_inc(v_infoState_6759_);
lean_inc(v_messages_6758_);
lean_inc(v_cache_6757_);
lean_inc(v_traceState_6756_);
lean_inc(v_auxDeclNGen_6755_);
lean_inc(v_ngen_6754_);
lean_inc(v_nextMacroScope_6753_);
lean_inc(v_env_6752_);
lean_dec(v___x_6749_);
v___x_6762_ = lean_box(0);
v_isShared_6763_ = v_isSharedCheck_6774_;
goto v_resetjp_6761_;
}
v_resetjp_6761_:
{
lean_object* v___x_6764_; lean_object* v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6769_; 
lean_inc(v_openDecls_6751_);
lean_inc(v_currNamespace_6750_);
v___x_6764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6764_, 0, v_currNamespace_6750_);
lean_ctor_set(v___x_6764_, 1, v_openDecls_6751_);
v___x_6765_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6765_, 0, v___x_6764_);
lean_ctor_set(v___x_6765_, 1, v___y_6746_);
lean_inc_ref(v___y_6743_);
lean_inc_ref(v___y_6741_);
v___x_6766_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6766_, 0, v___y_6741_);
lean_ctor_set(v___x_6766_, 1, v___y_6745_);
lean_ctor_set(v___x_6766_, 2, v___y_6740_);
lean_ctor_set(v___x_6766_, 3, v___y_6743_);
lean_ctor_set(v___x_6766_, 4, v___x_6765_);
lean_ctor_set_uint8(v___x_6766_, sizeof(void*)*5, v___y_6744_);
lean_ctor_set_uint8(v___x_6766_, sizeof(void*)*5 + 1, v___y_6742_);
lean_ctor_set_uint8(v___x_6766_, sizeof(void*)*5 + 2, v_isSilent_6735_);
v___x_6767_ = l_Lean_MessageLog_add(v___x_6766_, v_messages_6758_);
if (v_isShared_6763_ == 0)
{
lean_ctor_set(v___x_6762_, 6, v___x_6767_);
v___x_6769_ = v___x_6762_;
goto v_reusejp_6768_;
}
else
{
lean_object* v_reuseFailAlloc_6773_; 
v_reuseFailAlloc_6773_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6773_, 0, v_env_6752_);
lean_ctor_set(v_reuseFailAlloc_6773_, 1, v_nextMacroScope_6753_);
lean_ctor_set(v_reuseFailAlloc_6773_, 2, v_ngen_6754_);
lean_ctor_set(v_reuseFailAlloc_6773_, 3, v_auxDeclNGen_6755_);
lean_ctor_set(v_reuseFailAlloc_6773_, 4, v_traceState_6756_);
lean_ctor_set(v_reuseFailAlloc_6773_, 5, v_cache_6757_);
lean_ctor_set(v_reuseFailAlloc_6773_, 6, v___x_6767_);
lean_ctor_set(v_reuseFailAlloc_6773_, 7, v_infoState_6759_);
lean_ctor_set(v_reuseFailAlloc_6773_, 8, v_snapshotTasks_6760_);
v___x_6769_ = v_reuseFailAlloc_6773_;
goto v_reusejp_6768_;
}
v_reusejp_6768_:
{
lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; 
v___x_6770_ = lean_st_ref_put(v___y_6748_, v___x_6769_);
v___x_6771_ = lean_box(0);
v___x_6772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6772_, 0, v___x_6771_);
return v___x_6772_;
}
}
}
v___jp_6775_:
{
lean_object* v___x_6784_; lean_object* v___x_6785_; lean_object* v_a_6786_; lean_object* v___x_6788_; uint8_t v_isShared_6789_; uint8_t v_isSharedCheck_6799_; 
v___x_6784_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6733_);
v___x_6785_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6784_, v___y_6736_, v___y_6737_);
v_a_6786_ = lean_ctor_get(v___x_6785_, 0);
v_isSharedCheck_6799_ = !lean_is_exclusive(v___x_6785_);
if (v_isSharedCheck_6799_ == 0)
{
v___x_6788_ = v___x_6785_;
v_isShared_6789_ = v_isSharedCheck_6799_;
goto v_resetjp_6787_;
}
else
{
lean_inc(v_a_6786_);
lean_dec(v___x_6785_);
v___x_6788_ = lean_box(0);
v_isShared_6789_ = v_isSharedCheck_6799_;
goto v_resetjp_6787_;
}
v_resetjp_6787_:
{
lean_object* v___x_6790_; lean_object* v___x_6791_; lean_object* v___x_6792_; lean_object* v___x_6793_; 
lean_inc_ref_n(v___y_6778_, 2);
v___x_6790_ = l_Lean_FileMap_toPosition(v___y_6778_, v___y_6781_);
lean_dec(v___y_6781_);
v___x_6791_ = l_Lean_FileMap_toPosition(v___y_6778_, v___y_6783_);
lean_dec(v___y_6783_);
v___x_6792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6792_, 0, v___x_6791_);
v___x_6793_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6777_ == 0)
{
lean_del_object(v___x_6788_);
lean_dec_ref(v___y_6776_);
v___y_6740_ = v___x_6792_;
v___y_6741_ = v___y_6779_;
v___y_6742_ = v___y_6780_;
v___y_6743_ = v___x_6793_;
v___y_6744_ = v___y_6782_;
v___y_6745_ = v___x_6790_;
v___y_6746_ = v_a_6786_;
v___y_6747_ = v___y_6736_;
v___y_6748_ = v___y_6737_;
goto v___jp_6739_;
}
else
{
uint8_t v___x_6794_; 
lean_inc(v_a_6786_);
v___x_6794_ = l_Lean_MessageData_hasTag(v___y_6776_, v_a_6786_);
if (v___x_6794_ == 0)
{
lean_object* v___x_6795_; lean_object* v___x_6797_; 
lean_dec_ref_known(v___x_6792_, 1);
lean_dec_ref(v___x_6790_);
lean_dec(v_a_6786_);
v___x_6795_ = lean_box(0);
if (v_isShared_6789_ == 0)
{
lean_ctor_set(v___x_6788_, 0, v___x_6795_);
v___x_6797_ = v___x_6788_;
goto v_reusejp_6796_;
}
else
{
lean_object* v_reuseFailAlloc_6798_; 
v_reuseFailAlloc_6798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6798_, 0, v___x_6795_);
v___x_6797_ = v_reuseFailAlloc_6798_;
goto v_reusejp_6796_;
}
v_reusejp_6796_:
{
return v___x_6797_;
}
}
else
{
lean_del_object(v___x_6788_);
v___y_6740_ = v___x_6792_;
v___y_6741_ = v___y_6779_;
v___y_6742_ = v___y_6780_;
v___y_6743_ = v___x_6793_;
v___y_6744_ = v___y_6782_;
v___y_6745_ = v___x_6790_;
v___y_6746_ = v_a_6786_;
v___y_6747_ = v___y_6736_;
v___y_6748_ = v___y_6737_;
goto v___jp_6739_;
}
}
}
}
v___jp_6800_:
{
lean_object* v___x_6809_; 
v___x_6809_ = l_Lean_Syntax_getTailPos_x3f(v___y_6804_, v___y_6807_);
lean_dec(v___y_6804_);
if (lean_obj_tag(v___x_6809_) == 0)
{
lean_inc(v___y_6808_);
v___y_6776_ = v___y_6801_;
v___y_6777_ = v___y_6803_;
v___y_6778_ = v___y_6802_;
v___y_6779_ = v___y_6805_;
v___y_6780_ = v___y_6806_;
v___y_6781_ = v___y_6808_;
v___y_6782_ = v___y_6807_;
v___y_6783_ = v___y_6808_;
goto v___jp_6775_;
}
else
{
lean_object* v_val_6810_; 
v_val_6810_ = lean_ctor_get(v___x_6809_, 0);
lean_inc(v_val_6810_);
lean_dec_ref_known(v___x_6809_, 1);
v___y_6776_ = v___y_6801_;
v___y_6777_ = v___y_6803_;
v___y_6778_ = v___y_6802_;
v___y_6779_ = v___y_6805_;
v___y_6780_ = v___y_6806_;
v___y_6781_ = v___y_6808_;
v___y_6782_ = v___y_6807_;
v___y_6783_ = v_val_6810_;
goto v___jp_6775_;
}
}
v___jp_6811_:
{
lean_object* v_ref_6819_; lean_object* v___x_6820_; 
v_ref_6819_ = l_Lean_replaceRef(v_ref_6732_, v___y_6816_);
v___x_6820_ = l_Lean_Syntax_getPos_x3f(v_ref_6819_, v___y_6817_);
if (lean_obj_tag(v___x_6820_) == 0)
{
lean_object* v___x_6821_; 
v___x_6821_ = lean_unsigned_to_nat(0u);
v___y_6801_ = v___y_6812_;
v___y_6802_ = v___y_6814_;
v___y_6803_ = v___y_6813_;
v___y_6804_ = v_ref_6819_;
v___y_6805_ = v___y_6815_;
v___y_6806_ = v___y_6818_;
v___y_6807_ = v___y_6817_;
v___y_6808_ = v___x_6821_;
goto v___jp_6800_;
}
else
{
lean_object* v_val_6822_; 
v_val_6822_ = lean_ctor_get(v___x_6820_, 0);
lean_inc(v_val_6822_);
lean_dec_ref_known(v___x_6820_, 1);
v___y_6801_ = v___y_6812_;
v___y_6802_ = v___y_6814_;
v___y_6803_ = v___y_6813_;
v___y_6804_ = v_ref_6819_;
v___y_6805_ = v___y_6815_;
v___y_6806_ = v___y_6818_;
v___y_6807_ = v___y_6817_;
v___y_6808_ = v_val_6822_;
goto v___jp_6800_;
}
}
v___jp_6824_:
{
if (v___y_6831_ == 0)
{
v___y_6812_ = v___y_6829_;
v___y_6813_ = v___y_6826_;
v___y_6814_ = v___y_6825_;
v___y_6815_ = v___y_6827_;
v___y_6816_ = v___y_6828_;
v___y_6817_ = v___y_6830_;
v___y_6818_ = v_severity_6734_;
goto v___jp_6811_;
}
else
{
v___y_6812_ = v___y_6829_;
v___y_6813_ = v___y_6826_;
v___y_6814_ = v___y_6825_;
v___y_6815_ = v___y_6827_;
v___y_6816_ = v___y_6828_;
v___y_6817_ = v___y_6830_;
v___y_6818_ = v___x_6823_;
goto v___jp_6811_;
}
}
v___jp_6832_:
{
if (v___y_6833_ == 0)
{
lean_object* v_fileName_6834_; lean_object* v_fileMap_6835_; lean_object* v_options_6836_; lean_object* v_ref_6837_; uint8_t v_suppressElabErrors_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; lean_object* v___f_6841_; uint8_t v___x_6842_; uint8_t v___x_6843_; 
v_fileName_6834_ = lean_ctor_get(v___y_6736_, 0);
v_fileMap_6835_ = lean_ctor_get(v___y_6736_, 1);
v_options_6836_ = lean_ctor_get(v___y_6736_, 2);
v_ref_6837_ = lean_ctor_get(v___y_6736_, 5);
v_suppressElabErrors_6838_ = lean_ctor_get_uint8(v___y_6736_, sizeof(void*)*14 + 1);
v___x_6839_ = lean_box(v_suppressElabErrors_6838_);
v___x_6840_ = lean_box(v___y_6833_);
v___f_6841_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6841_, 0, v___x_6839_);
lean_closure_set(v___f_6841_, 1, v___x_6840_);
v___x_6842_ = 1;
v___x_6843_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6734_, v___x_6842_);
if (v___x_6843_ == 0)
{
v___y_6825_ = v_fileMap_6835_;
v___y_6826_ = v_suppressElabErrors_6838_;
v___y_6827_ = v_fileName_6834_;
v___y_6828_ = v_ref_6837_;
v___y_6829_ = v___f_6841_;
v___y_6830_ = v___y_6833_;
v___y_6831_ = v___x_6843_;
goto v___jp_6824_;
}
else
{
lean_object* v___x_6844_; uint8_t v___x_6845_; 
v___x_6844_ = l_Lean_warningAsError;
v___x_6845_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6836_, v___x_6844_);
v___y_6825_ = v_fileMap_6835_;
v___y_6826_ = v_suppressElabErrors_6838_;
v___y_6827_ = v_fileName_6834_;
v___y_6828_ = v_ref_6837_;
v___y_6829_ = v___f_6841_;
v___y_6830_ = v___y_6833_;
v___y_6831_ = v___x_6845_;
goto v___jp_6824_;
}
}
else
{
lean_object* v___x_6846_; lean_object* v___x_6847_; 
lean_dec_ref(v_msgData_6733_);
v___x_6846_ = lean_box(0);
v___x_6847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6847_, 0, v___x_6846_);
return v___x_6847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6850_, lean_object* v_msgData_6851_, lean_object* v_severity_6852_, lean_object* v_isSilent_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_, lean_object* v___y_6856_){
_start:
{
uint8_t v_severity_boxed_6857_; uint8_t v_isSilent_boxed_6858_; lean_object* v_res_6859_; 
v_severity_boxed_6857_ = lean_unbox(v_severity_6852_);
v_isSilent_boxed_6858_ = lean_unbox(v_isSilent_6853_);
v_res_6859_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6850_, v_msgData_6851_, v_severity_boxed_6857_, v_isSilent_boxed_6858_, v___y_6854_, v___y_6855_);
lean_dec(v___y_6855_);
lean_dec_ref(v___y_6854_);
lean_dec(v_ref_6850_);
return v_res_6859_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6860_, uint8_t v_severity_6861_, uint8_t v_isSilent_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_){
_start:
{
lean_object* v_ref_6866_; lean_object* v___x_6867_; 
v_ref_6866_ = lean_ctor_get(v___y_6863_, 5);
v___x_6867_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6866_, v_msgData_6860_, v_severity_6861_, v_isSilent_6862_, v___y_6863_, v___y_6864_);
return v___x_6867_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6868_, lean_object* v_severity_6869_, lean_object* v_isSilent_6870_, lean_object* v___y_6871_, lean_object* v___y_6872_, lean_object* v___y_6873_){
_start:
{
uint8_t v_severity_boxed_6874_; uint8_t v_isSilent_boxed_6875_; lean_object* v_res_6876_; 
v_severity_boxed_6874_ = lean_unbox(v_severity_6869_);
v_isSilent_boxed_6875_ = lean_unbox(v_isSilent_6870_);
v_res_6876_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6868_, v_severity_boxed_6874_, v_isSilent_boxed_6875_, v___y_6871_, v___y_6872_);
lean_dec(v___y_6872_);
lean_dec_ref(v___y_6871_);
return v_res_6876_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_){
_start:
{
uint8_t v___x_6881_; uint8_t v___x_6882_; lean_object* v___x_6883_; 
v___x_6881_ = 2;
v___x_6882_ = 0;
v___x_6883_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6877_, v___x_6881_, v___x_6882_, v___y_6878_, v___y_6879_);
return v___x_6883_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6884_, lean_object* v___y_6885_, lean_object* v___y_6886_, lean_object* v___y_6887_){
_start:
{
lean_object* v_res_6888_; 
v_res_6888_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6884_, v___y_6885_, v___y_6886_);
lean_dec(v___y_6886_);
lean_dec_ref(v___y_6885_);
return v_res_6888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6889_, lean_object* v___y_6890_, lean_object* v___y_6891_){
_start:
{
lean_object* v_module_6893_; lean_object* v_const_6894_; lean_object* v_exception_6895_; lean_object* v___x_6896_; lean_object* v___x_6897_; lean_object* v___x_6898_; lean_object* v___x_6899_; lean_object* v___x_6900_; lean_object* v___x_6901_; lean_object* v___x_6902_; lean_object* v___x_6903_; lean_object* v___x_6904_; lean_object* v___x_6905_; lean_object* v___x_6906_; lean_object* v___x_6907_; 
v_module_6893_ = lean_ctor_get(v_f_6889_, 0);
lean_inc(v_module_6893_);
v_const_6894_ = lean_ctor_get(v_f_6889_, 1);
lean_inc(v_const_6894_);
v_exception_6895_ = lean_ctor_get(v_f_6889_, 2);
lean_inc_ref(v_exception_6895_);
lean_dec_ref(v_f_6889_);
v___x_6896_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6897_ = l_Lean_MessageData_ofName(v_const_6894_);
v___x_6898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6898_, 0, v___x_6896_);
lean_ctor_set(v___x_6898_, 1, v___x_6897_);
v___x_6899_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6900_, 0, v___x_6898_);
lean_ctor_set(v___x_6900_, 1, v___x_6899_);
v___x_6901_ = l_Lean_MessageData_ofName(v_module_6893_);
v___x_6902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6902_, 0, v___x_6900_);
lean_ctor_set(v___x_6902_, 1, v___x_6901_);
v___x_6903_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6904_, 0, v___x_6902_);
lean_ctor_set(v___x_6904_, 1, v___x_6903_);
v___x_6905_ = l_Lean_Exception_toMessageData(v_exception_6895_);
v___x_6906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6906_, 0, v___x_6904_);
lean_ctor_set(v___x_6906_, 1, v___x_6905_);
v___x_6907_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6906_, v___y_6890_, v___y_6891_);
return v___x_6907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6908_, lean_object* v___y_6909_, lean_object* v___y_6910_, lean_object* v___y_6911_){
_start:
{
lean_object* v_res_6912_; 
v_res_6912_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6908_, v___y_6909_, v___y_6910_);
lean_dec(v___y_6910_);
lean_dec_ref(v___y_6909_);
return v_res_6912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_6913_, size_t v_i_6914_, size_t v_stop_6915_, lean_object* v_b_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_){
_start:
{
uint8_t v___x_6920_; 
v___x_6920_ = lean_usize_dec_eq(v_i_6914_, v_stop_6915_);
if (v___x_6920_ == 0)
{
lean_object* v___x_6921_; lean_object* v___x_6922_; 
v___x_6921_ = lean_array_uget_borrowed(v_as_6913_, v_i_6914_);
lean_inc(v___x_6921_);
v___x_6922_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_6921_, v___y_6917_, v___y_6918_);
if (lean_obj_tag(v___x_6922_) == 0)
{
lean_object* v_a_6923_; size_t v___x_6924_; size_t v___x_6925_; 
v_a_6923_ = lean_ctor_get(v___x_6922_, 0);
lean_inc(v_a_6923_);
lean_dec_ref_known(v___x_6922_, 1);
v___x_6924_ = ((size_t)1ULL);
v___x_6925_ = lean_usize_add(v_i_6914_, v___x_6924_);
v_i_6914_ = v___x_6925_;
v_b_6916_ = v_a_6923_;
goto _start;
}
else
{
return v___x_6922_;
}
}
else
{
lean_object* v___x_6927_; 
v___x_6927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6927_, 0, v_b_6916_);
return v___x_6927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_6928_, lean_object* v_i_6929_, lean_object* v_stop_6930_, lean_object* v_b_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_){
_start:
{
size_t v_i_boxed_6935_; size_t v_stop_boxed_6936_; lean_object* v_res_6937_; 
v_i_boxed_6935_ = lean_unbox_usize(v_i_6929_);
lean_dec(v_i_6929_);
v_stop_boxed_6936_ = lean_unbox_usize(v_stop_6930_);
lean_dec(v_stop_6930_);
v_res_6937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_6928_, v_i_boxed_6935_, v_stop_boxed_6936_, v_b_6931_, v___y_6932_, v___y_6933_);
lean_dec(v___y_6933_);
lean_dec_ref(v___y_6932_);
lean_dec_ref(v_as_6928_);
return v_res_6937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_6938_, lean_object* v_a_6939_, lean_object* v_a_6940_){
_start:
{
lean_object* v___x_6942_; lean_object* v___x_6943_; lean_object* v_a_6944_; lean_object* v___x_6946_; uint8_t v_isShared_6947_; uint8_t v_isSharedCheck_6978_; 
v___x_6942_ = lean_st_ref_get(v_a_6940_);
v___x_6943_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_6940_);
v_a_6944_ = lean_ctor_get(v___x_6943_, 0);
v_isSharedCheck_6978_ = !lean_is_exclusive(v___x_6943_);
if (v_isSharedCheck_6978_ == 0)
{
v___x_6946_ = v___x_6943_;
v_isShared_6947_ = v_isSharedCheck_6978_;
goto v_resetjp_6945_;
}
else
{
lean_inc(v_a_6944_);
lean_dec(v___x_6943_);
v___x_6946_ = lean_box(0);
v_isShared_6947_ = v_isSharedCheck_6978_;
goto v_resetjp_6945_;
}
v_resetjp_6945_:
{
lean_object* v___x_6948_; lean_object* v_env_6949_; lean_object* v___x_6950_; lean_object* v___y_6957_; lean_object* v___x_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; uint8_t v___x_6969_; 
v___x_6948_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_6949_ = lean_ctor_get(v___x_6942_, 0);
lean_inc_ref(v_env_6949_);
lean_dec(v___x_6942_);
lean_inc_ref(v_a_6939_);
v___x_6950_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_6939_, v_a_6944_, v_env_6949_, v___x_6948_, v_entriesForConst_6938_);
v___x_6966_ = lean_st_ref_get(v___x_6948_);
lean_dec(v___x_6948_);
v___x_6967_ = lean_unsigned_to_nat(0u);
v___x_6968_ = lean_array_get_size(v___x_6966_);
v___x_6969_ = lean_nat_dec_lt(v___x_6967_, v___x_6968_);
if (v___x_6969_ == 0)
{
lean_dec(v___x_6966_);
goto v___jp_6951_;
}
else
{
lean_object* v___x_6970_; uint8_t v___x_6971_; 
v___x_6970_ = lean_box(0);
v___x_6971_ = lean_nat_dec_le(v___x_6968_, v___x_6968_);
if (v___x_6971_ == 0)
{
if (v___x_6969_ == 0)
{
lean_dec(v___x_6966_);
goto v___jp_6951_;
}
else
{
size_t v___x_6972_; size_t v___x_6973_; lean_object* v___x_6974_; 
v___x_6972_ = ((size_t)0ULL);
v___x_6973_ = lean_usize_of_nat(v___x_6968_);
v___x_6974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_6966_, v___x_6972_, v___x_6973_, v___x_6970_, v_a_6939_, v_a_6940_);
lean_dec(v___x_6966_);
v___y_6957_ = v___x_6974_;
goto v___jp_6956_;
}
}
else
{
size_t v___x_6975_; size_t v___x_6976_; lean_object* v___x_6977_; 
v___x_6975_ = ((size_t)0ULL);
v___x_6976_ = lean_usize_of_nat(v___x_6968_);
v___x_6977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_6966_, v___x_6975_, v___x_6976_, v___x_6970_, v_a_6939_, v_a_6940_);
lean_dec(v___x_6966_);
v___y_6957_ = v___x_6977_;
goto v___jp_6956_;
}
}
v___jp_6951_:
{
lean_object* v___x_6952_; lean_object* v___x_6954_; 
v___x_6952_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_6950_);
if (v_isShared_6947_ == 0)
{
lean_ctor_set(v___x_6946_, 0, v___x_6952_);
v___x_6954_ = v___x_6946_;
goto v_reusejp_6953_;
}
else
{
lean_object* v_reuseFailAlloc_6955_; 
v_reuseFailAlloc_6955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6955_, 0, v___x_6952_);
v___x_6954_ = v_reuseFailAlloc_6955_;
goto v_reusejp_6953_;
}
v_reusejp_6953_:
{
return v___x_6954_;
}
}
v___jp_6956_:
{
if (lean_obj_tag(v___y_6957_) == 0)
{
lean_dec_ref_known(v___y_6957_, 1);
goto v___jp_6951_;
}
else
{
lean_object* v_a_6958_; lean_object* v___x_6960_; uint8_t v_isShared_6961_; uint8_t v_isSharedCheck_6965_; 
lean_dec_ref(v___x_6950_);
lean_del_object(v___x_6946_);
v_a_6958_ = lean_ctor_get(v___y_6957_, 0);
v_isSharedCheck_6965_ = !lean_is_exclusive(v___y_6957_);
if (v_isSharedCheck_6965_ == 0)
{
v___x_6960_ = v___y_6957_;
v_isShared_6961_ = v_isSharedCheck_6965_;
goto v_resetjp_6959_;
}
else
{
lean_inc(v_a_6958_);
lean_dec(v___y_6957_);
v___x_6960_ = lean_box(0);
v_isShared_6961_ = v_isSharedCheck_6965_;
goto v_resetjp_6959_;
}
v_resetjp_6959_:
{
lean_object* v___x_6963_; 
if (v_isShared_6961_ == 0)
{
v___x_6963_ = v___x_6960_;
goto v_reusejp_6962_;
}
else
{
lean_object* v_reuseFailAlloc_6964_; 
v_reuseFailAlloc_6964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6964_, 0, v_a_6958_);
v___x_6963_ = v_reuseFailAlloc_6964_;
goto v_reusejp_6962_;
}
v_reusejp_6962_:
{
return v___x_6963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_6979_, lean_object* v_a_6980_, lean_object* v_a_6981_, lean_object* v_a_6982_){
_start:
{
lean_object* v_res_6983_; 
v_res_6983_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_6979_, v_a_6980_, v_a_6981_);
lean_dec(v_a_6981_);
lean_dec_ref(v_a_6980_);
return v_res_6983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_6984_, lean_object* v_entriesForConst_6985_, lean_object* v_a_6986_, lean_object* v_a_6987_){
_start:
{
lean_object* v___x_6989_; 
v___x_6989_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_6985_, v_a_6986_, v_a_6987_);
return v___x_6989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_6990_, lean_object* v_entriesForConst_6991_, lean_object* v_a_6992_, lean_object* v_a_6993_, lean_object* v_a_6994_){
_start:
{
lean_object* v_res_6995_; 
v_res_6995_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_6990_, v_entriesForConst_6991_, v_a_6992_, v_a_6993_);
lean_dec(v_a_6993_);
lean_dec_ref(v_a_6992_);
return v_res_6995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_6996_, lean_object* v_droppedEntriesRef_6997_, lean_object* v_droppedKeys_6998_, lean_object* v___y_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_){
_start:
{
lean_object* v_t_7005_; lean_object* v___x_7008_; 
v___x_7008_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_6996_, v___y_7001_, v___y_7002_);
if (lean_obj_tag(v___x_7008_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6997_) == 1)
{
lean_object* v_a_7009_; lean_object* v_val_7010_; lean_object* v___x_7012_; uint8_t v_isShared_7013_; uint8_t v_isSharedCheck_7036_; 
v_a_7009_ = lean_ctor_get(v___x_7008_, 0);
lean_inc(v_a_7009_);
lean_dec_ref_known(v___x_7008_, 1);
v_val_7010_ = lean_ctor_get(v_droppedEntriesRef_6997_, 0);
v_isSharedCheck_7036_ = !lean_is_exclusive(v_droppedEntriesRef_6997_);
if (v_isSharedCheck_7036_ == 0)
{
v___x_7012_ = v_droppedEntriesRef_6997_;
v_isShared_7013_ = v_isSharedCheck_7036_;
goto v_resetjp_7011_;
}
else
{
lean_inc(v_val_7010_);
lean_dec(v_droppedEntriesRef_6997_);
v___x_7012_ = lean_box(0);
v_isShared_7013_ = v_isSharedCheck_7036_;
goto v_resetjp_7011_;
}
v_resetjp_7011_:
{
lean_object* v___x_7014_; 
v___x_7014_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7009_, v_droppedKeys_6998_, v___y_6999_, v___y_7000_, v___y_7001_, v___y_7002_);
lean_dec(v_droppedKeys_6998_);
if (lean_obj_tag(v___x_7014_) == 0)
{
lean_object* v_a_7015_; lean_object* v_fst_7016_; lean_object* v_snd_7017_; lean_object* v___x_7018_; lean_object* v___y_7020_; 
v_a_7015_ = lean_ctor_get(v___x_7014_, 0);
lean_inc(v_a_7015_);
lean_dec_ref_known(v___x_7014_, 1);
v_fst_7016_ = lean_ctor_get(v_a_7015_, 0);
lean_inc(v_fst_7016_);
v_snd_7017_ = lean_ctor_get(v_a_7015_, 1);
lean_inc(v_snd_7017_);
lean_dec(v_a_7015_);
v___x_7018_ = lean_st_ref_get(v_val_7010_);
if (lean_obj_tag(v___x_7018_) == 0)
{
lean_object* v___x_7026_; 
v___x_7026_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7020_ = v___x_7026_;
goto v___jp_7019_;
}
else
{
lean_object* v_val_7027_; 
v_val_7027_ = lean_ctor_get(v___x_7018_, 0);
lean_inc(v_val_7027_);
lean_dec_ref_known(v___x_7018_, 1);
v___y_7020_ = v_val_7027_;
goto v___jp_7019_;
}
v___jp_7019_:
{
lean_object* v___x_7021_; lean_object* v___x_7023_; 
v___x_7021_ = l_Array_append___redArg(v___y_7020_, v_fst_7016_);
lean_dec(v_fst_7016_);
if (v_isShared_7013_ == 0)
{
lean_ctor_set(v___x_7012_, 0, v___x_7021_);
v___x_7023_ = v___x_7012_;
goto v_reusejp_7022_;
}
else
{
lean_object* v_reuseFailAlloc_7025_; 
v_reuseFailAlloc_7025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7025_, 0, v___x_7021_);
v___x_7023_ = v_reuseFailAlloc_7025_;
goto v_reusejp_7022_;
}
v_reusejp_7022_:
{
lean_object* v___x_7024_; 
v___x_7024_ = lean_st_ref_swap(v_val_7010_, v___x_7023_);
lean_dec(v_val_7010_);
lean_dec(v___x_7024_);
v_t_7005_ = v_snd_7017_;
goto v___jp_7004_;
}
}
}
else
{
lean_object* v_a_7028_; lean_object* v___x_7030_; uint8_t v_isShared_7031_; uint8_t v_isSharedCheck_7035_; 
lean_del_object(v___x_7012_);
lean_dec(v_val_7010_);
v_a_7028_ = lean_ctor_get(v___x_7014_, 0);
v_isSharedCheck_7035_ = !lean_is_exclusive(v___x_7014_);
if (v_isSharedCheck_7035_ == 0)
{
v___x_7030_ = v___x_7014_;
v_isShared_7031_ = v_isSharedCheck_7035_;
goto v_resetjp_7029_;
}
else
{
lean_inc(v_a_7028_);
lean_dec(v___x_7014_);
v___x_7030_ = lean_box(0);
v_isShared_7031_ = v_isSharedCheck_7035_;
goto v_resetjp_7029_;
}
v_resetjp_7029_:
{
lean_object* v___x_7033_; 
if (v_isShared_7031_ == 0)
{
v___x_7033_ = v___x_7030_;
goto v_reusejp_7032_;
}
else
{
lean_object* v_reuseFailAlloc_7034_; 
v_reuseFailAlloc_7034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7034_, 0, v_a_7028_);
v___x_7033_ = v_reuseFailAlloc_7034_;
goto v_reusejp_7032_;
}
v_reusejp_7032_:
{
return v___x_7033_;
}
}
}
}
}
else
{
lean_object* v_a_7037_; lean_object* v___x_7038_; 
lean_dec(v_droppedEntriesRef_6997_);
v_a_7037_ = lean_ctor_get(v___x_7008_, 0);
lean_inc(v_a_7037_);
lean_dec_ref_known(v___x_7008_, 1);
v___x_7038_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7037_, v_droppedKeys_6998_, v___y_6999_, v___y_7000_, v___y_7001_, v___y_7002_);
if (lean_obj_tag(v___x_7038_) == 0)
{
lean_object* v_a_7039_; 
v_a_7039_ = lean_ctor_get(v___x_7038_, 0);
lean_inc(v_a_7039_);
lean_dec_ref_known(v___x_7038_, 1);
v_t_7005_ = v_a_7039_;
goto v___jp_7004_;
}
else
{
lean_object* v_a_7040_; lean_object* v___x_7042_; uint8_t v_isShared_7043_; uint8_t v_isSharedCheck_7047_; 
v_a_7040_ = lean_ctor_get(v___x_7038_, 0);
v_isSharedCheck_7047_ = !lean_is_exclusive(v___x_7038_);
if (v_isSharedCheck_7047_ == 0)
{
v___x_7042_ = v___x_7038_;
v_isShared_7043_ = v_isSharedCheck_7047_;
goto v_resetjp_7041_;
}
else
{
lean_inc(v_a_7040_);
lean_dec(v___x_7038_);
v___x_7042_ = lean_box(0);
v_isShared_7043_ = v_isSharedCheck_7047_;
goto v_resetjp_7041_;
}
v_resetjp_7041_:
{
lean_object* v___x_7045_; 
if (v_isShared_7043_ == 0)
{
v___x_7045_ = v___x_7042_;
goto v_reusejp_7044_;
}
else
{
lean_object* v_reuseFailAlloc_7046_; 
v_reuseFailAlloc_7046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7046_, 0, v_a_7040_);
v___x_7045_ = v_reuseFailAlloc_7046_;
goto v_reusejp_7044_;
}
v_reusejp_7044_:
{
return v___x_7045_;
}
}
}
}
}
else
{
lean_object* v_a_7048_; lean_object* v___x_7050_; uint8_t v_isShared_7051_; uint8_t v_isSharedCheck_7055_; 
lean_dec(v_droppedKeys_6998_);
lean_dec(v_droppedEntriesRef_6997_);
v_a_7048_ = lean_ctor_get(v___x_7008_, 0);
v_isSharedCheck_7055_ = !lean_is_exclusive(v___x_7008_);
if (v_isSharedCheck_7055_ == 0)
{
v___x_7050_ = v___x_7008_;
v_isShared_7051_ = v_isSharedCheck_7055_;
goto v_resetjp_7049_;
}
else
{
lean_inc(v_a_7048_);
lean_dec(v___x_7008_);
v___x_7050_ = lean_box(0);
v_isShared_7051_ = v_isSharedCheck_7055_;
goto v_resetjp_7049_;
}
v_resetjp_7049_:
{
lean_object* v___x_7053_; 
if (v_isShared_7051_ == 0)
{
v___x_7053_ = v___x_7050_;
goto v_reusejp_7052_;
}
else
{
lean_object* v_reuseFailAlloc_7054_; 
v_reuseFailAlloc_7054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7054_, 0, v_a_7048_);
v___x_7053_ = v_reuseFailAlloc_7054_;
goto v_reusejp_7052_;
}
v_reusejp_7052_:
{
return v___x_7053_;
}
}
}
v___jp_7004_:
{
lean_object* v___x_7006_; lean_object* v___x_7007_; 
v___x_7006_ = lean_st_mk_ref(v_t_7005_);
v___x_7007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7007_, 0, v___x_7006_);
return v___x_7007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7056_, lean_object* v_droppedEntriesRef_7057_, lean_object* v_droppedKeys_7058_, lean_object* v___y_7059_, lean_object* v___y_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_, lean_object* v___y_7063_){
_start:
{
lean_object* v_res_7064_; 
v_res_7064_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7056_, v_droppedEntriesRef_7057_, v_droppedKeys_7058_, v___y_7059_, v___y_7060_, v___y_7061_, v___y_7062_);
lean_dec(v___y_7062_);
lean_dec_ref(v___y_7061_);
lean_dec(v___y_7060_);
lean_dec_ref(v___y_7059_);
return v_res_7064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7066_, lean_object* v_droppedKeys_7067_, lean_object* v_droppedEntriesRef_7068_, lean_object* v_a_7069_, lean_object* v_a_7070_, lean_object* v_a_7071_, lean_object* v_a_7072_){
_start:
{
lean_object* v_options_7074_; lean_object* v___f_7075_; lean_object* v___x_7076_; lean_object* v___x_7077_; lean_object* v___x_7078_; 
v_options_7074_ = lean_ctor_get(v_a_7071_, 2);
v___f_7075_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7075_, 0, v_entriesForConst_7066_);
lean_closure_set(v___f_7075_, 1, v_droppedEntriesRef_7068_);
lean_closure_set(v___f_7075_, 2, v_droppedKeys_7067_);
v___x_7076_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7077_ = lean_box(0);
v___x_7078_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7076_, v_options_7074_, v___f_7075_, v___x_7077_, v_a_7069_, v_a_7070_, v_a_7071_, v_a_7072_);
return v___x_7078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7079_, lean_object* v_droppedKeys_7080_, lean_object* v_droppedEntriesRef_7081_, lean_object* v_a_7082_, lean_object* v_a_7083_, lean_object* v_a_7084_, lean_object* v_a_7085_, lean_object* v_a_7086_){
_start:
{
lean_object* v_res_7087_; 
v_res_7087_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7079_, v_droppedKeys_7080_, v_droppedEntriesRef_7081_, v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_);
lean_dec(v_a_7085_);
lean_dec_ref(v_a_7084_);
lean_dec(v_a_7083_);
lean_dec_ref(v_a_7082_);
return v_res_7087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7088_, lean_object* v_entriesForConst_7089_, lean_object* v_droppedKeys_7090_, lean_object* v_droppedEntriesRef_7091_, lean_object* v_a_7092_, lean_object* v_a_7093_, lean_object* v_a_7094_, lean_object* v_a_7095_){
_start:
{
lean_object* v___x_7097_; 
v___x_7097_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7089_, v_droppedKeys_7090_, v_droppedEntriesRef_7091_, v_a_7092_, v_a_7093_, v_a_7094_, v_a_7095_);
return v___x_7097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7098_, lean_object* v_entriesForConst_7099_, lean_object* v_droppedKeys_7100_, lean_object* v_droppedEntriesRef_7101_, lean_object* v_a_7102_, lean_object* v_a_7103_, lean_object* v_a_7104_, lean_object* v_a_7105_, lean_object* v_a_7106_){
_start:
{
lean_object* v_res_7107_; 
v_res_7107_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7098_, v_entriesForConst_7099_, v_droppedKeys_7100_, v_droppedEntriesRef_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_);
lean_dec(v_a_7105_);
lean_dec_ref(v_a_7104_);
lean_dec(v_a_7103_);
lean_dec_ref(v_a_7102_);
return v_res_7107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7108_, lean_object* v_ty_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_, lean_object* v___y_7112_, lean_object* v___y_7113_){
_start:
{
lean_object* v___x_7115_; lean_object* v___x_7116_; 
v___x_7115_ = lean_st_ref_get(v_moduleRef_7108_);
v___x_7116_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7115_, v_ty_7109_, v___y_7110_, v___y_7111_, v___y_7112_, v___y_7113_);
if (lean_obj_tag(v___x_7116_) == 0)
{
lean_object* v_a_7117_; lean_object* v___x_7119_; uint8_t v_isShared_7120_; uint8_t v_isSharedCheck_7127_; 
v_a_7117_ = lean_ctor_get(v___x_7116_, 0);
v_isSharedCheck_7127_ = !lean_is_exclusive(v___x_7116_);
if (v_isSharedCheck_7127_ == 0)
{
v___x_7119_ = v___x_7116_;
v_isShared_7120_ = v_isSharedCheck_7127_;
goto v_resetjp_7118_;
}
else
{
lean_inc(v_a_7117_);
lean_dec(v___x_7116_);
v___x_7119_ = lean_box(0);
v_isShared_7120_ = v_isSharedCheck_7127_;
goto v_resetjp_7118_;
}
v_resetjp_7118_:
{
lean_object* v_fst_7121_; lean_object* v_snd_7122_; lean_object* v___x_7123_; lean_object* v___x_7125_; 
v_fst_7121_ = lean_ctor_get(v_a_7117_, 0);
lean_inc(v_fst_7121_);
v_snd_7122_ = lean_ctor_get(v_a_7117_, 1);
lean_inc(v_snd_7122_);
lean_dec(v_a_7117_);
v___x_7123_ = lean_st_ref_swap(v_moduleRef_7108_, v_snd_7122_);
lean_dec(v___x_7123_);
if (v_isShared_7120_ == 0)
{
lean_ctor_set(v___x_7119_, 0, v_fst_7121_);
v___x_7125_ = v___x_7119_;
goto v_reusejp_7124_;
}
else
{
lean_object* v_reuseFailAlloc_7126_; 
v_reuseFailAlloc_7126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7126_, 0, v_fst_7121_);
v___x_7125_ = v_reuseFailAlloc_7126_;
goto v_reusejp_7124_;
}
v_reusejp_7124_:
{
return v___x_7125_;
}
}
}
else
{
lean_object* v_a_7128_; lean_object* v___x_7130_; uint8_t v_isShared_7131_; uint8_t v_isSharedCheck_7135_; 
v_a_7128_ = lean_ctor_get(v___x_7116_, 0);
v_isSharedCheck_7135_ = !lean_is_exclusive(v___x_7116_);
if (v_isSharedCheck_7135_ == 0)
{
v___x_7130_ = v___x_7116_;
v_isShared_7131_ = v_isSharedCheck_7135_;
goto v_resetjp_7129_;
}
else
{
lean_inc(v_a_7128_);
lean_dec(v___x_7116_);
v___x_7130_ = lean_box(0);
v_isShared_7131_ = v_isSharedCheck_7135_;
goto v_resetjp_7129_;
}
v_resetjp_7129_:
{
lean_object* v___x_7133_; 
if (v_isShared_7131_ == 0)
{
v___x_7133_ = v___x_7130_;
goto v_reusejp_7132_;
}
else
{
lean_object* v_reuseFailAlloc_7134_; 
v_reuseFailAlloc_7134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7134_, 0, v_a_7128_);
v___x_7133_ = v_reuseFailAlloc_7134_;
goto v_reusejp_7132_;
}
v_reusejp_7132_:
{
return v___x_7133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7136_, lean_object* v_ty_7137_, lean_object* v___y_7138_, lean_object* v___y_7139_, lean_object* v___y_7140_, lean_object* v___y_7141_, lean_object* v___y_7142_){
_start:
{
lean_object* v_res_7143_; 
v_res_7143_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7136_, v_ty_7137_, v___y_7138_, v___y_7139_, v___y_7140_, v___y_7141_);
lean_dec(v___y_7141_);
lean_dec_ref(v___y_7140_);
lean_dec(v___y_7139_);
lean_dec_ref(v___y_7138_);
lean_dec(v_moduleRef_7136_);
return v_res_7143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7145_, lean_object* v_ty_7146_, lean_object* v_a_7147_, lean_object* v_a_7148_, lean_object* v_a_7149_, lean_object* v_a_7150_){
_start:
{
lean_object* v_options_7152_; lean_object* v___f_7153_; lean_object* v___x_7154_; lean_object* v___x_7155_; lean_object* v___x_7156_; 
v_options_7152_ = lean_ctor_get(v_a_7149_, 2);
v___f_7153_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7153_, 0, v_moduleRef_7145_);
lean_closure_set(v___f_7153_, 1, v_ty_7146_);
v___x_7154_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7155_ = lean_box(0);
v___x_7156_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7154_, v_options_7152_, v___f_7153_, v___x_7155_, v_a_7147_, v_a_7148_, v_a_7149_, v_a_7150_);
return v___x_7156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7157_, lean_object* v_ty_7158_, lean_object* v_a_7159_, lean_object* v_a_7160_, lean_object* v_a_7161_, lean_object* v_a_7162_, lean_object* v_a_7163_){
_start:
{
lean_object* v_res_7164_; 
v_res_7164_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7157_, v_ty_7158_, v_a_7159_, v_a_7160_, v_a_7161_, v_a_7162_);
lean_dec(v_a_7162_);
lean_dec_ref(v_a_7161_);
lean_dec(v_a_7160_);
lean_dec_ref(v_a_7159_);
return v_res_7164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7165_, lean_object* v_moduleRef_7166_, lean_object* v_ty_7167_, lean_object* v_a_7168_, lean_object* v_a_7169_, lean_object* v_a_7170_, lean_object* v_a_7171_){
_start:
{
lean_object* v___x_7173_; 
v___x_7173_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7166_, v_ty_7167_, v_a_7168_, v_a_7169_, v_a_7170_, v_a_7171_);
return v___x_7173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7174_, lean_object* v_moduleRef_7175_, lean_object* v_ty_7176_, lean_object* v_a_7177_, lean_object* v_a_7178_, lean_object* v_a_7179_, lean_object* v_a_7180_, lean_object* v_a_7181_){
_start:
{
lean_object* v_res_7182_; 
v_res_7182_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7174_, v_moduleRef_7175_, v_ty_7176_, v_a_7177_, v_a_7178_, v_a_7179_, v_a_7180_);
lean_dec(v_a_7180_);
lean_dec_ref(v_a_7179_);
lean_dec(v_a_7178_);
lean_dec_ref(v_a_7177_);
return v_res_7182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7183_, lean_object* v_j_7184_, size_t v_sz_7185_, size_t v_i_7186_, lean_object* v_bs_7187_){
_start:
{
uint8_t v___x_7188_; 
v___x_7188_ = lean_usize_dec_lt(v_i_7186_, v_sz_7185_);
if (v___x_7188_ == 0)
{
lean_dec(v_j_7184_);
lean_dec(v_adjustResult_7183_);
return v_bs_7187_;
}
else
{
lean_object* v_v_7189_; lean_object* v___x_7190_; lean_object* v_bs_x27_7191_; lean_object* v___x_7192_; size_t v___x_7193_; size_t v___x_7194_; lean_object* v___x_7195_; 
v_v_7189_ = lean_array_uget(v_bs_7187_, v_i_7186_);
v___x_7190_ = lean_unsigned_to_nat(0u);
v_bs_x27_7191_ = lean_array_uset(v_bs_7187_, v_i_7186_, v___x_7190_);
lean_inc(v_adjustResult_7183_);
lean_inc(v_j_7184_);
v___x_7192_ = lean_apply_2(v_adjustResult_7183_, v_j_7184_, v_v_7189_);
v___x_7193_ = ((size_t)1ULL);
v___x_7194_ = lean_usize_add(v_i_7186_, v___x_7193_);
v___x_7195_ = lean_array_uset(v_bs_x27_7191_, v_i_7186_, v___x_7192_);
v_i_7186_ = v___x_7194_;
v_bs_7187_ = v___x_7195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7197_, lean_object* v_j_7198_, lean_object* v_sz_7199_, lean_object* v_i_7200_, lean_object* v_bs_7201_){
_start:
{
size_t v_sz_boxed_7202_; size_t v_i_boxed_7203_; lean_object* v_res_7204_; 
v_sz_boxed_7202_ = lean_unbox_usize(v_sz_7199_);
lean_dec(v_sz_7199_);
v_i_boxed_7203_ = lean_unbox_usize(v_i_7200_);
lean_dec(v_i_7200_);
v_res_7204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7197_, v_j_7198_, v_sz_boxed_7202_, v_i_boxed_7203_, v_bs_7201_);
return v_res_7204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7205_, lean_object* v_j_7206_, lean_object* v_as_7207_, size_t v_i_7208_, size_t v_stop_7209_, lean_object* v_b_7210_){
_start:
{
uint8_t v___x_7211_; 
v___x_7211_ = lean_usize_dec_eq(v_i_7208_, v_stop_7209_);
if (v___x_7211_ == 0)
{
lean_object* v___x_7212_; size_t v_sz_7213_; size_t v___x_7214_; lean_object* v___x_7215_; lean_object* v___x_7216_; size_t v___x_7217_; size_t v___x_7218_; 
v___x_7212_ = lean_array_uget_borrowed(v_as_7207_, v_i_7208_);
v_sz_7213_ = lean_array_size(v___x_7212_);
v___x_7214_ = ((size_t)0ULL);
lean_inc(v___x_7212_);
lean_inc(v_j_7206_);
lean_inc(v_adjustResult_7205_);
v___x_7215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7205_, v_j_7206_, v_sz_7213_, v___x_7214_, v___x_7212_);
v___x_7216_ = l_Array_append___redArg(v_b_7210_, v___x_7215_);
lean_dec_ref(v___x_7215_);
v___x_7217_ = ((size_t)1ULL);
v___x_7218_ = lean_usize_add(v_i_7208_, v___x_7217_);
v_i_7208_ = v___x_7218_;
v_b_7210_ = v___x_7216_;
goto _start;
}
else
{
lean_dec(v_j_7206_);
lean_dec(v_adjustResult_7205_);
return v_b_7210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7220_, lean_object* v_j_7221_, lean_object* v_as_7222_, lean_object* v_i_7223_, lean_object* v_stop_7224_, lean_object* v_b_7225_){
_start:
{
size_t v_i_boxed_7226_; size_t v_stop_boxed_7227_; lean_object* v_res_7228_; 
v_i_boxed_7226_ = lean_unbox_usize(v_i_7223_);
lean_dec(v_i_7223_);
v_stop_boxed_7227_ = lean_unbox_usize(v_stop_7224_);
lean_dec(v_stop_7224_);
v_res_7228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7220_, v_j_7221_, v_as_7222_, v_i_boxed_7226_, v_stop_boxed_7227_, v_b_7225_);
lean_dec_ref(v_as_7222_);
return v_res_7228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7229_, lean_object* v_aa_7230_, lean_object* v_adjustResult_7231_, lean_object* v_n_7232_, lean_object* v_j_7233_, lean_object* v_a_7234_){
_start:
{
lean_object* v_zero_7235_; uint8_t v_isZero_7236_; 
v_zero_7235_ = lean_unsigned_to_nat(0u);
v_isZero_7236_ = lean_nat_dec_eq(v_j_7233_, v_zero_7235_);
if (v_isZero_7236_ == 1)
{
lean_dec(v_j_7233_);
lean_dec(v_adjustResult_7231_);
return v_a_7234_;
}
else
{
lean_object* v_one_7237_; lean_object* v_n_7238_; lean_object* v___x_7239_; lean_object* v___x_7240_; lean_object* v_j_7241_; lean_object* v_b_7242_; lean_object* v___x_7243_; uint8_t v___x_7244_; 
v_one_7237_ = lean_unsigned_to_nat(1u);
v_n_7238_ = lean_nat_sub(v_j_7233_, v_one_7237_);
v___x_7239_ = lean_nat_sub(v_n_7232_, v_j_7233_);
lean_dec(v_j_7233_);
v___x_7240_ = lean_nat_sub(v_n_7229_, v_one_7237_);
v_j_7241_ = lean_nat_sub(v___x_7240_, v___x_7239_);
lean_dec(v___x_7239_);
lean_dec(v___x_7240_);
v_b_7242_ = lean_array_fget_borrowed(v_aa_7230_, v_j_7241_);
v___x_7243_ = lean_array_get_size(v_b_7242_);
v___x_7244_ = lean_nat_dec_lt(v_zero_7235_, v___x_7243_);
if (v___x_7244_ == 0)
{
lean_dec(v_j_7241_);
v_j_7233_ = v_n_7238_;
goto _start;
}
else
{
size_t v___x_7246_; size_t v___x_7247_; lean_object* v___x_7248_; 
v___x_7246_ = ((size_t)0ULL);
v___x_7247_ = lean_usize_of_nat(v___x_7243_);
lean_inc(v_adjustResult_7231_);
v___x_7248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7231_, v_j_7241_, v_b_7242_, v___x_7246_, v___x_7247_, v_a_7234_);
v_j_7233_ = v_n_7238_;
v_a_7234_ = v___x_7248_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7250_, lean_object* v_aa_7251_, lean_object* v_adjustResult_7252_, lean_object* v_n_7253_, lean_object* v_j_7254_, lean_object* v_a_7255_){
_start:
{
lean_object* v_res_7256_; 
v_res_7256_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7250_, v_aa_7251_, v_adjustResult_7252_, v_n_7253_, v_j_7254_, v_a_7255_);
lean_dec(v_n_7253_);
lean_dec_ref(v_aa_7251_);
lean_dec(v_n_7250_);
return v_res_7256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7257_, lean_object* v_adjustResult_7258_, lean_object* v_aa_7259_, lean_object* v_n_7260_, lean_object* v_j_7261_, lean_object* v_a_7262_){
_start:
{
lean_object* v_zero_7263_; uint8_t v_isZero_7264_; 
v_zero_7263_ = lean_unsigned_to_nat(0u);
v_isZero_7264_ = lean_nat_dec_eq(v_j_7261_, v_zero_7263_);
if (v_isZero_7264_ == 1)
{
lean_dec(v_adjustResult_7258_);
return v_a_7262_;
}
else
{
lean_object* v_one_7265_; lean_object* v_n_7266_; lean_object* v___x_7267_; lean_object* v___x_7268_; lean_object* v_j_7269_; lean_object* v_b_7270_; lean_object* v___x_7271_; uint8_t v___x_7272_; 
v_one_7265_ = lean_unsigned_to_nat(1u);
v_n_7266_ = lean_nat_sub(v_j_7261_, v_one_7265_);
v___x_7267_ = lean_nat_sub(v_n_7260_, v_j_7261_);
v___x_7268_ = lean_nat_sub(v_n_7257_, v_one_7265_);
v_j_7269_ = lean_nat_sub(v___x_7268_, v___x_7267_);
lean_dec(v___x_7267_);
lean_dec(v___x_7268_);
v_b_7270_ = lean_array_fget_borrowed(v_aa_7259_, v_j_7269_);
v___x_7271_ = lean_array_get_size(v_b_7270_);
v___x_7272_ = lean_nat_dec_lt(v_zero_7263_, v___x_7271_);
if (v___x_7272_ == 0)
{
lean_object* v___x_7273_; 
lean_dec(v_j_7269_);
v___x_7273_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7257_, v_aa_7259_, v_adjustResult_7258_, v_n_7260_, v_n_7266_, v_a_7262_);
return v___x_7273_;
}
else
{
size_t v___x_7274_; size_t v___x_7275_; lean_object* v___x_7276_; lean_object* v___x_7277_; 
v___x_7274_ = ((size_t)0ULL);
v___x_7275_ = lean_usize_of_nat(v___x_7271_);
lean_inc(v_adjustResult_7258_);
v___x_7276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7258_, v_j_7269_, v_b_7270_, v___x_7274_, v___x_7275_, v_a_7262_);
v___x_7277_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7257_, v_aa_7259_, v_adjustResult_7258_, v_n_7260_, v_n_7266_, v___x_7276_);
return v___x_7277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7278_, lean_object* v_adjustResult_7279_, lean_object* v_aa_7280_, lean_object* v_n_7281_, lean_object* v_j_7282_, lean_object* v_a_7283_){
_start:
{
lean_object* v_res_7284_; 
v_res_7284_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7278_, v_adjustResult_7279_, v_aa_7280_, v_n_7281_, v_j_7282_, v_a_7283_);
lean_dec(v_j_7282_);
lean_dec(v_n_7281_);
lean_dec_ref(v_aa_7280_);
lean_dec(v_n_7278_);
return v_res_7284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7285_, lean_object* v_mr_7286_, lean_object* v_a_7287_){
_start:
{
lean_object* v_n_7288_; lean_object* v___x_7289_; 
v_n_7288_ = lean_array_get_size(v_mr_7286_);
v___x_7289_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7288_, v_adjustResult_7285_, v_mr_7286_, v_n_7288_, v_n_7288_, v_a_7287_);
return v___x_7289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7290_, lean_object* v_mr_7291_, lean_object* v_a_7292_){
_start:
{
lean_object* v_res_7293_; 
v_res_7293_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7290_, v_mr_7291_, v_a_7292_);
lean_dec_ref(v_mr_7291_);
return v_res_7293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7294_, lean_object* v_ref_7295_, lean_object* v_addEntry_7296_, lean_object* v_droppedKeys_7297_, lean_object* v_constantsPerTask_7298_, lean_object* v_droppedEntriesRef_7299_, lean_object* v_adjustResult_7300_, lean_object* v_ty_7301_, lean_object* v_a_7302_, lean_object* v_a_7303_, lean_object* v_a_7304_, lean_object* v_a_7305_){
_start:
{
lean_object* v___x_7307_; 
lean_inc_ref(v_ty_7301_);
v___x_7307_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7294_, v_ty_7301_, v_a_7302_, v_a_7303_, v_a_7304_, v_a_7305_);
if (lean_obj_tag(v___x_7307_) == 0)
{
lean_object* v_a_7308_; lean_object* v___x_7309_; 
v_a_7308_ = lean_ctor_get(v___x_7307_, 0);
lean_inc(v_a_7308_);
lean_dec_ref_known(v___x_7307_, 1);
v___x_7309_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7295_, v_addEntry_7296_, v_droppedKeys_7297_, v_constantsPerTask_7298_, v_droppedEntriesRef_7299_, v_ty_7301_, v_a_7302_, v_a_7303_, v_a_7304_, v_a_7305_);
if (lean_obj_tag(v___x_7309_) == 0)
{
lean_object* v_a_7310_; lean_object* v___x_7312_; uint8_t v_isShared_7313_; uint8_t v_isSharedCheck_7323_; 
v_a_7310_ = lean_ctor_get(v___x_7309_, 0);
v_isSharedCheck_7323_ = !lean_is_exclusive(v___x_7309_);
if (v_isSharedCheck_7323_ == 0)
{
v___x_7312_ = v___x_7309_;
v_isShared_7313_ = v_isSharedCheck_7323_;
goto v_resetjp_7311_;
}
else
{
lean_inc(v_a_7310_);
lean_dec(v___x_7309_);
v___x_7312_ = lean_box(0);
v_isShared_7313_ = v_isSharedCheck_7323_;
goto v_resetjp_7311_;
}
v_resetjp_7311_:
{
lean_object* v___x_7314_; lean_object* v___x_7315_; lean_object* v___x_7316_; lean_object* v___x_7317_; lean_object* v___x_7318_; lean_object* v___x_7319_; lean_object* v___x_7321_; 
v___x_7314_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7308_);
v___x_7315_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7310_);
v___x_7316_ = lean_nat_add(v___x_7314_, v___x_7315_);
lean_dec(v___x_7315_);
lean_dec(v___x_7314_);
v___x_7317_ = lean_mk_empty_array_with_capacity(v___x_7316_);
lean_dec(v___x_7316_);
lean_inc(v_adjustResult_7300_);
v___x_7318_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7300_, v_a_7308_, v___x_7317_);
lean_dec(v_a_7308_);
v___x_7319_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7300_, v_a_7310_, v___x_7318_);
lean_dec(v_a_7310_);
if (v_isShared_7313_ == 0)
{
lean_ctor_set(v___x_7312_, 0, v___x_7319_);
v___x_7321_ = v___x_7312_;
goto v_reusejp_7320_;
}
else
{
lean_object* v_reuseFailAlloc_7322_; 
v_reuseFailAlloc_7322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7322_, 0, v___x_7319_);
v___x_7321_ = v_reuseFailAlloc_7322_;
goto v_reusejp_7320_;
}
v_reusejp_7320_:
{
return v___x_7321_;
}
}
}
else
{
lean_object* v_a_7324_; lean_object* v___x_7326_; uint8_t v_isShared_7327_; uint8_t v_isSharedCheck_7331_; 
lean_dec(v_a_7308_);
lean_dec(v_adjustResult_7300_);
v_a_7324_ = lean_ctor_get(v___x_7309_, 0);
v_isSharedCheck_7331_ = !lean_is_exclusive(v___x_7309_);
if (v_isSharedCheck_7331_ == 0)
{
v___x_7326_ = v___x_7309_;
v_isShared_7327_ = v_isSharedCheck_7331_;
goto v_resetjp_7325_;
}
else
{
lean_inc(v_a_7324_);
lean_dec(v___x_7309_);
v___x_7326_ = lean_box(0);
v_isShared_7327_ = v_isSharedCheck_7331_;
goto v_resetjp_7325_;
}
v_resetjp_7325_:
{
lean_object* v___x_7329_; 
if (v_isShared_7327_ == 0)
{
v___x_7329_ = v___x_7326_;
goto v_reusejp_7328_;
}
else
{
lean_object* v_reuseFailAlloc_7330_; 
v_reuseFailAlloc_7330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7330_, 0, v_a_7324_);
v___x_7329_ = v_reuseFailAlloc_7330_;
goto v_reusejp_7328_;
}
v_reusejp_7328_:
{
return v___x_7329_;
}
}
}
}
else
{
lean_object* v_a_7332_; lean_object* v___x_7334_; uint8_t v_isShared_7335_; uint8_t v_isSharedCheck_7339_; 
lean_dec_ref(v_ty_7301_);
lean_dec(v_adjustResult_7300_);
lean_dec(v_droppedEntriesRef_7299_);
lean_dec(v_constantsPerTask_7298_);
lean_dec(v_droppedKeys_7297_);
lean_dec_ref(v_addEntry_7296_);
v_a_7332_ = lean_ctor_get(v___x_7307_, 0);
v_isSharedCheck_7339_ = !lean_is_exclusive(v___x_7307_);
if (v_isSharedCheck_7339_ == 0)
{
v___x_7334_ = v___x_7307_;
v_isShared_7335_ = v_isSharedCheck_7339_;
goto v_resetjp_7333_;
}
else
{
lean_inc(v_a_7332_);
lean_dec(v___x_7307_);
v___x_7334_ = lean_box(0);
v_isShared_7335_ = v_isSharedCheck_7339_;
goto v_resetjp_7333_;
}
v_resetjp_7333_:
{
lean_object* v___x_7337_; 
if (v_isShared_7335_ == 0)
{
v___x_7337_ = v___x_7334_;
goto v_reusejp_7336_;
}
else
{
lean_object* v_reuseFailAlloc_7338_; 
v_reuseFailAlloc_7338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7338_, 0, v_a_7332_);
v___x_7337_ = v_reuseFailAlloc_7338_;
goto v_reusejp_7336_;
}
v_reusejp_7336_:
{
return v___x_7337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7340_, lean_object* v_ref_7341_, lean_object* v_addEntry_7342_, lean_object* v_droppedKeys_7343_, lean_object* v_constantsPerTask_7344_, lean_object* v_droppedEntriesRef_7345_, lean_object* v_adjustResult_7346_, lean_object* v_ty_7347_, lean_object* v_a_7348_, lean_object* v_a_7349_, lean_object* v_a_7350_, lean_object* v_a_7351_, lean_object* v_a_7352_){
_start:
{
lean_object* v_res_7353_; 
v_res_7353_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7340_, v_ref_7341_, v_addEntry_7342_, v_droppedKeys_7343_, v_constantsPerTask_7344_, v_droppedEntriesRef_7345_, v_adjustResult_7346_, v_ty_7347_, v_a_7348_, v_a_7349_, v_a_7350_, v_a_7351_);
lean_dec(v_a_7351_);
lean_dec_ref(v_a_7350_);
lean_dec(v_a_7349_);
lean_dec_ref(v_a_7348_);
lean_dec(v_ref_7341_);
return v_res_7353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7354_, lean_object* v_00_u03b2_7355_, lean_object* v_moduleTreeRef_7356_, lean_object* v_ref_7357_, lean_object* v_addEntry_7358_, lean_object* v_droppedKeys_7359_, lean_object* v_constantsPerTask_7360_, lean_object* v_droppedEntriesRef_7361_, lean_object* v_adjustResult_7362_, lean_object* v_ty_7363_, lean_object* v_a_7364_, lean_object* v_a_7365_, lean_object* v_a_7366_, lean_object* v_a_7367_){
_start:
{
lean_object* v___x_7369_; 
v___x_7369_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7356_, v_ref_7357_, v_addEntry_7358_, v_droppedKeys_7359_, v_constantsPerTask_7360_, v_droppedEntriesRef_7361_, v_adjustResult_7362_, v_ty_7363_, v_a_7364_, v_a_7365_, v_a_7366_, v_a_7367_);
return v___x_7369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7370_, lean_object* v_00_u03b2_7371_, lean_object* v_moduleTreeRef_7372_, lean_object* v_ref_7373_, lean_object* v_addEntry_7374_, lean_object* v_droppedKeys_7375_, lean_object* v_constantsPerTask_7376_, lean_object* v_droppedEntriesRef_7377_, lean_object* v_adjustResult_7378_, lean_object* v_ty_7379_, lean_object* v_a_7380_, lean_object* v_a_7381_, lean_object* v_a_7382_, lean_object* v_a_7383_, lean_object* v_a_7384_){
_start:
{
lean_object* v_res_7385_; 
v_res_7385_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7370_, v_00_u03b2_7371_, v_moduleTreeRef_7372_, v_ref_7373_, v_addEntry_7374_, v_droppedKeys_7375_, v_constantsPerTask_7376_, v_droppedEntriesRef_7377_, v_adjustResult_7378_, v_ty_7379_, v_a_7380_, v_a_7381_, v_a_7382_, v_a_7383_);
lean_dec(v_a_7383_);
lean_dec_ref(v_a_7382_);
lean_dec(v_a_7381_);
lean_dec_ref(v_a_7380_);
lean_dec(v_ref_7373_);
return v_res_7385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7386_, lean_object* v_00_u03b2_7387_, lean_object* v_adjustResult_7388_, lean_object* v_mr_7389_, lean_object* v_a_7390_){
_start:
{
lean_object* v___x_7391_; 
v___x_7391_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7388_, v_mr_7389_, v_a_7390_);
return v___x_7391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7392_, lean_object* v_00_u03b2_7393_, lean_object* v_adjustResult_7394_, lean_object* v_mr_7395_, lean_object* v_a_7396_){
_start:
{
lean_object* v_res_7397_; 
v_res_7397_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7392_, v_00_u03b2_7393_, v_adjustResult_7394_, v_mr_7395_, v_a_7396_);
lean_dec_ref(v_mr_7395_);
return v_res_7397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7398_, lean_object* v_00_u03b2_7399_, lean_object* v_adjustResult_7400_, lean_object* v_j_7401_, size_t v_sz_7402_, size_t v_i_7403_, lean_object* v_bs_7404_){
_start:
{
lean_object* v___x_7405_; 
v___x_7405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7400_, v_j_7401_, v_sz_7402_, v_i_7403_, v_bs_7404_);
return v___x_7405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7406_, lean_object* v_00_u03b2_7407_, lean_object* v_adjustResult_7408_, lean_object* v_j_7409_, lean_object* v_sz_7410_, lean_object* v_i_7411_, lean_object* v_bs_7412_){
_start:
{
size_t v_sz_boxed_7413_; size_t v_i_boxed_7414_; lean_object* v_res_7415_; 
v_sz_boxed_7413_ = lean_unbox_usize(v_sz_7410_);
lean_dec(v_sz_7410_);
v_i_boxed_7414_ = lean_unbox_usize(v_i_7411_);
lean_dec(v_i_7411_);
v_res_7415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7406_, v_00_u03b2_7407_, v_adjustResult_7408_, v_j_7409_, v_sz_boxed_7413_, v_i_boxed_7414_, v_bs_7412_);
return v_res_7415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7416_, lean_object* v_00_u03b2_7417_, lean_object* v_adjustResult_7418_, lean_object* v_j_7419_, lean_object* v_as_7420_, size_t v_i_7421_, size_t v_stop_7422_, lean_object* v_b_7423_){
_start:
{
lean_object* v___x_7424_; 
v___x_7424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7418_, v_j_7419_, v_as_7420_, v_i_7421_, v_stop_7422_, v_b_7423_);
return v___x_7424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7425_, lean_object* v_00_u03b2_7426_, lean_object* v_adjustResult_7427_, lean_object* v_j_7428_, lean_object* v_as_7429_, lean_object* v_i_7430_, lean_object* v_stop_7431_, lean_object* v_b_7432_){
_start:
{
size_t v_i_boxed_7433_; size_t v_stop_boxed_7434_; lean_object* v_res_7435_; 
v_i_boxed_7433_ = lean_unbox_usize(v_i_7430_);
lean_dec(v_i_7430_);
v_stop_boxed_7434_ = lean_unbox_usize(v_stop_7431_);
lean_dec(v_stop_7431_);
v_res_7435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7425_, v_00_u03b2_7426_, v_adjustResult_7427_, v_j_7428_, v_as_7429_, v_i_boxed_7433_, v_stop_boxed_7434_, v_b_7432_);
lean_dec_ref(v_as_7429_);
return v_res_7435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7436_, lean_object* v_n_7437_, lean_object* v_00_u03b1_7438_, lean_object* v_adjustResult_7439_, lean_object* v_aa_7440_, lean_object* v_n_7441_, lean_object* v_j_7442_, lean_object* v_a_7443_, lean_object* v_a_7444_){
_start:
{
lean_object* v___x_7445_; 
v___x_7445_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7437_, v_adjustResult_7439_, v_aa_7440_, v_n_7441_, v_j_7442_, v_a_7444_);
return v___x_7445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7446_, lean_object* v_n_7447_, lean_object* v_00_u03b1_7448_, lean_object* v_adjustResult_7449_, lean_object* v_aa_7450_, lean_object* v_n_7451_, lean_object* v_j_7452_, lean_object* v_a_7453_, lean_object* v_a_7454_){
_start:
{
lean_object* v_res_7455_; 
v_res_7455_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7446_, v_n_7447_, v_00_u03b1_7448_, v_adjustResult_7449_, v_aa_7450_, v_n_7451_, v_j_7452_, v_a_7453_, v_a_7454_);
lean_dec(v_j_7452_);
lean_dec(v_n_7451_);
lean_dec_ref(v_aa_7450_);
lean_dec(v_n_7447_);
return v_res_7455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7456_, lean_object* v_n_7457_, lean_object* v_00_u03b1_7458_, lean_object* v_aa_7459_, lean_object* v_adjustResult_7460_, lean_object* v_n_7461_, lean_object* v_j_7462_, lean_object* v_a_7463_, lean_object* v_a_7464_){
_start:
{
lean_object* v___x_7465_; 
v___x_7465_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7457_, v_aa_7459_, v_adjustResult_7460_, v_n_7461_, v_j_7462_, v_a_7464_);
return v___x_7465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7466_, lean_object* v_n_7467_, lean_object* v_00_u03b1_7468_, lean_object* v_aa_7469_, lean_object* v_adjustResult_7470_, lean_object* v_n_7471_, lean_object* v_j_7472_, lean_object* v_a_7473_, lean_object* v_a_7474_){
_start:
{
lean_object* v_res_7475_; 
v_res_7475_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7466_, v_n_7467_, v_00_u03b1_7468_, v_aa_7469_, v_adjustResult_7470_, v_n_7471_, v_j_7472_, v_a_7473_, v_a_7474_);
lean_dec(v_n_7471_);
lean_dec_ref(v_aa_7469_);
lean_dec(v_n_7467_);
return v_res_7475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7476_, lean_object* v_v_7477_){
_start:
{
lean_inc(v_v_7477_);
return v_v_7477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7478_, lean_object* v_v_7479_){
_start:
{
lean_object* v_res_7480_; 
v_res_7480_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7478_, v_v_7479_);
lean_dec(v_v_7479_);
lean_dec(v_x_7478_);
return v_res_7480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7482_, lean_object* v_addEntry_7483_, lean_object* v_droppedKeys_7484_, lean_object* v_constantsPerTask_7485_, lean_object* v_droppedEntriesRef_7486_, lean_object* v_ty_7487_, lean_object* v_a_7488_, lean_object* v_a_7489_, lean_object* v_a_7490_, lean_object* v_a_7491_){
_start:
{
lean_object* v___x_7493_; 
lean_inc(v_droppedEntriesRef_7486_);
lean_inc(v_droppedKeys_7484_);
lean_inc_ref(v_addEntry_7483_);
v___x_7493_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7483_, v_droppedKeys_7484_, v_droppedEntriesRef_7486_, v_a_7488_, v_a_7489_, v_a_7490_, v_a_7491_);
if (lean_obj_tag(v___x_7493_) == 0)
{
lean_object* v_a_7494_; lean_object* v___f_7495_; lean_object* v___x_7496_; 
v_a_7494_ = lean_ctor_get(v___x_7493_, 0);
lean_inc(v_a_7494_);
lean_dec_ref_known(v___x_7493_, 1);
v___f_7495_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7496_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7494_, v_ref_7482_, v_addEntry_7483_, v_droppedKeys_7484_, v_constantsPerTask_7485_, v_droppedEntriesRef_7486_, v___f_7495_, v_ty_7487_, v_a_7488_, v_a_7489_, v_a_7490_, v_a_7491_);
return v___x_7496_;
}
else
{
lean_object* v_a_7497_; lean_object* v___x_7499_; uint8_t v_isShared_7500_; uint8_t v_isSharedCheck_7504_; 
lean_dec_ref(v_ty_7487_);
lean_dec(v_droppedEntriesRef_7486_);
lean_dec(v_constantsPerTask_7485_);
lean_dec(v_droppedKeys_7484_);
lean_dec_ref(v_addEntry_7483_);
v_a_7497_ = lean_ctor_get(v___x_7493_, 0);
v_isSharedCheck_7504_ = !lean_is_exclusive(v___x_7493_);
if (v_isSharedCheck_7504_ == 0)
{
v___x_7499_ = v___x_7493_;
v_isShared_7500_ = v_isSharedCheck_7504_;
goto v_resetjp_7498_;
}
else
{
lean_inc(v_a_7497_);
lean_dec(v___x_7493_);
v___x_7499_ = lean_box(0);
v_isShared_7500_ = v_isSharedCheck_7504_;
goto v_resetjp_7498_;
}
v_resetjp_7498_:
{
lean_object* v___x_7502_; 
if (v_isShared_7500_ == 0)
{
v___x_7502_ = v___x_7499_;
goto v_reusejp_7501_;
}
else
{
lean_object* v_reuseFailAlloc_7503_; 
v_reuseFailAlloc_7503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7503_, 0, v_a_7497_);
v___x_7502_ = v_reuseFailAlloc_7503_;
goto v_reusejp_7501_;
}
v_reusejp_7501_:
{
return v___x_7502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7505_, lean_object* v_addEntry_7506_, lean_object* v_droppedKeys_7507_, lean_object* v_constantsPerTask_7508_, lean_object* v_droppedEntriesRef_7509_, lean_object* v_ty_7510_, lean_object* v_a_7511_, lean_object* v_a_7512_, lean_object* v_a_7513_, lean_object* v_a_7514_, lean_object* v_a_7515_){
_start:
{
lean_object* v_res_7516_; 
v_res_7516_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7505_, v_addEntry_7506_, v_droppedKeys_7507_, v_constantsPerTask_7508_, v_droppedEntriesRef_7509_, v_ty_7510_, v_a_7511_, v_a_7512_, v_a_7513_, v_a_7514_);
lean_dec(v_a_7514_);
lean_dec_ref(v_a_7513_);
lean_dec(v_a_7512_);
lean_dec_ref(v_a_7511_);
lean_dec(v_ref_7505_);
return v_res_7516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7517_, lean_object* v_ref_7518_, lean_object* v_addEntry_7519_, lean_object* v_droppedKeys_7520_, lean_object* v_constantsPerTask_7521_, lean_object* v_droppedEntriesRef_7522_, lean_object* v_ty_7523_, lean_object* v_a_7524_, lean_object* v_a_7525_, lean_object* v_a_7526_, lean_object* v_a_7527_){
_start:
{
lean_object* v___x_7529_; 
v___x_7529_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7518_, v_addEntry_7519_, v_droppedKeys_7520_, v_constantsPerTask_7521_, v_droppedEntriesRef_7522_, v_ty_7523_, v_a_7524_, v_a_7525_, v_a_7526_, v_a_7527_);
return v___x_7529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7530_, lean_object* v_ref_7531_, lean_object* v_addEntry_7532_, lean_object* v_droppedKeys_7533_, lean_object* v_constantsPerTask_7534_, lean_object* v_droppedEntriesRef_7535_, lean_object* v_ty_7536_, lean_object* v_a_7537_, lean_object* v_a_7538_, lean_object* v_a_7539_, lean_object* v_a_7540_, lean_object* v_a_7541_){
_start:
{
lean_object* v_res_7542_; 
v_res_7542_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7530_, v_ref_7531_, v_addEntry_7532_, v_droppedKeys_7533_, v_constantsPerTask_7534_, v_droppedEntriesRef_7535_, v_ty_7536_, v_a_7537_, v_a_7538_, v_a_7539_, v_a_7540_);
lean_dec(v_a_7540_);
lean_dec_ref(v_a_7539_);
lean_dec(v_a_7538_);
lean_dec_ref(v_a_7537_);
lean_dec(v_ref_7531_);
return v_res_7542_;
}
}
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
