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
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_780_; lean_object* v___y_790_; uint8_t v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v_toCold_799_; lean_object* v_currRecDepth_800_; lean_object* v_ref_801_; uint8_t v_diag_802_; uint8_t v_suppressElabErrors_803_; lean_object* v_maxRecDepth_804_; lean_object* v_cancelTk_x3f_805_; 
v_toCold_799_ = lean_ctor_get(v___y_776_, 0);
v_currRecDepth_800_ = lean_ctor_get(v___y_776_, 1);
v_ref_801_ = lean_ctor_get(v___y_776_, 2);
v_diag_802_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*3);
v_suppressElabErrors_803_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*3 + 1);
v_maxRecDepth_804_ = lean_ctor_get(v_toCold_799_, 3);
v_cancelTk_x3f_805_ = lean_ctor_get(v_toCold_799_, 10);
if (lean_obj_tag(v_cancelTk_x3f_805_) == 1)
{
lean_object* v_val_811_; uint8_t v___x_812_; 
v_val_811_ = lean_ctor_get(v_cancelTk_x3f_805_, 0);
v___x_812_ = l_IO_CancelToken_isSet(v_val_811_);
if (v___x_812_ == 0)
{
goto v___jp_806_;
}
else
{
lean_object* v___x_813_; lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_x_774_);
v___x_813_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
goto v___jp_806_;
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
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = lean_nat_add(v___y_790_, v___x_795_);
lean_inc_ref(v___y_792_);
v___x_797_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_797_, 0, v___y_792_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_ctor_set(v___x_797_, 2, v___y_794_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*3, v___y_791_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*3 + 1, v___y_793_);
lean_inc(v___y_777_);
lean_inc(v___y_775_);
v___x_798_ = lean_apply_4(v_x_774_, v___y_775_, v___x_797_, v___y_777_, lean_box(0));
v___y_780_ = v___x_798_;
goto v___jp_779_;
}
v___jp_806_:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_nat_dec_eq(v_maxRecDepth_804_, v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_eq(v_currRecDepth_800_, v_maxRecDepth_804_);
if (v___x_809_ == 0)
{
lean_inc(v_ref_801_);
v___y_790_ = v_currRecDepth_800_;
v___y_791_ = v_diag_802_;
v___y_792_ = v_toCold_799_;
v___y_793_ = v_suppressElabErrors_803_;
v___y_794_ = v_ref_801_;
goto v___jp_789_;
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v_x_774_);
lean_inc(v_ref_801_);
v___x_810_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_801_);
v___y_780_ = v___x_810_;
goto v___jp_779_;
}
}
else
{
lean_inc(v_ref_801_);
v___y_790_ = v_currRecDepth_800_;
v___y_791_ = v_diag_802_;
v___y_792_ = v_toCold_799_;
v___y_793_ = v_suppressElabErrors_803_;
v___y_794_ = v_ref_801_;
goto v___jp_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_828_, lean_object* v_x_829_){
_start:
{
if (lean_obj_tag(v_x_829_) == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
return v___x_830_;
}
else
{
lean_object* v_key_831_; lean_object* v_value_832_; lean_object* v_tail_833_; uint8_t v___x_834_; 
v_key_831_ = lean_ctor_get(v_x_829_, 0);
v_value_832_ = lean_ctor_get(v_x_829_, 1);
v_tail_833_ = lean_ctor_get(v_x_829_, 2);
v___x_834_ = l_Lean_ExprStructEq_beq(v_key_831_, v_a_828_);
if (v___x_834_ == 0)
{
v_x_829_ = v_tail_833_;
goto _start;
}
else
{
lean_object* v___x_836_; 
lean_inc(v_value_832_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v_value_832_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_837_, v_x_838_);
lean_dec(v_x_838_);
lean_dec_ref(v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_buckets_842_; lean_object* v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v_fold_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_buckets_842_ = lean_ctor_get(v_m_840_, 1);
v___x_843_ = lean_array_get_size(v_buckets_842_);
v___x_844_ = l_Lean_ExprStructEq_hash(v_a_841_);
v___x_845_ = 32ULL;
v___x_846_ = lean_uint64_shift_right(v___x_844_, v___x_845_);
v_fold_847_ = lean_uint64_xor(v___x_844_, v___x_846_);
v___x_848_ = 16ULL;
v___x_849_ = lean_uint64_shift_right(v_fold_847_, v___x_848_);
v___x_850_ = lean_uint64_xor(v_fold_847_, v___x_849_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = lean_usize_of_nat(v___x_843_);
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_sub(v___x_852_, v___x_853_);
v___x_855_ = lean_usize_land(v___x_851_, v___x_854_);
v___x_856_ = lean_array_uget_borrowed(v_buckets_842_, v___x_855_);
v___x_857_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_841_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_858_, v_a_859_);
lean_dec_ref(v_a_859_);
lean_dec_ref(v_m_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_dec(v_b_862_);
lean_dec_ref(v_a_861_);
return v_x_863_;
}
else
{
lean_object* v_key_864_; lean_object* v_value_865_; lean_object* v_tail_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_878_; 
v_key_864_ = lean_ctor_get(v_x_863_, 0);
v_value_865_ = lean_ctor_get(v_x_863_, 1);
v_tail_866_ = lean_ctor_get(v_x_863_, 2);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_878_ == 0)
{
v___x_868_ = v_x_863_;
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_tail_866_);
lean_inc(v_value_865_);
lean_inc(v_key_864_);
lean_dec(v_x_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
uint8_t v___x_870_; 
v___x_870_ = l_Lean_ExprStructEq_beq(v_key_864_, v_a_861_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_861_, v_b_862_, v_tail_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 2, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_key_864_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_value_865_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
else
{
lean_object* v___x_876_; 
lean_dec(v_value_865_);
lean_dec(v_key_864_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_b_862_);
lean_ctor_set(v___x_868_, 0, v_a_861_);
v___x_876_ = v___x_868_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_861_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_b_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_tail_866_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
return v_x_879_;
}
else
{
lean_object* v_key_881_; lean_object* v_value_882_; lean_object* v_tail_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_906_; 
v_key_881_ = lean_ctor_get(v_x_880_, 0);
v_value_882_ = lean_ctor_get(v_x_880_, 1);
v_tail_883_ = lean_ctor_get(v_x_880_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_x_880_);
if (v_isSharedCheck_906_ == 0)
{
v___x_885_ = v_x_880_;
v_isShared_886_ = v_isSharedCheck_906_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_tail_883_);
lean_inc(v_value_882_);
lean_inc(v_key_881_);
lean_dec(v_x_880_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_906_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v_fold_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_887_ = lean_array_get_size(v_x_879_);
v___x_888_ = l_Lean_ExprStructEq_hash(v_key_881_);
v___x_889_ = 32ULL;
v___x_890_ = lean_uint64_shift_right(v___x_888_, v___x_889_);
v_fold_891_ = lean_uint64_xor(v___x_888_, v___x_890_);
v___x_892_ = 16ULL;
v___x_893_ = lean_uint64_shift_right(v_fold_891_, v___x_892_);
v___x_894_ = lean_uint64_xor(v_fold_891_, v___x_893_);
v___x_895_ = lean_uint64_to_usize(v___x_894_);
v___x_896_ = lean_usize_of_nat(v___x_887_);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_sub(v___x_896_, v___x_897_);
v___x_899_ = lean_usize_land(v___x_895_, v___x_898_);
v___x_900_ = lean_array_uget_borrowed(v_x_879_, v___x_899_);
lean_inc(v___x_900_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 2, v___x_900_);
v___x_902_ = v___x_885_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_key_881_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_value_882_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v___x_900_);
v___x_902_ = v_reuseFailAlloc_905_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = lean_array_uset(v_x_879_, v___x_899_, v___x_902_);
v_x_879_ = v___x_903_;
v_x_880_ = v_tail_883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_907_, lean_object* v_source_908_, lean_object* v_target_909_){
_start:
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_array_get_size(v_source_908_);
v___x_911_ = lean_nat_dec_lt(v_i_907_, v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v_source_908_);
lean_dec(v_i_907_);
return v_target_909_;
}
else
{
lean_object* v_es_912_; lean_object* v___x_913_; lean_object* v_source_914_; lean_object* v_target_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_es_912_ = lean_array_fget(v_source_908_, v_i_907_);
v___x_913_ = lean_box(0);
v_source_914_ = lean_array_fset(v_source_908_, v_i_907_, v___x_913_);
v_target_915_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_909_, v_es_912_);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_add(v_i_907_, v___x_916_);
lean_dec(v_i_907_);
v_i_907_ = v___x_917_;
v_source_908_ = v_source_914_;
v_target_909_ = v_target_915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_nbuckets_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_920_ = lean_array_get_size(v_data_919_);
v___x_921_ = lean_unsigned_to_nat(2u);
v_nbuckets_922_ = lean_nat_mul(v___x_920_, v___x_921_);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_box(0);
v___x_925_ = lean_mk_array(v_nbuckets_922_, v___x_924_);
v___x_926_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_923_, v_data_919_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_927_, lean_object* v_x_928_){
_start:
{
if (lean_obj_tag(v_x_928_) == 0)
{
uint8_t v___x_929_; 
v___x_929_ = 0;
return v___x_929_;
}
else
{
lean_object* v_key_930_; lean_object* v_tail_931_; uint8_t v___x_932_; 
v_key_930_ = lean_ctor_get(v_x_928_, 0);
v_tail_931_ = lean_ctor_get(v_x_928_, 2);
v___x_932_ = l_Lean_ExprStructEq_beq(v_key_930_, v_a_927_);
if (v___x_932_ == 0)
{
v_x_928_ = v_tail_931_;
goto _start;
}
else
{
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_934_, lean_object* v_x_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_934_, v_x_935_);
lean_dec(v_x_935_);
lean_dec_ref(v_a_934_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_938_, lean_object* v_a_939_, lean_object* v_b_940_){
_start:
{
lean_object* v_size_941_; lean_object* v_buckets_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_985_; 
v_size_941_ = lean_ctor_get(v_m_938_, 0);
v_buckets_942_ = lean_ctor_get(v_m_938_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_m_938_);
if (v_isSharedCheck_985_ == 0)
{
v___x_944_ = v_m_938_;
v_isShared_945_ = v_isSharedCheck_985_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_buckets_942_);
lean_inc(v_size_941_);
lean_dec(v_m_938_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_985_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; uint64_t v___x_947_; uint64_t v___x_948_; uint64_t v___x_949_; uint64_t v_fold_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v_bkt_959_; uint8_t v___x_960_; 
v___x_946_ = lean_array_get_size(v_buckets_942_);
v___x_947_ = l_Lean_ExprStructEq_hash(v_a_939_);
v___x_948_ = 32ULL;
v___x_949_ = lean_uint64_shift_right(v___x_947_, v___x_948_);
v_fold_950_ = lean_uint64_xor(v___x_947_, v___x_949_);
v___x_951_ = 16ULL;
v___x_952_ = lean_uint64_shift_right(v_fold_950_, v___x_951_);
v___x_953_ = lean_uint64_xor(v_fold_950_, v___x_952_);
v___x_954_ = lean_uint64_to_usize(v___x_953_);
v___x_955_ = lean_usize_of_nat(v___x_946_);
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_sub(v___x_955_, v___x_956_);
v___x_958_ = lean_usize_land(v___x_954_, v___x_957_);
v_bkt_959_ = lean_array_uget_borrowed(v_buckets_942_, v___x_958_);
v___x_960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_939_, v_bkt_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v_size_x27_962_; lean_object* v___x_963_; lean_object* v_buckets_x27_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_961_ = lean_unsigned_to_nat(1u);
v_size_x27_962_ = lean_nat_add(v_size_941_, v___x_961_);
lean_dec(v_size_941_);
lean_inc(v_bkt_959_);
v___x_963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_963_, 0, v_a_939_);
lean_ctor_set(v___x_963_, 1, v_b_940_);
lean_ctor_set(v___x_963_, 2, v_bkt_959_);
v_buckets_x27_964_ = lean_array_uset(v_buckets_942_, v___x_958_, v___x_963_);
v___x_965_ = lean_unsigned_to_nat(4u);
v___x_966_ = lean_nat_mul(v_size_x27_962_, v___x_965_);
v___x_967_ = lean_unsigned_to_nat(3u);
v___x_968_ = lean_nat_div(v___x_966_, v___x_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_array_get_size(v_buckets_x27_964_);
v___x_970_ = lean_nat_dec_le(v___x_968_, v___x_969_);
lean_dec(v___x_968_);
if (v___x_970_ == 0)
{
lean_object* v_val_971_; lean_object* v___x_973_; 
v_val_971_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_964_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_val_971_);
lean_ctor_set(v___x_944_, 0, v_size_x27_962_);
v___x_973_ = v___x_944_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_size_x27_962_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_val_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v___x_976_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_buckets_x27_964_);
lean_ctor_set(v___x_944_, 0, v_size_x27_962_);
v___x_976_ = v___x_944_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_size_x27_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_buckets_x27_964_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
lean_object* v___x_978_; lean_object* v_buckets_x27_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
lean_inc(v_bkt_959_);
v___x_978_ = lean_box(0);
v_buckets_x27_979_ = lean_array_uset(v_buckets_942_, v___x_958_, v___x_978_);
v___x_980_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_939_, v_b_940_, v_bkt_959_);
v___x_981_ = lean_array_uset(v_buckets_x27_979_, v___x_958_, v___x_980_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_981_);
v___x_983_ = v___x_944_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_size_941_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_986_, lean_object* v_e_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_st_ref_take(v_a_986_);
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_990_, v_e_987_, v_a_988_);
v___x_992_ = lean_st_ref_put(v_a_986_, v___x_991_);
v___x_993_ = lean_box(0);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_994_, lean_object* v_e_995_, lean_object* v_a_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_994_, v_e_995_, v_a_996_);
lean_dec(v_a_994_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_apply_1(v_x_1000_, lean_box(0));
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1006_, v_x_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1011_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1013_; lean_object* v_dummy_1014_; 
v___x_1013_ = lean_box(0);
v_dummy_1014_ = l_Lean_Expr_sort___override(v___x_1013_);
return v_dummy_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1015_, lean_object* v_post_1016_, size_t v_sz_1017_, size_t v_i_1018_, lean_object* v_bs_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_usize_dec_lt(v_i_1018_, v_sz_1017_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref(v_post_1016_);
lean_dec_ref(v_pre_1015_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_bs_1019_);
return v___x_1025_;
}
else
{
lean_object* v_v_1026_; lean_object* v___x_1027_; 
v_v_1026_ = lean_array_uget_borrowed(v_bs_1019_, v_i_1018_);
lean_inc(v_v_1026_);
lean_inc_ref(v_post_1016_);
lean_inc_ref(v_pre_1015_);
v___x_1027_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1015_, v_post_1016_, v_v_1026_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v_bs_x27_1030_; size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = lean_unsigned_to_nat(0u);
v_bs_x27_1030_ = lean_array_uset(v_bs_1019_, v_i_1018_, v___x_1029_);
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_add(v_i_1018_, v___x_1031_);
v___x_1033_ = lean_array_uset(v_bs_x27_1030_, v_i_1018_, v_a_1028_);
v_i_1018_ = v___x_1032_;
v_bs_1019_ = v___x_1033_;
goto _start;
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_bs_1019_);
lean_dec_ref(v_post_1016_);
lean_dec_ref(v_pre_1015_);
v_a_1035_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1027_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1027_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1043_, lean_object* v_post_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
if (lean_obj_tag(v_x_1045_) == 5)
{
lean_object* v_fn_1052_; lean_object* v_arg_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_fn_1052_ = lean_ctor_get(v_x_1045_, 0);
lean_inc_ref(v_fn_1052_);
v_arg_1053_ = lean_ctor_get(v_x_1045_, 1);
lean_inc_ref(v_arg_1053_);
lean_dec_ref_known(v_x_1045_, 2);
v___x_1054_ = lean_array_set(v_x_1046_, v_x_1047_, v_arg_1053_);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_sub(v_x_1047_, v___x_1055_);
lean_dec(v_x_1047_);
v_x_1045_ = v_fn_1052_;
v_x_1046_ = v___x_1054_;
v_x_1047_ = v___x_1056_;
goto _start;
}
else
{
lean_object* v___x_1058_; 
lean_dec(v_x_1047_);
lean_inc_ref(v_post_1044_);
lean_inc_ref(v_pre_1043_);
v___x_1058_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1043_, v_post_1044_, v_x_1045_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v_sz_1060_ = lean_array_size(v_x_1046_);
v___x_1061_ = ((size_t)0ULL);
lean_inc_ref(v_post_1044_);
lean_inc_ref(v_pre_1043_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1043_, v_post_1044_, v_sz_1060_, v___x_1061_, v_x_1046_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = l_Lean_mkAppN(v_a_1059_, v_a_1063_);
lean_dec(v_a_1063_);
v___x_1065_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1043_, v_post_1044_, v___x_1064_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1065_;
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_a_1059_);
lean_dec_ref(v_post_1044_);
lean_dec_ref(v_pre_1043_);
v_a_1066_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1062_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1062_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_dec_ref(v_x_1046_);
lean_dec_ref(v_post_1044_);
lean_dec_ref(v_pre_1043_);
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1074_, lean_object* v_pre_1075_, lean_object* v_e_1076_, lean_object* v_post_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Core_checkSystem(v___x_1074_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; 
lean_dec_ref_known(v___x_1082_, 1);
lean_inc_ref(v_pre_1075_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc_ref(v_e_1076_);
v___x_1083_ = lean_apply_4(v_pre_1075_, v_e_1076_, v___y_1079_, v___y_1080_, lean_box(0));
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1199_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1199_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1199_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___y_1089_; 
switch(lean_obj_tag(v_a_1084_))
{
case 0:
{
lean_object* v_e_1189_; lean_object* v___x_1191_; 
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_e_1076_);
lean_dec_ref(v_pre_1075_);
v_e_1189_ = lean_ctor_get(v_a_1084_, 0);
lean_inc_ref(v_e_1189_);
lean_dec_ref_known(v_a_1084_, 1);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v_e_1189_);
v___x_1191_ = v___x_1086_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_e_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
case 1:
{
lean_object* v_e_1193_; lean_object* v___x_1194_; 
lean_del_object(v___x_1086_);
lean_dec_ref(v_e_1076_);
v_e_1193_ = lean_ctor_get(v_a_1084_, 0);
lean_inc_ref(v_e_1193_);
lean_dec_ref_known(v_a_1084_, 1);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1194_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_e_1193_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v_a_1195_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1196_;
}
else
{
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1194_;
}
}
default: 
{
lean_object* v_e_x3f_1197_; 
lean_del_object(v___x_1086_);
v_e_x3f_1197_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_e_x3f_1197_);
lean_dec_ref_known(v_a_1084_, 1);
if (lean_obj_tag(v_e_x3f_1197_) == 0)
{
v___y_1089_ = v_e_1076_;
goto v___jp_1088_;
}
else
{
lean_object* v_val_1198_; 
lean_dec_ref(v_e_1076_);
v_val_1198_ = lean_ctor_get(v_e_x3f_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_e_x3f_1197_, 1);
v___y_1089_ = v_val_1198_;
goto v___jp_1088_;
}
}
}
v___jp_1088_:
{
switch(lean_obj_tag(v___y_1089_))
{
case 7:
{
lean_object* v_binderName_1090_; lean_object* v_binderType_1091_; lean_object* v_body_1092_; uint8_t v_binderInfo_1093_; lean_object* v___x_1094_; 
v_binderName_1090_ = lean_ctor_get(v___y_1089_, 0);
v_binderType_1091_ = lean_ctor_get(v___y_1089_, 1);
v_body_1092_ = lean_ctor_get(v___y_1089_, 2);
v_binderInfo_1093_ = lean_ctor_get_uint8(v___y_1089_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1091_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1094_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_binderType_1091_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
lean_inc_ref(v_body_1092_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1096_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_body_1092_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; size_t v___x_1098_; size_t v___x_1099_; uint8_t v___x_1100_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_ptr_addr(v_binderType_1091_);
v___x_1099_ = lean_ptr_addr(v_a_1095_);
v___x_1100_ = lean_usize_dec_eq(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_inc(v_binderName_1090_);
lean_dec_ref_known(v___y_1089_, 3);
v___x_1101_ = l_Lean_Expr_forallE___override(v_binderName_1090_, v_a_1095_, v_a_1097_, v_binderInfo_1093_);
v___x_1102_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1101_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1102_;
}
else
{
size_t v___x_1103_; size_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = lean_ptr_addr(v_body_1092_);
v___x_1104_ = lean_ptr_addr(v_a_1097_);
v___x_1105_ = lean_usize_dec_eq(v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc(v_binderName_1090_);
lean_dec_ref_known(v___y_1089_, 3);
v___x_1106_ = l_Lean_Expr_forallE___override(v_binderName_1090_, v_a_1095_, v_a_1097_, v_binderInfo_1093_);
v___x_1107_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1106_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1107_;
}
else
{
uint8_t v___x_1108_; 
v___x_1108_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1093_, v_binderInfo_1093_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_inc(v_binderName_1090_);
lean_dec_ref_known(v___y_1089_, 3);
v___x_1109_ = l_Lean_Expr_forallE___override(v_binderName_1090_, v_a_1095_, v_a_1097_, v_binderInfo_1093_);
v___x_1110_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1109_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; 
lean_dec(v_a_1097_);
lean_dec(v_a_1095_);
v___x_1111_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___y_1089_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1111_;
}
}
}
}
else
{
lean_dec(v_a_1095_);
lean_dec_ref_known(v___y_1089_, 3);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1096_;
}
}
else
{
lean_dec_ref_known(v___y_1089_, 3);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1094_;
}
}
case 6:
{
lean_object* v_binderName_1112_; lean_object* v_binderType_1113_; lean_object* v_body_1114_; uint8_t v_binderInfo_1115_; lean_object* v___x_1116_; 
v_binderName_1112_ = lean_ctor_get(v___y_1089_, 0);
v_binderType_1113_ = lean_ctor_get(v___y_1089_, 1);
v_body_1114_ = lean_ctor_get(v___y_1089_, 2);
v_binderInfo_1115_ = lean_ctor_get_uint8(v___y_1089_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1113_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_binderType_1113_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
lean_inc_ref(v_body_1114_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1118_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_body_1114_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; size_t v___x_1120_; size_t v___x_1121_; uint8_t v___x_1122_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = lean_ptr_addr(v_binderType_1113_);
v___x_1121_ = lean_ptr_addr(v_a_1117_);
v___x_1122_ = lean_usize_dec_eq(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_inc(v_binderName_1112_);
lean_dec_ref_known(v___y_1089_, 3);
v___x_1123_ = l_Lean_Expr_lam___override(v_binderName_1112_, v_a_1117_, v_a_1119_, v_binderInfo_1115_);
v___x_1124_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1123_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1124_;
}
else
{
size_t v___x_1125_; size_t v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_ptr_addr(v_body_1114_);
v___x_1126_ = lean_ptr_addr(v_a_1119_);
v___x_1127_ = lean_usize_dec_eq(v___x_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_inc(v_binderName_1112_);
lean_dec_ref_known(v___y_1089_, 3);
v___x_1128_ = l_Lean_Expr_lam___override(v_binderName_1112_, v_a_1117_, v_a_1119_, v_binderInfo_1115_);
v___x_1129_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1128_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1129_;
}
else
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1115_, v_binderInfo_1115_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_inc(v_binderName_1112_);
lean_dec_ref_known(v___y_1089_, 3);
v___x_1131_ = l_Lean_Expr_lam___override(v_binderName_1112_, v_a_1117_, v_a_1119_, v_binderInfo_1115_);
v___x_1132_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1131_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; 
lean_dec(v_a_1119_);
lean_dec(v_a_1117_);
v___x_1133_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___y_1089_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1133_;
}
}
}
}
else
{
lean_dec(v_a_1117_);
lean_dec_ref_known(v___y_1089_, 3);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1118_;
}
}
else
{
lean_dec_ref_known(v___y_1089_, 3);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1116_;
}
}
case 8:
{
lean_object* v_declName_1134_; lean_object* v_type_1135_; lean_object* v_value_1136_; lean_object* v_body_1137_; uint8_t v_nondep_1138_; lean_object* v___x_1139_; 
v_declName_1134_ = lean_ctor_get(v___y_1089_, 0);
v_type_1135_ = lean_ctor_get(v___y_1089_, 1);
v_value_1136_ = lean_ctor_get(v___y_1089_, 2);
v_body_1137_ = lean_ctor_get(v___y_1089_, 3);
v_nondep_1138_ = lean_ctor_get_uint8(v___y_1089_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1135_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1139_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_type_1135_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
lean_inc_ref(v_value_1136_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1141_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_value_1136_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
lean_inc_ref(v_body_1137_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1143_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_body_1137_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; size_t v___x_1145_; size_t v___x_1146_; uint8_t v___x_1147_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = lean_ptr_addr(v_type_1135_);
v___x_1146_ = lean_ptr_addr(v_a_1140_);
v___x_1147_ = lean_usize_dec_eq(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_inc(v_declName_1134_);
lean_dec_ref_known(v___y_1089_, 4);
v___x_1148_ = l_Lean_Expr_letE___override(v_declName_1134_, v_a_1140_, v_a_1142_, v_a_1144_, v_nondep_1138_);
v___x_1149_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1148_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1149_;
}
else
{
size_t v___x_1150_; size_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_ptr_addr(v_value_1136_);
v___x_1151_ = lean_ptr_addr(v_a_1142_);
v___x_1152_ = lean_usize_dec_eq(v___x_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_inc(v_declName_1134_);
lean_dec_ref_known(v___y_1089_, 4);
v___x_1153_ = l_Lean_Expr_letE___override(v_declName_1134_, v_a_1140_, v_a_1142_, v_a_1144_, v_nondep_1138_);
v___x_1154_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1153_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1154_;
}
else
{
size_t v___x_1155_; size_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_ptr_addr(v_body_1137_);
v___x_1156_ = lean_ptr_addr(v_a_1144_);
v___x_1157_ = lean_usize_dec_eq(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc(v_declName_1134_);
lean_dec_ref_known(v___y_1089_, 4);
v___x_1158_ = l_Lean_Expr_letE___override(v_declName_1134_, v_a_1140_, v_a_1142_, v_a_1144_, v_nondep_1138_);
v___x_1159_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1158_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; 
lean_dec(v_a_1144_);
lean_dec(v_a_1142_);
lean_dec(v_a_1140_);
v___x_1160_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___y_1089_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1160_;
}
}
}
}
else
{
lean_dec(v_a_1142_);
lean_dec(v_a_1140_);
lean_dec_ref_known(v___y_1089_, 4);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1143_;
}
}
else
{
lean_dec(v_a_1140_);
lean_dec_ref_known(v___y_1089_, 4);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1141_;
}
}
else
{
lean_dec_ref_known(v___y_1089_, 4);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1139_;
}
}
case 5:
{
lean_object* v_dummy_1161_; lean_object* v_nargs_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_dummy_1161_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1162_ = l_Lean_Expr_getAppNumArgs(v___y_1089_);
lean_inc(v_nargs_1162_);
v___x_1163_ = lean_mk_array(v_nargs_1162_, v_dummy_1161_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v_nargs_1162_, v___x_1164_);
lean_dec(v_nargs_1162_);
v___x_1166_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1075_, v_post_1077_, v___y_1089_, v___x_1163_, v___x_1165_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1166_;
}
case 10:
{
lean_object* v_data_1167_; lean_object* v_expr_1168_; lean_object* v___x_1169_; 
v_data_1167_ = lean_ctor_get(v___y_1089_, 0);
v_expr_1168_ = lean_ctor_get(v___y_1089_, 1);
lean_inc_ref(v_expr_1168_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1169_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_expr_1168_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; size_t v___x_1171_; size_t v___x_1172_; uint8_t v___x_1173_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = lean_ptr_addr(v_expr_1168_);
v___x_1172_ = lean_ptr_addr(v_a_1170_);
v___x_1173_ = lean_usize_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_inc(v_data_1167_);
lean_dec_ref_known(v___y_1089_, 2);
v___x_1174_ = l_Lean_Expr_mdata___override(v_data_1167_, v_a_1170_);
v___x_1175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1174_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; 
lean_dec(v_a_1170_);
v___x_1176_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___y_1089_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1176_;
}
}
else
{
lean_dec_ref_known(v___y_1089_, 2);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1169_;
}
}
case 11:
{
lean_object* v_typeName_1177_; lean_object* v_idx_1178_; lean_object* v_struct_1179_; lean_object* v___x_1180_; 
v_typeName_1177_ = lean_ctor_get(v___y_1089_, 0);
v_idx_1178_ = lean_ctor_get(v___y_1089_, 1);
v_struct_1179_ = lean_ctor_get(v___y_1089_, 2);
lean_inc_ref(v_struct_1179_);
lean_inc_ref(v_post_1077_);
lean_inc_ref(v_pre_1075_);
v___x_1180_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1075_, v_post_1077_, v_struct_1179_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; size_t v___x_1182_; size_t v___x_1183_; uint8_t v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = lean_ptr_addr(v_struct_1179_);
v___x_1183_ = lean_ptr_addr(v_a_1181_);
v___x_1184_ = lean_usize_dec_eq(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_inc(v_idx_1178_);
lean_inc(v_typeName_1177_);
lean_dec_ref_known(v___y_1089_, 3);
v___x_1185_ = l_Lean_Expr_proj___override(v_typeName_1177_, v_idx_1178_, v_a_1181_);
v___x_1186_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___x_1185_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
lean_dec(v_a_1181_);
v___x_1187_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___y_1089_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1187_;
}
}
else
{
lean_dec_ref_known(v___y_1089_, 3);
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_pre_1075_);
return v___x_1180_;
}
}
default: 
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1075_, v_post_1077_, v___y_1089_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_e_1076_);
lean_dec_ref(v_pre_1075_);
v_a_1200_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1083_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1083_);
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
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v_post_1077_);
lean_dec_ref(v_e_1076_);
lean_dec_ref(v_pre_1075_);
v_a_1208_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1082_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1082_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1216_, lean_object* v_pre_1217_, lean_object* v_e_1218_, lean_object* v_post_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1216_, v_pre_1217_, v_e_1218_, v_post_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1225_, lean_object* v_post_1226_, lean_object* v_e_1227_, lean_object* v_a_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_inc(v_a_1228_);
v___x_1232_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1232_, 0, lean_box(0));
lean_closure_set(v___x_1232_, 1, lean_box(0));
lean_closure_set(v___x_1232_, 2, v_a_1228_);
v___x_1233_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1232_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1265_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1265_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1265_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1234_, v_e_1227_);
lean_dec(v_a_1234_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; 
lean_del_object(v___x_1236_);
v___x_1239_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1227_);
v___f_1240_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1240_, 0, v___x_1239_);
lean_closure_set(v___f_1240_, 1, v_pre_1225_);
lean_closure_set(v___f_1240_, 2, v_e_1227_);
lean_closure_set(v___f_1240_, 3, v_post_1226_);
v___x_1241_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1240_, v_a_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___f_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_n(v_a_1242_, 2);
lean_dec_ref_known(v___x_1241_, 1);
lean_inc(v_a_1228_);
v___f_1243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1243_, 0, v_a_1228_);
lean_closure_set(v___f_1243_, 1, v_e_1227_);
lean_closure_set(v___f_1243_, 2, v_a_1242_);
v___x_1244_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1243_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1252_);
v___x_1246_ = v___x_1244_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v___x_1244_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v_a_1242_);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1242_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_a_1242_);
v_a_1253_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1244_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1244_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_dec_ref(v_e_1227_);
return v___x_1241_;
}
}
else
{
lean_object* v_val_1261_; lean_object* v___x_1263_; 
lean_dec_ref(v_e_1227_);
lean_dec_ref(v_post_1226_);
lean_dec_ref(v_pre_1225_);
v_val_1261_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v___x_1238_, 1);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_val_1261_);
v___x_1263_ = v___x_1236_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_val_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_e_1227_);
lean_dec_ref(v_post_1226_);
lean_dec_ref(v_pre_1225_);
v_a_1266_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1233_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1233_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1274_, lean_object* v_post_1275_, lean_object* v_e_1276_, lean_object* v_a_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
lean_inc_ref(v_post_1275_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc_ref(v_e_1276_);
v___x_1281_ = lean_apply_4(v_post_1275_, v_e_1276_, v___y_1278_, v___y_1279_, lean_box(0));
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1300_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1300_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1300_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
switch(lean_obj_tag(v_a_1282_))
{
case 0:
{
lean_object* v_e_1286_; lean_object* v___x_1288_; 
lean_dec_ref(v_e_1276_);
lean_dec_ref(v_post_1275_);
lean_dec_ref(v_pre_1274_);
v_e_1286_ = lean_ctor_get(v_a_1282_, 0);
lean_inc_ref(v_e_1286_);
lean_dec_ref_known(v_a_1282_, 1);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_e_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_e_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
case 1:
{
lean_object* v_e_1290_; lean_object* v___x_1291_; 
lean_del_object(v___x_1284_);
lean_dec_ref(v_e_1276_);
v_e_1290_ = lean_ctor_get(v_a_1282_, 0);
lean_inc_ref(v_e_1290_);
lean_dec_ref_known(v_a_1282_, 1);
v___x_1291_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1274_, v_post_1275_, v_e_1290_, v_a_1277_, v___y_1278_, v___y_1279_);
return v___x_1291_;
}
default: 
{
lean_object* v_e_x3f_1292_; 
lean_dec_ref(v_post_1275_);
lean_dec_ref(v_pre_1274_);
v_e_x3f_1292_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_e_x3f_1292_);
lean_dec_ref_known(v_a_1282_, 1);
if (lean_obj_tag(v_e_x3f_1292_) == 0)
{
lean_object* v___x_1294_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_e_1276_);
v___x_1294_ = v___x_1284_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_e_1276_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
else
{
lean_object* v_val_1296_; lean_object* v___x_1298_; 
lean_dec_ref(v_e_1276_);
v_val_1296_ = lean_ctor_get(v_e_x3f_1292_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v_e_x3f_1292_, 1);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_val_1296_);
v___x_1298_ = v___x_1284_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_val_1296_);
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
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v_e_1276_);
lean_dec_ref(v_post_1275_);
lean_dec_ref(v_pre_1274_);
v_a_1301_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1281_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1281_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1309_, lean_object* v_post_1310_, lean_object* v_e_1311_, lean_object* v_a_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1309_, v_post_1310_, v_e_1311_, v_a_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v_a_1312_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1317_, lean_object* v_post_1318_, lean_object* v_sz_1319_, lean_object* v_i_1320_, lean_object* v_bs_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1319_);
lean_dec(v_sz_1319_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1317_, v_post_1318_, v_sz_boxed_1326_, v_i_boxed_1327_, v_bs_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1329_, lean_object* v_post_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1329_, v_post_1330_, v_x_1331_, v_x_1332_, v_x_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1339_, lean_object* v_post_1340_, lean_object* v_e_1341_, lean_object* v_a_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1339_, v_post_1340_, v_e_1341_, v_a_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v_a_1342_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1347_, lean_object* v_x_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_apply_1(v_x_1348_, lean_box(0));
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_x_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1354_, v_x_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1359_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_unsigned_to_nat(16u);
v___x_1362_ = lean_mk_array(v___x_1361_, v___x_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___x_1363_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1367_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1367_, 0, lean_box(0));
lean_closure_set(v___x_1367_, 1, lean_box(0));
lean_closure_set(v___x_1367_, 2, v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1368_, lean_object* v_pre_1369_, lean_object* v_post_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_a_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1375_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1374_, v___y_1371_, v___y_1372_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1369_, v_post_1370_, v_input_1368_, v_a_1376_, v___y_1371_, v___y_1372_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1379_, 0, lean_box(0));
lean_closure_set(v___x_1379_, 1, lean_box(0));
lean_closure_set(v___x_1379_, 2, v_a_1376_);
v___x_1380_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1379_, v___y_1371_, v___y_1372_);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v___x_1380_, 0);
lean_dec(v_unused_1388_);
v___x_1382_ = v___x_1380_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v___x_1380_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v_a_1378_);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1378_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
else
{
lean_dec(v_a_1376_);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1389_, lean_object* v_pre_1390_, lean_object* v_post_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1389_, v_pre_1390_, v_post_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___f_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; 
v___f_1402_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1403_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1404_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1398_, v___f_1402_, v___f_1403_, v_a_1399_, v_a_1400_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1410_, lean_object* v_m_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1411_, v_a_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1414_, lean_object* v_m_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1414_, v_m_1415_, v_a_1416_);
lean_dec_ref(v_a_1416_);
lean_dec_ref(v_m_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1418_, lean_object* v_ref_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1424_, lean_object* v_ref_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1424_, v_ref_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1447_, v_x_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1454_, lean_object* v_m_1455_, lean_object* v_a_1456_, lean_object* v_b_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1455_, v_a_1456_, v_b_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1459_, lean_object* v_a_1460_, lean_object* v_x_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1460_, v_x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1463_, lean_object* v_a_1464_, lean_object* v_x_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1463_, v_a_1464_, v_x_1465_);
lean_dec(v_x_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1467_, lean_object* v_a_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1468_, v_x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1471_, lean_object* v_a_1472_, lean_object* v_x_1473_){
_start:
{
uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_res_1474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1471_, v_a_1472_, v_x_1473_);
lean_dec(v_x_1473_);
lean_dec_ref(v_a_1472_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1476_, lean_object* v_data_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1479_, lean_object* v_a_1480_, lean_object* v_b_1481_, lean_object* v_x_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1480_, v_b_1481_, v_x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1484_, lean_object* v_i_1485_, lean_object* v_source_1486_, lean_object* v_target_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1485_, v_source_1486_, v_target_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1490_, v_x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1496_; lean_object* v_env_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1496_ = lean_st_ref_get(v___y_1494_);
v_env_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc_ref(v_env_1497_);
lean_dec(v___x_1496_);
v___x_1498_ = l_Lean_isRecCore(v_env_1497_, v_declName_1493_);
v___x_1499_ = lean_box(v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1501_, v___y_1502_);
lean_dec(v___y_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1505_, v___y_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v_env_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1522_ = lean_st_ref_get(v___y_1520_);
v_env_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc_ref(v_env_1523_);
lean_dec(v___x_1522_);
v___x_1524_ = l_Lean_getReducibilityStatusCore(v_env_1523_, v_declName_1519_);
v___x_1525_ = lean_box(v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1527_, v___y_1528_);
lean_dec(v___y_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1553_; 
v___x_1537_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1531_, v___y_1535_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1553_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1553_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_unbox(v_a_1538_);
lean_dec(v_a_1538_);
if (v___x_1542_ == 0)
{
uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1543_ = 1;
v___x_1544_ = lean_box(v___x_1543_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1544_);
v___x_1546_ = v___x_1540_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1548_ = 0;
v___x_1549_ = lean_box(v___x_1548_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1549_);
v___x_1551_ = v___x_1540_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1561_, lean_object* v_b_1562_){
_start:
{
lean_object* v_array_1564_; lean_object* v_start_1565_; lean_object* v_stop_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1583_; 
v_array_1564_ = lean_ctor_get(v_a_1561_, 0);
v_start_1565_ = lean_ctor_get(v_a_1561_, 1);
v_stop_1566_ = lean_ctor_get(v_a_1561_, 2);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_a_1561_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1568_ = v_a_1561_;
v_isShared_1569_ = v_isSharedCheck_1583_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_stop_1566_);
lean_inc(v_start_1565_);
lean_inc(v_array_1564_);
lean_dec(v_a_1561_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1583_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_nat_dec_lt(v_start_1565_, v_stop_1566_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_del_object(v___x_1568_);
lean_dec(v_stop_1566_);
lean_dec(v_start_1565_);
lean_dec_ref(v_array_1564_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_b_1562_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = lean_nat_add(v_start_1565_, v___x_1573_);
lean_inc_ref(v_array_1564_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1574_);
v___x_1576_ = v___x_1568_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_array_1564_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_stop_1566_);
v___x_1576_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_array_fget(v_array_1564_, v_start_1565_);
lean_dec(v_start_1565_);
lean_dec_ref(v_array_1564_);
v___x_1578_ = l_Lean_Expr_hasExprMVar(v___x_1577_);
lean_dec(v___x_1577_);
if (v___x_1578_ == 0)
{
v_a_1561_ = v___x_1576_;
v_b_1562_ = v___x_1572_;
goto _start;
}
else
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_dec_ref_known(v___x_1580_, 1);
v_a_1561_ = v___x_1576_;
v_b_1562_ = v___x_1572_;
goto _start;
}
else
{
lean_dec_ref(v___x_1576_);
return v___x_1580_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1584_, v_b_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1596_, uint8_t v_isMatch_1597_, uint8_t v_root_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___y_1605_; lean_object* v_b_1606_; lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1596_, v_root_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1780_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1780_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1780_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___y_1623_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; 
if (v_root_1598_ == 0)
{
lean_object* v___x_1768_; 
lean_inc(v_a_1618_);
v___x_1768_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1618_);
if (lean_obj_tag(v___x_1768_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1779_; 
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v_val_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1779_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_val_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1779_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 2);
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_val_1769_);
v___x_1774_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
}
else
{
lean_dec(v___x_1768_);
v___y_1633_ = v_a_1599_;
v___y_1634_ = v_a_1600_;
v___y_1635_ = v_a_1601_;
v___y_1636_ = v_a_1602_;
goto v___jp_1632_;
}
}
else
{
v___y_1633_ = v_a_1599_;
v___y_1634_ = v_a_1600_;
v___y_1635_ = v_a_1601_;
v___y_1636_ = v_a_1602_;
goto v___jp_1632_;
}
v___jp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1624_ = l_Lean_Expr_getAppNumArgs(v_a_1618_);
lean_inc(v___x_1624_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___y_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_mk_empty_array_with_capacity(v___x_1624_);
lean_dec(v___x_1624_);
v___x_1627_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1618_, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1625_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1628_);
v___x_1630_ = v___x_1620_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
v___jp_1632_:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Expr_getAppFn(v_a_1618_);
switch(lean_obj_tag(v___x_1637_))
{
case 1:
{
lean_object* v_fvarId_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1620_);
v_fvarId_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_fvarId_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = l_Lean_Expr_getAppNumArgs(v_a_1618_);
lean_inc(v___x_1639_);
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_fvarId_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_mk_empty_array_with_capacity(v___x_1639_);
lean_dec(v___x_1639_);
v___x_1642_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1618_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1640_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
case 2:
{
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
if (v_isMatch_1597_ == 0)
{
lean_object* v_mvarId_1645_; lean_object* v___x_1646_; uint8_t v_isDefEqStuckEx_1647_; 
v_mvarId_1645_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_mvarId_1645_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1646_ = l_Lean_Meta_Context_config(v___y_1633_);
v_isDefEqStuckEx_1647_ = lean_ctor_get_uint8(v___x_1646_, 4);
lean_dec_ref(v___x_1646_);
if (v_isDefEqStuckEx_1647_ == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1645_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1662_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1662_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1662_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1654_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1658_);
v___x_1660_ = v___x_1651_;
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
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1648_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1648_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v_mvarId_1645_);
v___x_1671_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref_known(v___x_1637_, 1);
v___x_1673_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
case 4:
{
lean_object* v_declName_1675_; lean_object* v___x_1676_; uint8_t v_isDefEqStuckEx_1677_; 
v_declName_1675_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_declName_1675_);
lean_dec_ref_known(v___x_1637_, 2);
v___x_1676_ = l_Lean_Meta_Context_config(v___y_1633_);
v_isDefEqStuckEx_1677_ = lean_ctor_get_uint8(v___x_1676_, 4);
lean_dec_ref(v___x_1676_);
if (v_isDefEqStuckEx_1677_ == 0)
{
v___y_1623_ = v_declName_1675_;
goto v___jp_1622_;
}
else
{
uint8_t v___x_1678_; 
v___x_1678_ = l_Lean_Expr_hasExprMVar(v_a_1618_);
if (v___x_1678_ == 0)
{
v___y_1623_ = v_declName_1675_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1679_; 
lean_inc(v_declName_1675_);
v___x_1679_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1675_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; uint8_t v___x_1681_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = lean_unbox(v_a_1680_);
lean_dec(v_a_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v_env_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_st_ref_get(v___y_1636_);
v_env_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc_ref(v_env_1683_);
lean_dec(v___x_1682_);
v___x_1684_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1683_, v_a_1618_);
if (lean_obj_tag(v___x_1684_) == 1)
{
lean_object* v_val_1685_; lean_object* v_numDiscrs_1686_; lean_object* v_nargs_1687_; lean_object* v_dummy_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_val_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_val_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v_numDiscrs_1686_ = lean_ctor_get(v_val_1685_, 1);
lean_inc(v_numDiscrs_1686_);
v_nargs_1687_ = l_Lean_Expr_getAppNumArgs(v_a_1618_);
v_dummy_1688_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1687_);
v___x_1689_ = lean_mk_array(v_nargs_1687_, v_dummy_1688_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_nat_sub(v_nargs_1687_, v___x_1690_);
lean_dec(v_nargs_1687_);
lean_inc(v_a_1618_);
v___x_1692_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1618_, v___x_1689_, v___x_1691_);
v___x_1693_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1685_);
lean_dec(v_val_1685_);
v___x_1694_ = lean_nat_add(v___x_1693_, v_numDiscrs_1686_);
lean_dec(v_numDiscrs_1686_);
v___x_1695_ = l_Array_toSubarray___redArg(v___x_1692_, v___x_1693_, v___x_1694_);
v___x_1696_ = lean_box(0);
v___x_1697_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1695_, v___x_1696_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_dec_ref_known(v___x_1697_, 1);
v___y_1623_ = v_declName_1675_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_declName_1675_);
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
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
else
{
lean_object* v___x_1706_; lean_object* v_a_1707_; uint8_t v___x_1708_; 
lean_dec(v___x_1684_);
lean_inc(v_declName_1675_);
v___x_1706_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1675_, v___y_1636_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
if (v___x_1708_ == 0)
{
v___y_1623_ = v_declName_1675_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_dec_ref_known(v___x_1709_, 1);
v___y_1623_ = v_declName_1675_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_declName_1675_);
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_dec_ref_known(v___x_1718_, 1);
v___y_1623_ = v_declName_1675_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_declName_1675_);
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_declName_1675_);
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v_a_1727_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1679_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1679_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderType_1735_; lean_object* v_body_1736_; uint8_t v___x_1737_; 
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v_binderType_1735_ = lean_ctor_get(v___x_1637_, 1);
lean_inc_ref(v_binderType_1735_);
v_body_1736_ = lean_ctor_get(v___x_1637_, 2);
lean_inc_ref(v_body_1736_);
lean_dec_ref_known(v___x_1637_, 3);
v___x_1737_ = l_Lean_Expr_hasLooseBVars(v_body_1736_);
if (v___x_1737_ == 0)
{
v___y_1605_ = v_binderType_1735_;
v_b_1606_ = v_body_1736_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1736_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___y_1605_ = v_binderType_1735_;
v_b_1606_ = v_a_1739_;
goto v___jp_1604_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_binderType_1735_);
v_a_1740_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1738_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1738_);
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
}
case 9:
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v_a_1748_ = lean_ctor_get(v___x_1637_, 0);
lean_inc_ref(v_a_1748_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1749_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_a_1748_);
v___x_1750_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
case 11:
{
lean_object* v_typeName_1753_; lean_object* v_idx_1754_; lean_object* v_struct_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_del_object(v___x_1620_);
v_typeName_1753_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_typeName_1753_);
v_idx_1754_ = lean_ctor_get(v___x_1637_, 1);
lean_inc(v_idx_1754_);
v_struct_1755_ = lean_ctor_get(v___x_1637_, 2);
lean_inc_ref(v_struct_1755_);
lean_dec_ref_known(v___x_1637_, 3);
v___x_1756_ = l_Lean_Expr_getAppNumArgs(v_a_1618_);
lean_inc(v___x_1756_);
v___x_1757_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1757_, 0, v_typeName_1753_);
lean_ctor_set(v___x_1757_, 1, v_idx_1754_);
lean_ctor_set(v___x_1757_, 2, v___x_1756_);
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_mk_empty_array_with_capacity(v___x_1758_);
v___x_1760_ = lean_array_push(v___x_1759_, v_struct_1755_);
v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1756_);
lean_dec(v___x_1756_);
v___x_1762_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1618_, v___x_1761_);
v___x_1763_ = l_Array_append___redArg(v___x_1760_, v___x_1762_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1757_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
default: 
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v___x_1637_);
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v___x_1766_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1617_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1617_);
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
v___jp_1604_:
{
uint8_t v___x_1607_; 
v___x_1607_ = l_Lean_Expr_hasLooseBVars(v_b_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1608_ = lean_box(5);
v___x_1609_ = lean_unsigned_to_nat(2u);
v___x_1610_ = lean_mk_empty_array_with_capacity(v___x_1609_);
v___x_1611_ = lean_array_push(v___x_1610_, v___y_1605_);
v___x_1612_ = lean_array_push(v___x_1611_, v_b_1606_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1608_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref(v_b_1606_);
lean_dec_ref(v___y_1605_);
v___x_1615_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1789_, lean_object* v_isMatch_1790_, lean_object* v_root_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
uint8_t v_isMatch_boxed_1797_; uint8_t v_root_boxed_1798_; lean_object* v_res_1799_; 
v_isMatch_boxed_1797_ = lean_unbox(v_isMatch_1790_);
v_root_boxed_1798_ = lean_unbox(v_root_1791_);
v_res_1799_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1789_, v_isMatch_boxed_1797_, v_root_boxed_1798_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1800_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1814_, lean_object* v_R_1815_, lean_object* v_a_1816_, lean_object* v_b_1817_, lean_object* v_c_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1816_, v_b_1817_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1825_, lean_object* v_R_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_, lean_object* v_c_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1825_, v_R_1826_, v_a_1827_, v_b_1828_, v_c_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1836_, uint8_t v_root_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
uint8_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = 1;
v___x_1844_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1836_, v___x_1843_, v_root_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1845_, lean_object* v_root_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
uint8_t v_root_boxed_1852_; lean_object* v_res_1853_; 
v_root_boxed_1852_ = lean_unbox(v_root_1846_);
v_res_1853_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1845_, v_root_boxed_1852_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_unsigned_to_nat(16u);
v___x_1858_ = lean_mk_array(v___x_1857_, v___x_1856_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___x_1859_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1864_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_1865_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1868_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1866_);
lean_ctor_set(v___x_1868_, 2, v___x_1865_);
lean_ctor_set(v___x_1868_, 3, v___x_1864_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1879_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1877_);
lean_ctor_set(v___x_1879_, 2, v___x_1876_);
lean_ctor_set(v___x_1879_, 3, v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1882_, lean_object* v_x_1883_){
_start:
{
lean_object* v_values_1884_; lean_object* v_star_1885_; lean_object* v_children_1886_; lean_object* v_pending_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_values_1884_ = lean_ctor_get(v_x_1882_, 0);
v_star_1885_ = lean_ctor_get(v_x_1882_, 1);
v_children_1886_ = lean_ctor_get(v_x_1882_, 2);
v_pending_1887_ = lean_ctor_get(v_x_1882_, 3);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v_x_1882_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_pending_1887_);
lean_inc(v_children_1886_);
lean_inc(v_star_1885_);
lean_inc(v_values_1884_);
lean_dec(v_x_1882_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_array_push(v_pending_1887_, v_x_1883_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 3, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_values_1884_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_star_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_children_1886_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1897_, v_x_1898_);
return v___x_1899_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_mk_empty_array_with_capacity(v___x_1901_);
v___x_1903_ = lean_array_push(v___x_1902_, v___x_1900_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1905_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v_env_1916_; lean_object* v___x_1917_; lean_object* v_toCold_1918_; lean_object* v_mctx_1919_; lean_object* v_lctx_1920_; lean_object* v_options_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1915_ = lean_st_ref_get(v___y_1913_);
v_env_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_env_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = lean_st_ref_get(v___y_1911_);
v_toCold_1918_ = lean_ctor_get(v___y_1912_, 0);
v_mctx_1919_ = lean_ctor_get(v___x_1917_, 0);
lean_inc_ref(v_mctx_1919_);
lean_dec(v___x_1917_);
v_lctx_1920_ = lean_ctor_get(v___y_1910_, 2);
v_options_1921_ = lean_ctor_get(v_toCold_1918_, 2);
lean_inc_ref(v_options_1921_);
lean_inc_ref(v_lctx_1920_);
v___x_1922_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1922_, 0, v_env_1916_);
lean_ctor_set(v___x_1922_, 1, v_mctx_1919_);
lean_ctor_set(v___x_1922_, 2, v_lctx_1920_);
lean_ctor_set(v___x_1922_, 3, v_options_1921_);
v___x_1923_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_msgData_1909_);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_ref_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
v_ref_1938_ = lean_ctor_get(v___y_1935_, 2);
v___x_1939_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_inc(v_ref_1938_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_ref_1938_);
lean_ctor_set(v___x_1944_, 1, v_a_1940_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set_tag(v___x_1942_, 1);
lean_ctor_set(v___x_1942_, 0, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1955_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1958_ = l_Lean_stringToMessageData(v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1959_, lean_object* v_todo_1960_, lean_object* v_e_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
uint8_t v___x_1967_; 
v___x_1967_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1961_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1961_, v_root_1959_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2108_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_2108_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2108_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_v_1974_; lean_object* v___x_1980_; lean_object* v_k_1982_; lean_object* v_nargs_1983_; lean_object* v_todo_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; 
v___x_1980_ = l_Lean_Expr_getAppFn(v_a_1969_);
switch(lean_obj_tag(v___x_1980_))
{
case 9:
{
lean_object* v_a_2027_; 
lean_dec(v_a_1969_);
v_a_2027_ = lean_ctor_get(v___x_1980_, 0);
lean_inc_ref(v_a_2027_);
lean_dec_ref_known(v___x_1980_, 1);
v_v_1974_ = v_a_2027_;
goto v___jp_1973_;
}
case 4:
{
lean_object* v_declName_2028_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; 
v_declName_2028_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_declName_2028_);
if (v_root_1959_ == 0)
{
lean_object* v___x_2036_; 
lean_inc(v_a_1969_);
v___x_2036_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1969_);
if (lean_obj_tag(v___x_2036_) == 1)
{
lean_object* v_val_2037_; 
lean_dec_ref_known(v___x_1980_, 2);
lean_dec(v_declName_2028_);
lean_dec(v_a_1969_);
v_val_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_val_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v_v_1974_ = v_val_2037_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_2038_; 
lean_dec(v___x_2036_);
lean_del_object(v___x_1971_);
v___x_2038_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2028_, v_a_1969_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
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
uint8_t v___x_2043_; 
v___x_2043_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2043_ == 0)
{
lean_del_object(v___x_2041_);
v___y_2030_ = v_a_1962_;
v___y_2031_ = v_a_1963_;
v___y_2032_ = v_a_1964_;
v___y_2033_ = v_a_1965_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec_ref_known(v___x_1980_, 2);
lean_dec(v_declName_2028_);
lean_dec(v_a_1969_);
v___x_2044_ = lean_box(3);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v_todo_1960_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2045_);
v___x_2047_ = v___x_2041_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_declName_2028_);
lean_dec_ref_known(v___x_1980_, 2);
lean_dec(v_a_1969_);
lean_dec_ref(v_todo_1960_);
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
lean_del_object(v___x_1971_);
v___y_2030_ = v_a_1962_;
v___y_2031_ = v_a_1963_;
v___y_2032_ = v_a_1964_;
v___y_2033_ = v_a_1965_;
goto v___jp_2029_;
}
v___jp_2029_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = l_Lean_Expr_getAppNumArgs(v_a_1969_);
lean_inc(v___x_2034_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_declName_2028_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v_k_1982_ = v___x_2035_;
v_nargs_1983_ = v___x_2034_;
v_todo_1984_ = v_todo_1960_;
v___y_1985_ = v___y_2030_;
v___y_1986_ = v___y_2031_;
v___y_1987_ = v___y_2032_;
v___y_1988_ = v___y_2033_;
goto v___jp_1981_;
}
}
case 11:
{
lean_object* v_typeName_2058_; lean_object* v_idx_2059_; lean_object* v_struct_2060_; lean_object* v___x_2061_; lean_object* v___y_2063_; lean_object* v_env_2067_; uint8_t v___x_2068_; 
lean_del_object(v___x_1971_);
v_typeName_2058_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_typeName_2058_);
v_idx_2059_ = lean_ctor_get(v___x_1980_, 1);
lean_inc(v_idx_2059_);
v_struct_2060_ = lean_ctor_get(v___x_1980_, 2);
lean_inc_ref(v_struct_2060_);
v___x_2061_ = lean_st_ref_get(v_a_1965_);
v_env_2067_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2061_);
v___x_2068_ = l_Lean_isClass(v_env_2067_, v_typeName_2058_);
if (v___x_2068_ == 0)
{
v___y_2063_ = v_struct_2060_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2060_);
v___y_2063_ = v___x_2069_;
goto v___jp_2062_;
}
v___jp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = l_Lean_Expr_getAppNumArgs(v_a_1969_);
lean_inc(v___x_2064_);
v___x_2065_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2065_, 0, v_typeName_2058_);
lean_ctor_set(v___x_2065_, 1, v_idx_2059_);
lean_ctor_set(v___x_2065_, 2, v___x_2064_);
v___x_2066_ = lean_array_push(v_todo_1960_, v___y_2063_);
v_k_1982_ = v___x_2065_;
v_nargs_1983_ = v___x_2064_;
v_todo_1984_ = v___x_2066_;
v___y_1985_ = v_a_1962_;
v___y_1986_ = v_a_1963_;
v___y_1987_ = v_a_1964_;
v___y_1988_ = v_a_1965_;
goto v___jp_1981_;
}
}
case 1:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec_ref_known(v___x_1980_, 1);
lean_del_object(v___x_1971_);
lean_dec(v_a_1969_);
v___x_2070_ = lean_box(3);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v_todo_1960_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
case 2:
{
lean_object* v_mvarId_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
lean_del_object(v___x_1971_);
lean_dec(v_a_1969_);
v_mvarId_2073_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_mvarId_2073_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_2074_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2075_ = l_Lean_instBEqMVarId_beq(v_mvarId_2073_, v___x_2074_);
lean_dec(v_mvarId_2073_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec_ref(v_todo_1960_);
v___x_2076_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2077_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2076_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_box(3);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_todo_1960_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
case 7:
{
lean_object* v_binderType_2081_; lean_object* v_body_2082_; lean_object* v_b_2084_; uint8_t v___x_2094_; 
lean_del_object(v___x_1971_);
lean_dec(v_a_1969_);
v_binderType_2081_ = lean_ctor_get(v___x_1980_, 1);
lean_inc_ref(v_binderType_2081_);
v_body_2082_ = lean_ctor_get(v___x_1980_, 2);
lean_inc_ref(v_body_2082_);
lean_dec_ref_known(v___x_1980_, 3);
v___x_2094_ = l_Lean_Expr_hasLooseBVars(v_body_2082_);
if (v___x_2094_ == 0)
{
v_b_2084_ = v_body_2082_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2082_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_b_2084_ = v_a_2096_;
goto v___jp_2083_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_binderType_2081_);
lean_dec_ref(v_todo_1960_);
v_a_2097_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2095_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
v___jp_2083_:
{
uint8_t v___x_2085_; 
v___x_2085_ = l_Lean_Expr_hasLooseBVars(v_b_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2086_ = lean_box(5);
v___x_2087_ = lean_array_push(v_todo_1960_, v_binderType_2081_);
v___x_2088_ = lean_array_push(v___x_2087_, v_b_2084_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2086_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref(v_b_2084_);
lean_dec_ref(v_binderType_2081_);
v___x_2091_ = lean_box(4);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_todo_1960_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
default: 
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec_ref(v___x_1980_);
lean_del_object(v___x_1971_);
lean_dec(v_a_1969_);
v___x_2105_ = lean_box(4);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_todo_1960_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
}
v___jp_1973_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1975_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_v_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v_todo_1960_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1976_);
v___x_1978_ = v___x_1971_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
v___jp_1981_:
{
lean_object* v___x_1989_; 
lean_inc(v_nargs_1983_);
v___x_1989_ = l_Lean_Meta_getFunInfoNArgs(v___x_1980_, v_nargs_1983_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v_paramInfo_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2017_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v_paramInfo_1991_ = lean_ctor_get(v_a_1990_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_a_1990_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v_a_1990_, 1);
lean_dec(v_unused_2018_);
v___x_1993_ = v_a_1990_;
v_isShared_1994_ = v_isSharedCheck_2017_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_paramInfo_1991_);
lean_dec(v_a_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2017_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_sub(v_nargs_1983_, v___x_1995_);
lean_dec(v_nargs_1983_);
v___x_1997_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_1991_, v___x_1996_, v_a_1969_, v_todo_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec_ref(v_paramInfo_1991_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2008_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v_a_1998_);
lean_ctor_set(v___x_1993_, 0, v_k_1982_);
v___x_2003_ = v___x_1993_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_del_object(v___x_1993_);
lean_dec(v_k_1982_);
v_a_2009_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1997_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1997_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_todo_1984_);
lean_dec(v_nargs_1983_);
lean_dec(v_k_1982_);
lean_dec(v_a_1969_);
v_a_2019_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1989_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1989_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
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
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_todo_1960_);
v_a_2109_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_1968_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_1968_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec_ref(v_e_1961_);
v___x_2117_ = lean_box(3);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_todo_1960_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2120_, lean_object* v_todo_2121_, lean_object* v_e_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
uint8_t v_root_boxed_2128_; lean_object* v_res_2129_; 
v_root_boxed_2128_ = lean_unbox(v_root_2120_);
v_res_2129_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2128_, v_todo_2121_, v_e_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2130_, lean_object* v_msg_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_msg_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2138_, v_msg_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_unsigned_to_nat(8u);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2153_ = 1;
v___x_2154_ = lean_unsigned_to_nat(8u);
v___x_2155_ = lean_mk_empty_array_with_capacity(v___x_2154_);
v___x_2156_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2153_, v___x_2155_, v_e_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2164_, uint8_t v_root_2165_, lean_object* v_todo_2166_, lean_object* v_keys_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = lean_array_get_size(v_todo_2166_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_nat_dec_eq(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_e_2179_; lean_object* v_todo_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2176_ = l_Lean_instInhabitedExpr;
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = lean_nat_sub(v___x_2173_, v___x_2177_);
v_e_2179_ = lean_array_get(v___x_2176_, v_todo_2166_, v___x_2178_);
lean_dec(v___x_2178_);
v_todo_2180_ = lean_array_pop(v_todo_2166_);
v___x_2181_ = lean_box(v_root_2165_);
lean_inc_ref(v_op_2164_);
lean_inc(v_a_2171_);
lean_inc_ref(v_a_2170_);
lean_inc(v_a_2169_);
lean_inc_ref(v_a_2168_);
v___x_2182_ = lean_apply_8(v_op_2164_, v___x_2181_, v_todo_2180_, v_e_2179_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, lean_box(0));
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; lean_object* v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v_fst_2184_ = lean_ctor_get(v_a_2183_, 0);
lean_inc(v_fst_2184_);
v_snd_2185_ = lean_ctor_get(v_a_2183_, 1);
lean_inc(v_snd_2185_);
lean_dec(v_a_2183_);
v___x_2186_ = lean_array_push(v_keys_2167_, v_fst_2184_);
v_root_2165_ = v___x_2175_;
v_todo_2166_ = v_snd_2185_;
v_keys_2167_ = v___x_2186_;
goto _start;
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_keys_2167_);
lean_dec_ref(v_op_2164_);
v_a_2188_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2182_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2182_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
else
{
lean_object* v___x_2196_; 
lean_dec_ref(v_todo_2166_);
lean_dec_ref(v_op_2164_);
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_keys_2167_);
return v___x_2196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2197_, lean_object* v_root_2198_, lean_object* v_todo_2199_, lean_object* v_keys_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
uint8_t v_root_boxed_2206_; lean_object* v_res_2207_; 
v_root_boxed_2206_ = lean_unbox(v_root_2198_);
v_res_2207_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2197_, v_root_boxed_2206_, v_todo_2199_, v_keys_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_op_2215_; lean_object* v___x_2216_; lean_object* v_todo_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v_op_2215_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2216_ = lean_unsigned_to_nat(8u);
v_todo_2217_ = lean_mk_empty_array_with_capacity(v___x_2216_);
v___x_2218_ = 1;
lean_inc_ref(v_todo_2217_);
v___x_2219_ = lean_array_push(v_todo_2217_, v_e_2209_);
v___x_2220_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2215_, v___x_2218_, v___x_2219_, v_todo_2217_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2228_, lean_object* v_todo_2229_, lean_object* v_e_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
uint8_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = 1;
v___x_2237_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2230_, v___x_2236_, v_root_2228_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2255_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2255_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2255_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_fst_2242_; lean_object* v_snd_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2254_; 
v_fst_2242_ = lean_ctor_get(v_a_2238_, 0);
v_snd_2243_ = lean_ctor_get(v_a_2238_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_a_2238_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2245_ = v_a_2238_;
v_isShared_2246_ = v_isSharedCheck_2254_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_snd_2243_);
lean_inc(v_fst_2242_);
lean_dec(v_a_2238_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2254_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2247_ = l_Array_append___redArg(v_todo_2229_, v_snd_2243_);
lean_dec(v_snd_2243_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v___x_2247_);
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_fst_2242_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2249_);
v___x_2251_ = v___x_2240_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2229_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2256_, lean_object* v_todo_2257_, lean_object* v_e_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v_root_boxed_2264_; lean_object* v_res_2265_; 
v_root_boxed_2264_ = lean_unbox(v_root_2256_);
v_res_2265_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2264_, v_todo_2257_, v_e_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_op_2273_; lean_object* v___x_2274_; lean_object* v_todo_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_op_2273_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2274_ = lean_unsigned_to_nat(8u);
v_todo_2275_ = lean_mk_empty_array_with_capacity(v___x_2274_);
v___x_2276_ = 1;
lean_inc_ref(v_todo_2275_);
v___x_2277_ = lean_array_push(v_todo_2275_, v_e_2267_);
v___x_2278_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2273_, v___x_2276_, v___x_2277_, v_todo_2275_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2286_, lean_object* v_m_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_st_mk_ref(v_tries_2286_);
lean_inc(v___x_2293_);
v___x_2294_ = lean_apply_6(v_m_2287_, v___x_2293_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, lean_box(0));
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2304_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2299_ = lean_st_ref_get(v___x_2293_);
lean_dec(v___x_2293_);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v_a_2295_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2300_);
v___x_2302_ = v___x_2297_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v___x_2293_);
v_a_2305_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2294_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2294_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2313_, lean_object* v_m_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2313_, v_m_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2321_, lean_object* v_m_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_tries_2328_; lean_object* v_roots_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2382_; 
v_tries_2328_ = lean_ctor_get(v_d_2321_, 0);
v_roots_2329_ = lean_ctor_get(v_d_2321_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_d_2321_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2331_ = v_d_2321_;
v_isShared_2332_ = v_isSharedCheck_2382_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_roots_2329_);
lean_inc(v_tries_2328_);
lean_dec(v_d_2321_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2382_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___y_2334_; lean_object* v___x_2363_; uint8_t v_transparency_2364_; uint8_t v___x_2365_; uint8_t v___x_2366_; 
v___x_2363_ = l_Lean_Meta_Context_config(v_a_2323_);
v_transparency_2364_ = lean_ctor_get_uint8(v___x_2363_, 9);
lean_dec_ref(v___x_2363_);
v___x_2365_ = 2;
v___x_2366_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2364_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v_keyedConfig_2367_; uint8_t v_trackZetaDelta_2368_; lean_object* v_zetaDeltaSet_2369_; lean_object* v_lctx_2370_; lean_object* v_localInstances_2371_; lean_object* v_defEqCtx_x3f_2372_; lean_object* v_synthPendingDepth_2373_; lean_object* v_customCanUnfoldPredicate_x3f_2374_; uint8_t v_univApprox_2375_; uint8_t v_inTypeClassResolution_2376_; uint8_t v_cacheInferType_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_keyedConfig_2367_ = lean_ctor_get(v_a_2323_, 0);
v_trackZetaDelta_2368_ = lean_ctor_get_uint8(v_a_2323_, sizeof(void*)*7);
v_zetaDeltaSet_2369_ = lean_ctor_get(v_a_2323_, 1);
v_lctx_2370_ = lean_ctor_get(v_a_2323_, 2);
v_localInstances_2371_ = lean_ctor_get(v_a_2323_, 3);
v_defEqCtx_x3f_2372_ = lean_ctor_get(v_a_2323_, 4);
v_synthPendingDepth_2373_ = lean_ctor_get(v_a_2323_, 5);
v_customCanUnfoldPredicate_x3f_2374_ = lean_ctor_get(v_a_2323_, 6);
v_univApprox_2375_ = lean_ctor_get_uint8(v_a_2323_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2376_ = lean_ctor_get_uint8(v_a_2323_, sizeof(void*)*7 + 2);
v_cacheInferType_2377_ = lean_ctor_get_uint8(v_a_2323_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2367_);
v___x_2378_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2365_, v_keyedConfig_2367_);
lean_inc(v_customCanUnfoldPredicate_x3f_2374_);
lean_inc(v_synthPendingDepth_2373_);
lean_inc(v_defEqCtx_x3f_2372_);
lean_inc_ref(v_localInstances_2371_);
lean_inc_ref(v_lctx_2370_);
lean_inc(v_zetaDeltaSet_2369_);
v___x_2379_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v_zetaDeltaSet_2369_);
lean_ctor_set(v___x_2379_, 2, v_lctx_2370_);
lean_ctor_set(v___x_2379_, 3, v_localInstances_2371_);
lean_ctor_set(v___x_2379_, 4, v_defEqCtx_x3f_2372_);
lean_ctor_set(v___x_2379_, 5, v_synthPendingDepth_2373_);
lean_ctor_set(v___x_2379_, 6, v_customCanUnfoldPredicate_x3f_2374_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*7, v_trackZetaDelta_2368_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*7 + 1, v_univApprox_2375_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2376_);
lean_ctor_set_uint8(v___x_2379_, sizeof(void*)*7 + 3, v_cacheInferType_2377_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
lean_inc(v_a_2324_);
v___x_2380_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2328_, v_m_2322_, v___x_2379_, v_a_2324_, v_a_2325_, v_a_2326_);
v___y_2334_ = v___x_2380_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2381_; 
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
lean_inc(v_a_2324_);
lean_inc_ref(v_a_2323_);
v___x_2381_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2328_, v_m_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
v___y_2334_ = v___x_2381_;
goto v___jp_2333_;
}
v___jp_2333_:
{
if (lean_obj_tag(v___y_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2354_; 
v_a_2335_ = lean_ctor_get(v___y_2334_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___y_2334_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2337_ = v___y_2334_;
v_isShared_2338_ = v_isSharedCheck_2354_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___y_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2354_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_fst_2339_; lean_object* v_snd_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2353_; 
v_fst_2339_ = lean_ctor_get(v_a_2335_, 0);
v_snd_2340_ = lean_ctor_get(v_a_2335_, 1);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_a_2335_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2342_ = v_a_2335_;
v_isShared_2343_ = v_isSharedCheck_2353_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_snd_2340_);
lean_inc(v_fst_2339_);
lean_dec(v_a_2335_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2353_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v_snd_2340_);
v___x_2345_ = v___x_2331_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_snd_2340_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_roots_2329_);
v___x_2345_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 1, v___x_2345_);
v___x_2347_ = v___x_2342_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_fst_2339_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2347_);
v___x_2349_ = v___x_2337_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_del_object(v___x_2331_);
lean_dec_ref(v_roots_2329_);
v_a_2355_ = lean_ctor_get(v___y_2334_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___y_2334_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___y_2334_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___y_2334_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2383_, lean_object* v_m_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2383_, v_m_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2391_, lean_object* v_00_u03b2_2392_, lean_object* v_d_2393_, lean_object* v_m_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2393_, v_m_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_00_u03b2_2402_, lean_object* v_d_2403_, lean_object* v_m_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2401_, v_00_u03b2_2402_, v_d_2403_, v_m_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2411_, lean_object* v_v_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2415_ = lean_st_ref_take(v_a_2413_);
v___x_2416_ = lean_array_set(v___x_2415_, v_i_2411_, v_v_2412_);
v___x_2417_ = lean_st_ref_put(v_a_2413_, v___x_2416_);
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2420_, lean_object* v_v_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2420_, v_v_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec(v_i_2420_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2425_, lean_object* v_i_2426_, lean_object* v_v_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2426_, v_v_2427_, v_a_2428_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_i_2436_, lean_object* v_v_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2435_, v_i_2436_, v_v_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec(v_i_2436_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_sz_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v_sz_2447_ = lean_array_get_size(v_a_2446_);
v___x_2448_ = lean_unsigned_to_nat(0u);
v___x_2449_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2450_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_mk_empty_array_with_capacity(v___x_2451_);
v___x_2453_ = lean_array_push(v___x_2452_, v_e_2445_);
v___x_2454_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2449_);
lean_ctor_set(v___x_2454_, 1, v___x_2448_);
lean_ctor_set(v___x_2454_, 2, v___x_2450_);
lean_ctor_set(v___x_2454_, 3, v___x_2453_);
v___x_2455_ = lean_array_push(v_a_2446_, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v_sz_2447_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2457_, lean_object* v_e_2458_){
_start:
{
lean_object* v_modifyGet_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
v_modifyGet_2459_ = lean_ctor_get(v_inst_2457_, 2);
lean_inc(v_modifyGet_2459_);
lean_dec_ref(v_inst_2457_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2460_, 0, v_e_2458_);
v___x_2461_ = lean_apply_2(v_modifyGet_2459_, lean_box(0), v___f_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2462_, lean_object* v_00_u03b1_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_e_2466_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2465_, v_e_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2468_, lean_object* v_00_u03b1_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v_e_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2468_, v_00_u03b1_2469_, v_inst_2470_, v_inst_2471_, v_e_2472_);
lean_dec_ref(v_inst_2470_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2474_, lean_object* v_e_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; lean_object* v_fst_2480_; lean_object* v_snd_2481_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2478_ = lean_st_ref_take(v_a_2476_);
v___x_2484_ = lean_box(0);
v___x_2485_ = lean_array_get_size(v___x_2478_);
v___x_2486_ = lean_nat_dec_lt(v_i_2474_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_dec_ref(v_e_2475_);
v_fst_2480_ = v___x_2484_;
v_snd_2481_ = v___x_2478_;
goto v___jp_2479_;
}
else
{
lean_object* v_v_2487_; lean_object* v_xs_x27_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_v_2487_ = lean_array_fget(v___x_2478_, v_i_2474_);
v_xs_x27_2488_ = lean_array_fset(v___x_2478_, v_i_2474_, v___x_2484_);
v___x_2489_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2487_, v_e_2475_);
v___x_2490_ = lean_array_fset(v_xs_x27_2488_, v_i_2474_, v___x_2489_);
v_fst_2480_ = v___x_2484_;
v_snd_2481_ = v___x_2490_;
goto v___jp_2479_;
}
v___jp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_st_ref_put(v_a_2476_, v_snd_2481_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_fst_2480_);
return v___x_2483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2491_, lean_object* v_e_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2491_, v_e_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec(v_i_2491_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2496_, lean_object* v_i_2497_, lean_object* v_e_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2497_, v_e_2498_, v_a_2499_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2506_, lean_object* v_i_2507_, lean_object* v_e_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2506_, v_i_2507_, v_e_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec(v_i_2507_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
lean_inc(v___y_2517_);
v___x_2523_ = lean_apply_6(v_x_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, lean_box(0));
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2525_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2532_, lean_object* v_localInsts_2533_, lean_object* v_x_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___f_2541_; lean_object* v___x_2542_; 
lean_inc(v___y_2535_);
v___f_2541_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2541_, 0, v_x_2534_);
lean_closure_set(v___f_2541_, 1, v___y_2535_);
v___x_2542_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2532_, v_localInsts_2533_, v___f_2541_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
if (lean_obj_tag(v___x_2542_) == 0)
{
return v___x_2542_;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2551_, lean_object* v_localInsts_2552_, lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2551_, v_localInsts_2552_, v_x_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2561_, lean_object* v_00_u03b1_2562_, lean_object* v_lctx_2563_, lean_object* v_localInsts_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2563_, v_localInsts_2564_, v_x_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b1_2574_, lean_object* v_lctx_2575_, lean_object* v_localInsts_2576_, lean_object* v_x_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2573_, v_00_u03b1_2574_, v_lctx_2575_, v_localInsts_2576_, v_x_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v_sz_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2588_ = lean_st_ref_take(v___y_2586_);
v_sz_2589_ = lean_array_get_size(v___x_2588_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2592_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_mk_empty_array_with_capacity(v___x_2593_);
v___x_2595_ = lean_array_push(v___x_2594_, v_e_2585_);
v___x_2596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2591_);
lean_ctor_set(v___x_2596_, 1, v___x_2590_);
lean_ctor_set(v___x_2596_, 2, v___x_2592_);
lean_ctor_set(v___x_2596_, 3, v___x_2595_);
v___x_2597_ = lean_array_push(v___x_2588_, v___x_2596_);
v___x_2598_ = lean_st_ref_put(v___y_2586_, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_sz_2589_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2600_, v___y_2601_);
lean_dec(v___y_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2604_, lean_object* v_e_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2605_, v___y_2606_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2613_, lean_object* v_e_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2613_, v_e_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2622_, lean_object* v_todo_2623_, lean_object* v_e_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2622_, v_todo_2623_, v_e_2624_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2632_, lean_object* v_todo_2633_, lean_object* v_e_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
uint8_t v___x_3410__boxed_2641_; lean_object* v_res_2642_; 
v___x_3410__boxed_2641_ = lean_unbox(v___x_2632_);
v_res_2642_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3410__boxed_2641_, v_todo_2633_, v_e_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2643_, lean_object* v_b_2644_, lean_object* v_x_2645_){
_start:
{
if (lean_obj_tag(v_x_2645_) == 0)
{
lean_dec(v_b_2644_);
lean_dec(v_a_2643_);
return v_x_2645_;
}
else
{
lean_object* v_key_2646_; lean_object* v_value_2647_; lean_object* v_tail_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2660_; 
v_key_2646_ = lean_ctor_get(v_x_2645_, 0);
v_value_2647_ = lean_ctor_get(v_x_2645_, 1);
v_tail_2648_ = lean_ctor_get(v_x_2645_, 2);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_x_2645_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2650_ = v_x_2645_;
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_tail_2648_);
lean_inc(v_value_2647_);
lean_inc(v_key_2646_);
lean_dec(v_x_2645_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
uint8_t v___x_2652_; 
v___x_2652_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2646_, v_a_2643_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2643_, v_b_2644_, v_tail_2648_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 2, v___x_2653_);
v___x_2655_ = v___x_2650_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_key_2646_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_value_2647_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
else
{
lean_object* v___x_2658_; 
lean_dec(v_value_2647_);
lean_dec(v_key_2646_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v_b_2644_);
lean_ctor_set(v___x_2650_, 0, v_a_2643_);
v___x_2658_ = v___x_2650_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2643_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_b_2644_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_tail_2648_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2661_, lean_object* v_x_2662_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 0)
{
uint8_t v___x_2663_; 
v___x_2663_ = 0;
return v___x_2663_;
}
else
{
lean_object* v_key_2664_; lean_object* v_tail_2665_; uint8_t v___x_2666_; 
v_key_2664_ = lean_ctor_get(v_x_2662_, 0);
v_tail_2665_ = lean_ctor_get(v_x_2662_, 2);
v___x_2666_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2664_, v_a_2661_);
if (v___x_2666_ == 0)
{
v_x_2662_ = v_tail_2665_;
goto _start;
}
else
{
return v___x_2666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2668_, lean_object* v_x_2669_){
_start:
{
uint8_t v_res_2670_; lean_object* v_r_2671_; 
v_res_2670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2668_, v_x_2669_);
lean_dec(v_x_2669_);
lean_dec(v_a_2668_);
v_r_2671_ = lean_box(v_res_2670_);
return v_r_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2672_, lean_object* v_x_2673_){
_start:
{
if (lean_obj_tag(v_x_2673_) == 0)
{
return v_x_2672_;
}
else
{
lean_object* v_key_2674_; lean_object* v_value_2675_; lean_object* v_tail_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2699_; 
v_key_2674_ = lean_ctor_get(v_x_2673_, 0);
v_value_2675_ = lean_ctor_get(v_x_2673_, 1);
v_tail_2676_ = lean_ctor_get(v_x_2673_, 2);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_x_2673_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2678_ = v_x_2673_;
v_isShared_2679_ = v_isSharedCheck_2699_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_tail_2676_);
lean_inc(v_value_2675_);
lean_inc(v_key_2674_);
lean_dec(v_x_2673_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2699_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; uint64_t v___x_2681_; uint64_t v___x_2682_; uint64_t v___x_2683_; uint64_t v_fold_2684_; uint64_t v___x_2685_; uint64_t v___x_2686_; uint64_t v___x_2687_; size_t v___x_2688_; size_t v___x_2689_; size_t v___x_2690_; size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2680_ = lean_array_get_size(v_x_2672_);
v___x_2681_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2674_);
v___x_2682_ = 32ULL;
v___x_2683_ = lean_uint64_shift_right(v___x_2681_, v___x_2682_);
v_fold_2684_ = lean_uint64_xor(v___x_2681_, v___x_2683_);
v___x_2685_ = 16ULL;
v___x_2686_ = lean_uint64_shift_right(v_fold_2684_, v___x_2685_);
v___x_2687_ = lean_uint64_xor(v_fold_2684_, v___x_2686_);
v___x_2688_ = lean_uint64_to_usize(v___x_2687_);
v___x_2689_ = lean_usize_of_nat(v___x_2680_);
v___x_2690_ = ((size_t)1ULL);
v___x_2691_ = lean_usize_sub(v___x_2689_, v___x_2690_);
v___x_2692_ = lean_usize_land(v___x_2688_, v___x_2691_);
v___x_2693_ = lean_array_uget_borrowed(v_x_2672_, v___x_2692_);
lean_inc(v___x_2693_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 2, v___x_2693_);
v___x_2695_ = v___x_2678_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_key_2674_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_value_2675_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_array_uset(v_x_2672_, v___x_2692_, v___x_2695_);
v_x_2672_ = v___x_2696_;
v_x_2673_ = v_tail_2676_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2700_, lean_object* v_source_2701_, lean_object* v_target_2702_){
_start:
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = lean_array_get_size(v_source_2701_);
v___x_2704_ = lean_nat_dec_lt(v_i_2700_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_dec_ref(v_source_2701_);
lean_dec(v_i_2700_);
return v_target_2702_;
}
else
{
lean_object* v_es_2705_; lean_object* v___x_2706_; lean_object* v_source_2707_; lean_object* v_target_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_es_2705_ = lean_array_fget(v_source_2701_, v_i_2700_);
v___x_2706_ = lean_box(0);
v_source_2707_ = lean_array_fset(v_source_2701_, v_i_2700_, v___x_2706_);
v_target_2708_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2702_, v_es_2705_);
v___x_2709_ = lean_unsigned_to_nat(1u);
v___x_2710_ = lean_nat_add(v_i_2700_, v___x_2709_);
lean_dec(v_i_2700_);
v_i_2700_ = v___x_2710_;
v_source_2701_ = v_source_2707_;
v_target_2702_ = v_target_2708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2712_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_nbuckets_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2713_ = lean_array_get_size(v_data_2712_);
v___x_2714_ = lean_unsigned_to_nat(2u);
v_nbuckets_2715_ = lean_nat_mul(v___x_2713_, v___x_2714_);
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = lean_box(0);
v___x_2718_ = lean_mk_array(v_nbuckets_2715_, v___x_2717_);
v___x_2719_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2716_, v_data_2712_, v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2720_, lean_object* v_a_2721_, lean_object* v_b_2722_){
_start:
{
lean_object* v_size_2723_; lean_object* v_buckets_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2767_; 
v_size_2723_ = lean_ctor_get(v_m_2720_, 0);
v_buckets_2724_ = lean_ctor_get(v_m_2720_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_m_2720_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2726_ = v_m_2720_;
v_isShared_2727_ = v_isSharedCheck_2767_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_buckets_2724_);
lean_inc(v_size_2723_);
lean_dec(v_m_2720_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2767_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2728_; uint64_t v___x_2729_; uint64_t v___x_2730_; uint64_t v___x_2731_; uint64_t v_fold_2732_; uint64_t v___x_2733_; uint64_t v___x_2734_; uint64_t v___x_2735_; size_t v___x_2736_; size_t v___x_2737_; size_t v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; lean_object* v_bkt_2741_; uint8_t v___x_2742_; 
v___x_2728_ = lean_array_get_size(v_buckets_2724_);
v___x_2729_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2721_);
v___x_2730_ = 32ULL;
v___x_2731_ = lean_uint64_shift_right(v___x_2729_, v___x_2730_);
v_fold_2732_ = lean_uint64_xor(v___x_2729_, v___x_2731_);
v___x_2733_ = 16ULL;
v___x_2734_ = lean_uint64_shift_right(v_fold_2732_, v___x_2733_);
v___x_2735_ = lean_uint64_xor(v_fold_2732_, v___x_2734_);
v___x_2736_ = lean_uint64_to_usize(v___x_2735_);
v___x_2737_ = lean_usize_of_nat(v___x_2728_);
v___x_2738_ = ((size_t)1ULL);
v___x_2739_ = lean_usize_sub(v___x_2737_, v___x_2738_);
v___x_2740_ = lean_usize_land(v___x_2736_, v___x_2739_);
v_bkt_2741_ = lean_array_uget_borrowed(v_buckets_2724_, v___x_2740_);
v___x_2742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2721_, v_bkt_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2743_; lean_object* v_size_x27_2744_; lean_object* v___x_2745_; lean_object* v_buckets_x27_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2743_ = lean_unsigned_to_nat(1u);
v_size_x27_2744_ = lean_nat_add(v_size_2723_, v___x_2743_);
lean_dec(v_size_2723_);
lean_inc(v_bkt_2741_);
v___x_2745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2745_, 0, v_a_2721_);
lean_ctor_set(v___x_2745_, 1, v_b_2722_);
lean_ctor_set(v___x_2745_, 2, v_bkt_2741_);
v_buckets_x27_2746_ = lean_array_uset(v_buckets_2724_, v___x_2740_, v___x_2745_);
v___x_2747_ = lean_unsigned_to_nat(4u);
v___x_2748_ = lean_nat_mul(v_size_x27_2744_, v___x_2747_);
v___x_2749_ = lean_unsigned_to_nat(3u);
v___x_2750_ = lean_nat_div(v___x_2748_, v___x_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_array_get_size(v_buckets_x27_2746_);
v___x_2752_ = lean_nat_dec_le(v___x_2750_, v___x_2751_);
lean_dec(v___x_2750_);
if (v___x_2752_ == 0)
{
lean_object* v_val_2753_; lean_object* v___x_2755_; 
v_val_2753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2746_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 1, v_val_2753_);
lean_ctor_set(v___x_2726_, 0, v_size_x27_2744_);
v___x_2755_ = v___x_2726_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_size_x27_2744_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_val_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
else
{
lean_object* v___x_2758_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 1, v_buckets_x27_2746_);
lean_ctor_set(v___x_2726_, 0, v_size_x27_2744_);
v___x_2758_ = v___x_2726_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_size_x27_2744_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_buckets_x27_2746_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_object* v___x_2760_; lean_object* v_buckets_x27_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
lean_inc(v_bkt_2741_);
v___x_2760_ = lean_box(0);
v_buckets_x27_2761_ = lean_array_uset(v_buckets_2724_, v___x_2740_, v___x_2760_);
v___x_2762_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2721_, v_b_2722_, v_bkt_2741_);
v___x_2763_ = lean_array_uset(v_buckets_x27_2761_, v___x_2740_, v___x_2762_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 1, v___x_2763_);
v___x_2765_ = v___x_2726_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_size_2723_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2768_, lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2769_) == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_box(0);
return v___x_2770_;
}
else
{
lean_object* v_key_2771_; lean_object* v_value_2772_; lean_object* v_tail_2773_; uint8_t v___x_2774_; 
v_key_2771_ = lean_ctor_get(v_x_2769_, 0);
v_value_2772_ = lean_ctor_get(v_x_2769_, 1);
v_tail_2773_ = lean_ctor_get(v_x_2769_, 2);
v___x_2774_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2771_, v_a_2768_);
if (v___x_2774_ == 0)
{
v_x_2769_ = v_tail_2773_;
goto _start;
}
else
{
lean_object* v___x_2776_; 
lean_inc(v_value_2772_);
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_value_2772_);
return v___x_2776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2777_, v_x_2778_);
lean_dec(v_x_2778_);
lean_dec(v_a_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_buckets_2782_; lean_object* v___x_2783_; uint64_t v___x_2784_; uint64_t v___x_2785_; uint64_t v___x_2786_; uint64_t v_fold_2787_; uint64_t v___x_2788_; uint64_t v___x_2789_; uint64_t v___x_2790_; size_t v___x_2791_; size_t v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_buckets_2782_ = lean_ctor_get(v_m_2780_, 1);
v___x_2783_ = lean_array_get_size(v_buckets_2782_);
v___x_2784_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2781_);
v___x_2785_ = 32ULL;
v___x_2786_ = lean_uint64_shift_right(v___x_2784_, v___x_2785_);
v_fold_2787_ = lean_uint64_xor(v___x_2784_, v___x_2786_);
v___x_2788_ = 16ULL;
v___x_2789_ = lean_uint64_shift_right(v_fold_2787_, v___x_2788_);
v___x_2790_ = lean_uint64_xor(v_fold_2787_, v___x_2789_);
v___x_2791_ = lean_uint64_to_usize(v___x_2790_);
v___x_2792_ = lean_usize_of_nat(v___x_2783_);
v___x_2793_ = ((size_t)1ULL);
v___x_2794_ = lean_usize_sub(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_usize_land(v___x_2791_, v___x_2794_);
v___x_2796_ = lean_array_uget_borrowed(v_buckets_2782_, v___x_2795_);
v___x_2797_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2781_, v___x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_m_2798_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2801_, lean_object* v_entry_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_snd_2809_; lean_object* v_snd_2810_; lean_object* v_fst_2811_; lean_object* v_fst_2812_; lean_object* v_snd_2813_; lean_object* v_fst_2814_; lean_object* v_fst_2815_; lean_object* v_snd_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_snd_2809_ = lean_ctor_get(v_p_2801_, 1);
v_snd_2810_ = lean_ctor_get(v_entry_2802_, 1);
lean_inc(v_snd_2810_);
v_fst_2811_ = lean_ctor_get(v_p_2801_, 0);
v_fst_2812_ = lean_ctor_get(v_snd_2809_, 0);
v_snd_2813_ = lean_ctor_get(v_snd_2809_, 1);
v_fst_2814_ = lean_ctor_get(v_entry_2802_, 0);
lean_inc(v_fst_2814_);
lean_dec_ref(v_entry_2802_);
v_fst_2815_ = lean_ctor_get(v_snd_2810_, 0);
lean_inc(v_fst_2815_);
v_snd_2816_ = lean_ctor_get(v_snd_2810_, 1);
v___x_2817_ = lean_array_get_size(v_fst_2814_);
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = lean_nat_dec_eq(v___x_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2926_; 
v_fst_2820_ = lean_ctor_get(v_fst_2815_, 0);
v_snd_2821_ = lean_ctor_get(v_fst_2815_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_fst_2815_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2823_ = v_fst_2815_;
v_isShared_2824_ = v_isSharedCheck_2926_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snd_2821_);
lean_inc(v_fst_2820_);
lean_dec(v_fst_2815_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2926_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v_e_2828_; lean_object* v_todo_2829_; lean_object* v___x_2830_; lean_object* v___f_2831_; lean_object* v___x_2832_; 
v___x_2825_ = l_Lean_instInhabitedExpr;
v___x_2826_ = lean_unsigned_to_nat(1u);
v___x_2827_ = lean_nat_sub(v___x_2817_, v___x_2826_);
v_e_2828_ = lean_array_get(v___x_2825_, v_fst_2814_, v___x_2827_);
lean_dec(v___x_2827_);
v_todo_2829_ = lean_array_pop(v_fst_2814_);
v___x_2830_ = lean_box(v___x_2819_);
v___f_2831_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2831_, 0, v___x_2830_);
lean_closure_set(v___f_2831_, 1, v_todo_2829_);
lean_closure_set(v___f_2831_, 2, v_e_2828_);
v___x_2832_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2820_, v_snd_2821_, v___f_2831_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v_fst_2834_; lean_object* v_snd_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2917_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v_fst_2834_ = lean_ctor_get(v_a_2833_, 0);
v_snd_2835_ = lean_ctor_get(v_a_2833_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2833_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2837_ = v_a_2833_;
v_isShared_2838_ = v_isSharedCheck_2917_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snd_2835_);
lean_inc(v_fst_2834_);
lean_dec(v_a_2833_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2917_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = lean_box(3);
v___x_2840_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2834_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2813_, v_fst_2834_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2843_; 
lean_inc(v_snd_2813_);
lean_inc(v_fst_2812_);
lean_inc(v_fst_2811_);
lean_dec_ref(v_p_2801_);
lean_inc(v_snd_2810_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_snd_2810_);
lean_ctor_set(v___x_2837_, 0, v_snd_2835_);
v___x_2843_ = v___x_2837_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_snd_2835_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_snd_2810_);
v___x_2843_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2863_; 
v_isSharedCheck_2863_ = !lean_is_exclusive(v_snd_2810_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; lean_object* v_unused_2865_; 
v_unused_2864_ = lean_ctor_get(v_snd_2810_, 1);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v_snd_2810_, 0);
lean_dec(v_unused_2865_);
v___x_2845_ = v_snd_2810_;
v_isShared_2846_ = v_isSharedCheck_2863_;
goto v_resetjp_2844_;
}
else
{
lean_dec(v_snd_2810_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2863_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2862_; 
v___x_2847_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2843_, v_a_2803_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2862_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2862_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2852_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2813_, v_fst_2834_, v_a_2848_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2852_);
lean_ctor_set(v___x_2823_, 0, v_fst_2812_);
v___x_2854_ = v___x_2823_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_fst_2812_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2856_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___x_2854_);
lean_ctor_set(v___x_2845_, 0, v_fst_2811_);
v___x_2856_ = v___x_2845_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_fst_2811_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2858_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2856_);
v___x_2858_ = v___x_2850_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2867_; lean_object* v___x_2869_; 
lean_dec(v_fst_2834_);
lean_del_object(v___x_2823_);
v_val_2867_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v___x_2841_, 1);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_snd_2810_);
lean_ctor_set(v___x_2837_, 0, v_snd_2835_);
v___x_2869_ = v___x_2837_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_snd_2835_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_snd_2810_);
v___x_2869_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v___x_2870_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2867_, v___x_2869_, v_a_2803_);
lean_dec(v_val_2867_);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; 
v_unused_2878_ = lean_ctor_get(v___x_2870_, 0);
lean_dec(v_unused_2878_);
v___x_2872_ = v___x_2870_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_dec(v___x_2870_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v_p_2801_);
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_p_2801_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
else
{
uint8_t v___x_2880_; 
lean_dec(v_fst_2834_);
v___x_2880_ = lean_nat_dec_eq(v_fst_2812_, v___x_2818_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2882_; 
lean_del_object(v___x_2823_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_snd_2810_);
lean_ctor_set(v___x_2837_, 0, v_snd_2835_);
v___x_2882_ = v___x_2837_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_snd_2835_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_snd_2810_);
v___x_2882_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v___x_2883_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2812_, v___x_2882_, v_a_2803_);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; 
v_unused_2891_ = lean_ctor_get(v___x_2883_, 0);
lean_dec(v_unused_2891_);
v___x_2885_ = v___x_2883_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_dec(v___x_2883_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v_p_2801_);
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_p_2801_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v___x_2894_; 
lean_inc(v_snd_2813_);
lean_inc(v_fst_2811_);
lean_dec_ref(v_p_2801_);
lean_inc(v_snd_2810_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_snd_2810_);
lean_ctor_set(v___x_2837_, 0, v_snd_2835_);
v___x_2894_ = v___x_2837_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_snd_2835_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_snd_2810_);
v___x_2894_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2913_; 
v_isSharedCheck_2913_ = !lean_is_exclusive(v_snd_2810_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; lean_object* v_unused_2915_; 
v_unused_2914_ = lean_ctor_get(v_snd_2810_, 1);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_snd_2810_, 0);
lean_dec(v_unused_2915_);
v___x_2896_ = v_snd_2810_;
v_isShared_2897_ = v_isSharedCheck_2913_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v_snd_2810_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2913_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2912_; 
v___x_2898_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2894_, v_a_2803_);
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2912_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2912_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_snd_2813_);
lean_ctor_set(v___x_2823_, 0, v_a_2899_);
v___x_2904_ = v___x_2823_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2899_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_snd_2813_);
v___x_2904_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2906_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 1, v___x_2904_);
lean_ctor_set(v___x_2896_, 0, v_fst_2811_);
v___x_2906_ = v___x_2896_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_fst_2811_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2906_);
v___x_2908_ = v___x_2901_;
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_del_object(v___x_2823_);
lean_dec(v_snd_2810_);
lean_dec_ref(v_p_2801_);
v_a_2918_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2832_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2832_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
else
{
lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2935_; 
lean_inc(v_snd_2816_);
lean_inc(v_fst_2811_);
lean_inc(v_snd_2809_);
lean_dec(v_fst_2815_);
lean_dec(v_fst_2814_);
lean_dec_ref(v_p_2801_);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_snd_2810_);
if (v_isSharedCheck_2935_ == 0)
{
lean_object* v_unused_2936_; lean_object* v_unused_2937_; 
v_unused_2936_ = lean_ctor_get(v_snd_2810_, 1);
lean_dec(v_unused_2936_);
v_unused_2937_ = lean_ctor_get(v_snd_2810_, 0);
lean_dec(v_unused_2937_);
v___x_2928_ = v_snd_2810_;
v_isShared_2929_ = v_isSharedCheck_2935_;
goto v_resetjp_2927_;
}
else
{
lean_dec(v_snd_2810_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2935_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v_values_2930_; lean_object* v___x_2932_; 
v_values_2930_ = lean_array_push(v_fst_2811_, v_snd_2816_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v_snd_2809_);
lean_ctor_set(v___x_2928_, 0, v_values_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_values_2930_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_snd_2809_);
v___x_2932_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
return v___x_2933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2938_, lean_object* v_entry_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2938_, v_entry_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2947_, lean_object* v_p_2948_, lean_object* v_entry_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2948_, v_entry_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2957_, lean_object* v_p_2958_, lean_object* v_entry_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2957_, v_p_2958_, v_entry_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2967_, lean_object* v_m_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2968_, v_a_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2971_, lean_object* v_m_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2971_, v_m_2972_, v_a_2973_);
lean_dec(v_a_2973_);
lean_dec_ref(v_m_2972_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2975_, lean_object* v_m_2976_, lean_object* v_a_2977_, lean_object* v_b_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2976_, v_a_2977_, v_b_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2980_, lean_object* v_a_2981_, lean_object* v_x_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2981_, v_x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2984_, lean_object* v_a_2985_, lean_object* v_x_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2984_, v_a_2985_, v_x_2986_);
lean_dec(v_x_2986_);
lean_dec(v_a_2985_);
return v_res_2987_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2988_, lean_object* v_a_2989_, lean_object* v_x_2990_){
_start:
{
uint8_t v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2989_, v_x_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2992_, lean_object* v_a_2993_, lean_object* v_x_2994_){
_start:
{
uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_res_2995_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2992_, v_a_2993_, v_x_2994_);
lean_dec(v_x_2994_);
lean_dec(v_a_2993_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2997_, lean_object* v_data_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3000_, lean_object* v_a_3001_, lean_object* v_b_3002_, lean_object* v_x_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3001_, v_b_3002_, v_x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3005_, lean_object* v_i_3006_, lean_object* v_source_3007_, lean_object* v_target_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3006_, v_source_3007_, v_target_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3010_, lean_object* v_x_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3011_, v_x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3014_, size_t v_i_3015_, size_t v_stop_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_usize_dec_eq(v_i_3015_, v_stop_3016_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_array_uget_borrowed(v_as_3014_, v_i_3015_);
lean_inc(v___x_3025_);
v___x_3026_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3017_, v___x_3025_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; size_t v___x_3028_; size_t v___x_3029_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = ((size_t)1ULL);
v___x_3029_ = lean_usize_add(v_i_3015_, v___x_3028_);
v_i_3015_ = v___x_3029_;
v_b_3017_ = v_a_3027_;
goto _start;
}
else
{
return v___x_3026_;
}
}
else
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_b_3017_);
return v___x_3031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3032_, lean_object* v_i_3033_, lean_object* v_stop_3034_, lean_object* v_b_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
size_t v_i_boxed_3042_; size_t v_stop_boxed_3043_; lean_object* v_res_3044_; 
v_i_boxed_3042_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_stop_boxed_3043_ = lean_unbox_usize(v_stop_3034_);
lean_dec(v_stop_3034_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3032_, v_i_boxed_3042_, v_stop_boxed_3043_, v_b_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v_as_3032_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3045_, lean_object* v_starIdx_3046_, lean_object* v_children_3047_, lean_object* v_entries_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v_starIdx_3046_);
lean_ctor_set(v___x_3055_, 1, v_children_3047_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v_values_3045_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_array_get_size(v_entries_3048_);
v___x_3059_ = lean_nat_dec_lt(v___x_3057_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3056_);
return v___x_3060_;
}
else
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_nat_dec_le(v___x_3058_, v___x_3058_);
if (v___x_3061_ == 0)
{
if (v___x_3059_ == 0)
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3056_);
return v___x_3062_;
}
else
{
size_t v___x_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = ((size_t)0ULL);
v___x_3064_ = lean_usize_of_nat(v___x_3058_);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3048_, v___x_3063_, v___x_3064_, v___x_3056_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
return v___x_3065_;
}
}
else
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((size_t)0ULL);
v___x_3067_ = lean_usize_of_nat(v___x_3058_);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3048_, v___x_3066_, v___x_3067_, v___x_3056_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3069_, lean_object* v_starIdx_3070_, lean_object* v_children_3071_, lean_object* v_entries_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3069_, v_starIdx_3070_, v_children_3071_, v_entries_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_entries_3072_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3080_, lean_object* v_values_3081_, lean_object* v_starIdx_3082_, lean_object* v_children_3083_, lean_object* v_entries_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3081_, v_starIdx_3082_, v_children_3083_, v_entries_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3092_, lean_object* v_values_3093_, lean_object* v_starIdx_3094_, lean_object* v_children_3095_, lean_object* v_entries_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3092_, v_values_3093_, v_starIdx_3094_, v_children_3095_, v_entries_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_entries_3096_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3104_, lean_object* v_as_3105_, size_t v_i_3106_, size_t v_stop_3107_, lean_object* v_b_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3105_, v_i_3106_, v_stop_3107_, v_b_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_as_3117_, lean_object* v_i_3118_, lean_object* v_stop_3119_, lean_object* v_b_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
size_t v_i_boxed_3127_; size_t v_stop_boxed_3128_; lean_object* v_res_3129_; 
v_i_boxed_3127_ = lean_unbox_usize(v_i_3118_);
lean_dec(v_i_3118_);
v_stop_boxed_3128_ = lean_unbox_usize(v_stop_3119_);
lean_dec(v_stop_3119_);
v_res_3129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3116_, v_as_3117_, v_i_boxed_3127_, v_stop_boxed_3128_, v_b_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v_as_3117_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v_values_3140_; lean_object* v_star_3141_; lean_object* v_children_3142_; lean_object* v_pending_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3173_; 
v___x_3137_ = lean_st_ref_get(v_a_3131_);
v___x_3138_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3139_ = lean_array_get(v___x_3138_, v___x_3137_, v_c_3130_);
lean_dec(v___x_3137_);
v_values_3140_ = lean_ctor_get(v___x_3139_, 0);
v_star_3141_ = lean_ctor_get(v___x_3139_, 1);
v_children_3142_ = lean_ctor_get(v___x_3139_, 2);
v_pending_3143_ = lean_ctor_get(v___x_3139_, 3);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3145_ = v___x_3139_;
v_isShared_3146_ = v_isSharedCheck_3173_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_pending_3143_);
lean_inc(v_children_3142_);
lean_inc(v_star_3141_);
lean_inc(v_values_3140_);
lean_dec(v___x_3139_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3173_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v___x_3147_ = lean_array_get_size(v_pending_3143_);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = lean_nat_dec_eq(v___x_3147_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3130_, v___x_3138_, v_a_3131_);
lean_dec_ref(v___x_3150_);
v___x_3151_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3140_, v_star_3141_, v_children_3142_, v_pending_3143_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec_ref(v_pending_3143_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v_snd_3153_; lean_object* v_fst_3154_; lean_object* v_fst_3155_; lean_object* v_snd_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v_snd_3153_ = lean_ctor_get(v_a_3152_, 1);
v_fst_3154_ = lean_ctor_get(v_a_3152_, 0);
v_fst_3155_ = lean_ctor_get(v_snd_3153_, 0);
v_snd_3156_ = lean_ctor_get(v_snd_3153_, 1);
v___x_3157_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
lean_inc(v_snd_3156_);
lean_inc(v_fst_3155_);
lean_inc(v_fst_3154_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 3, v___x_3157_);
lean_ctor_set(v___x_3145_, 2, v_snd_3156_);
lean_ctor_set(v___x_3145_, 1, v_fst_3155_);
lean_ctor_set(v___x_3145_, 0, v_fst_3154_);
v___x_3159_ = v___x_3145_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_fst_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_fst_3155_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_snd_3156_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v___x_3160_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3130_, v___x_3159_, v_a_3131_);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v___x_3160_, 0);
lean_dec(v_unused_3168_);
v___x_3162_ = v___x_3160_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_dec(v___x_3160_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v_a_3152_);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3152_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_del_object(v___x_3145_);
return v___x_3151_;
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
lean_del_object(v___x_3145_);
lean_dec_ref(v_pending_3143_);
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_star_3141_);
lean_ctor_set(v___x_3170_, 1, v_children_3142_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v_values_3140_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec(v_c_3174_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3182_, lean_object* v_c_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3191_, lean_object* v_c_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3191_, v_c_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec(v_c_3192_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3200_, lean_object* v_fallback_3201_, lean_object* v_x_3202_){
_start:
{
if (lean_obj_tag(v_x_3202_) == 0)
{
lean_inc(v_fallback_3201_);
return v_fallback_3201_;
}
else
{
lean_object* v_key_3203_; lean_object* v_value_3204_; lean_object* v_tail_3205_; uint8_t v___x_3206_; 
v_key_3203_ = lean_ctor_get(v_x_3202_, 0);
v_value_3204_ = lean_ctor_get(v_x_3202_, 1);
v_tail_3205_ = lean_ctor_get(v_x_3202_, 2);
v___x_3206_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3203_, v_a_3200_);
if (v___x_3206_ == 0)
{
v_x_3202_ = v_tail_3205_;
goto _start;
}
else
{
lean_inc(v_value_3204_);
return v_value_3204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3208_, lean_object* v_fallback_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3208_, v_fallback_3209_, v_x_3210_);
lean_dec(v_x_3210_);
lean_dec(v_fallback_3209_);
lean_dec(v_a_3208_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3212_, lean_object* v_a_3213_, lean_object* v_fallback_3214_){
_start:
{
lean_object* v_buckets_3215_; lean_object* v___x_3216_; uint64_t v___x_3217_; uint64_t v___x_3218_; uint64_t v___x_3219_; uint64_t v_fold_3220_; uint64_t v___x_3221_; uint64_t v___x_3222_; uint64_t v___x_3223_; size_t v___x_3224_; size_t v___x_3225_; size_t v___x_3226_; size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v_buckets_3215_ = lean_ctor_get(v_m_3212_, 1);
v___x_3216_ = lean_array_get_size(v_buckets_3215_);
v___x_3217_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3213_);
v___x_3218_ = 32ULL;
v___x_3219_ = lean_uint64_shift_right(v___x_3217_, v___x_3218_);
v_fold_3220_ = lean_uint64_xor(v___x_3217_, v___x_3219_);
v___x_3221_ = 16ULL;
v___x_3222_ = lean_uint64_shift_right(v_fold_3220_, v___x_3221_);
v___x_3223_ = lean_uint64_xor(v_fold_3220_, v___x_3222_);
v___x_3224_ = lean_uint64_to_usize(v___x_3223_);
v___x_3225_ = lean_usize_of_nat(v___x_3216_);
v___x_3226_ = ((size_t)1ULL);
v___x_3227_ = lean_usize_sub(v___x_3225_, v___x_3226_);
v___x_3228_ = lean_usize_land(v___x_3224_, v___x_3227_);
v___x_3229_ = lean_array_uget_borrowed(v_buckets_3215_, v___x_3228_);
v___x_3230_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3213_, v_fallback_3214_, v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3231_, lean_object* v_a_3232_, lean_object* v_fallback_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3231_, v_a_3232_, v_fallback_3233_);
lean_dec(v_fallback_3233_);
lean_dec(v_a_3232_);
lean_dec_ref(v_m_3231_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3235_, lean_object* v_rest_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = lean_nat_dec_eq(v_next_3235_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3235_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3271_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3248_ = v___x_3245_;
v_isShared_3249_ = v_isSharedCheck_3271_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3271_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v_snd_3250_; 
v_snd_3250_ = lean_ctor_get(v_a_3246_, 1);
lean_inc(v_snd_3250_);
lean_dec(v_a_3246_);
if (lean_obj_tag(v_rest_3236_) == 0)
{
lean_object* v_fst_3251_; lean_object* v_snd_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v_fst_3251_ = lean_ctor_get(v_snd_3250_, 0);
lean_inc(v_fst_3251_);
v_snd_3252_ = lean_ctor_get(v_snd_3250_, 1);
lean_inc(v_snd_3252_);
lean_dec(v_snd_3250_);
v___x_3253_ = lean_st_ref_take(v_a_3237_);
v___x_3254_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v_fst_3251_);
lean_ctor_set(v___x_3255_, 2, v_snd_3252_);
lean_ctor_set(v___x_3255_, 3, v___x_3254_);
v___x_3256_ = lean_array_set(v___x_3253_, v_next_3235_, v___x_3255_);
lean_dec(v_next_3235_);
v___x_3257_ = lean_st_ref_put(v_a_3237_, v___x_3256_);
v___x_3258_ = lean_box(0);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v___x_3258_);
v___x_3260_ = v___x_3248_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
else
{
lean_object* v_fst_3262_; lean_object* v_snd_3263_; lean_object* v_head_3264_; lean_object* v_tail_3265_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
lean_del_object(v___x_3248_);
lean_dec(v_next_3235_);
v_fst_3262_ = lean_ctor_get(v_snd_3250_, 0);
lean_inc(v_fst_3262_);
v_snd_3263_ = lean_ctor_get(v_snd_3250_, 1);
lean_inc(v_snd_3263_);
lean_dec(v_snd_3250_);
v_head_3264_ = lean_ctor_get(v_rest_3236_, 0);
v_tail_3265_ = lean_ctor_get(v_rest_3236_, 1);
v___x_3266_ = lean_box(3);
v___x_3267_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3264_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
lean_dec(v_fst_3262_);
v___x_3268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3263_, v_head_3264_, v___x_3243_);
lean_dec(v_snd_3263_);
v_next_3235_ = v___x_3268_;
v_rest_3236_ = v_tail_3265_;
goto _start;
}
else
{
lean_dec(v_snd_3263_);
v_next_3235_ = v_fst_3262_;
v_rest_3236_ = v_tail_3265_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec(v_next_3235_);
v_a_3272_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3245_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3245_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec(v_next_3235_);
v___x_3280_ = lean_box(0);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3282_, lean_object* v_rest_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3282_, v_rest_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_rest_3283_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3291_, lean_object* v_next_3292_, lean_object* v_rest_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3292_, v_rest_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3301_, lean_object* v_next_3302_, lean_object* v_rest_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3301_, v_next_3302_, v_rest_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec(v_rest_3303_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3311_, lean_object* v_m_3312_, lean_object* v_a_3313_, lean_object* v_fallback_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3312_, v_a_3313_, v_fallback_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3316_, lean_object* v_m_3317_, lean_object* v_a_3318_, lean_object* v_fallback_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3316_, v_m_3317_, v_a_3318_, v_fallback_3319_);
lean_dec(v_fallback_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_m_3317_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3321_, lean_object* v_a_3322_, lean_object* v_fallback_3323_, lean_object* v_x_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3322_, v_fallback_3323_, v_x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3326_, lean_object* v_a_3327_, lean_object* v_fallback_3328_, lean_object* v_x_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3326_, v_a_3327_, v_fallback_3328_, v_x_3329_);
lean_dec(v_x_3329_);
lean_dec(v_fallback_3328_);
lean_dec(v_a_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3331_, lean_object* v_path_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_){
_start:
{
if (lean_obj_tag(v_path_3332_) == 0)
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_t_3331_);
return v___x_3338_;
}
else
{
lean_object* v_head_3339_; lean_object* v_tail_3340_; lean_object* v_roots_3341_; lean_object* v___x_3342_; lean_object* v_idx_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_head_3339_ = lean_ctor_get(v_path_3332_, 0);
lean_inc(v_head_3339_);
v_tail_3340_ = lean_ctor_get(v_path_3332_, 1);
lean_inc(v_tail_3340_);
lean_dec_ref_known(v_path_3332_, 2);
v_roots_3341_ = lean_ctor_get(v_t_3331_, 1);
v___x_3342_ = lean_unsigned_to_nat(0u);
v_idx_3343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3341_, v_head_3339_, v___x_3342_);
lean_dec(v_head_3339_);
v___x_3344_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3344_, 0, lean_box(0));
lean_closure_set(v___x_3344_, 1, v_idx_3343_);
lean_closure_set(v___x_3344_, 2, v_tail_3340_);
v___x_3345_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3331_, v___x_3344_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3354_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3354_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3354_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v_snd_3350_; lean_object* v___x_3352_; 
v_snd_3350_ = lean_ctor_get(v_a_3346_, 1);
lean_inc(v_snd_3350_);
lean_dec(v_a_3346_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_snd_3350_);
v___x_3352_ = v___x_3348_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_snd_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
v_a_3355_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3345_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3345_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3363_, lean_object* v_path_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3363_, v_path_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3371_, lean_object* v_t_3372_, lean_object* v_path_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3372_, v_path_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_t_3381_, lean_object* v_path_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3380_, v_t_3381_, v_path_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3391_, lean_object* v_e_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3394_ = lean_array_get_size(v_a_3393_);
v___x_3395_ = lean_nat_dec_lt(v___x_3394_, v_score_3391_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3396_ = lean_unsigned_to_nat(1u);
v___x_3397_ = lean_mk_empty_array_with_capacity(v___x_3396_);
v___x_3398_ = lean_array_push(v___x_3397_, v_e_3392_);
v___x_3399_ = lean_array_push(v_a_3393_, v___x_3398_);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3401_ = lean_array_push(v_a_3393_, v___x_3400_);
v_a_3393_ = v___x_3401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3403_, lean_object* v_e_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3403_, v_e_3404_, v_a_3405_);
lean_dec(v_score_3403_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3407_, lean_object* v_score_3408_, lean_object* v_e_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3408_, v_e_3409_, v_a_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3412_, lean_object* v_score_3413_, lean_object* v_e_3414_, lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3412_, v_score_3413_, v_e_3414_, v_a_3415_);
lean_dec(v_score_3413_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3417_, lean_object* v_score_3418_, lean_object* v_e_3419_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3420_ = lean_array_get_size(v_e_3419_);
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = lean_nat_dec_eq(v___x_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3423_ = lean_array_get_size(v_r_3417_);
v___x_3424_ = lean_nat_dec_lt(v_score_3418_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
v___x_3425_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3418_, v_e_3419_, v_r_3417_);
return v___x_3425_;
}
else
{
if (v___x_3424_ == 0)
{
lean_dec_ref(v_e_3419_);
return v_r_3417_;
}
else
{
lean_object* v_v_3426_; lean_object* v___x_3427_; lean_object* v_xs_x27_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_v_3426_ = lean_array_fget(v_r_3417_, v_score_3418_);
v___x_3427_ = lean_box(0);
v_xs_x27_3428_ = lean_array_fset(v_r_3417_, v_score_3418_, v___x_3427_);
v___x_3429_ = lean_array_push(v_v_3426_, v_e_3419_);
v___x_3430_ = lean_array_fset(v_xs_x27_3428_, v_score_3418_, v___x_3429_);
return v___x_3430_;
}
}
}
else
{
lean_dec_ref(v_e_3419_);
return v_r_3417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3431_, lean_object* v_score_3432_, lean_object* v_e_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3431_, v_score_3432_, v_e_3433_);
lean_dec(v_score_3432_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3435_, lean_object* v_r_3436_, lean_object* v_score_3437_, lean_object* v_e_3438_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3436_, v_score_3437_, v_e_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3440_, lean_object* v_r_3441_, lean_object* v_score_3442_, lean_object* v_e_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3440_, v_r_3441_, v_score_3442_, v_e_3443_);
lean_dec(v_score_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3445_, size_t v_i_3446_, size_t v_stop_3447_, lean_object* v_b_3448_){
_start:
{
uint8_t v___x_3449_; 
v___x_3449_ = lean_usize_dec_eq(v_i_3446_, v_stop_3447_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; size_t v___x_3453_; size_t v___x_3454_; 
v___x_3450_ = lean_array_uget_borrowed(v_as_3445_, v_i_3446_);
v___x_3451_ = lean_array_get_size(v___x_3450_);
v___x_3452_ = lean_nat_add(v_b_3448_, v___x_3451_);
lean_dec(v_b_3448_);
v___x_3453_ = ((size_t)1ULL);
v___x_3454_ = lean_usize_add(v_i_3446_, v___x_3453_);
v_i_3446_ = v___x_3454_;
v_b_3448_ = v___x_3452_;
goto _start;
}
else
{
return v_b_3448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3456_, lean_object* v_i_3457_, lean_object* v_stop_3458_, lean_object* v_b_3459_){
_start:
{
size_t v_i_boxed_3460_; size_t v_stop_boxed_3461_; lean_object* v_res_3462_; 
v_i_boxed_3460_ = lean_unbox_usize(v_i_3457_);
lean_dec(v_i_3457_);
v_stop_boxed_3461_ = lean_unbox_usize(v_stop_3458_);
lean_dec(v_stop_3458_);
v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3456_, v_i_boxed_3460_, v_stop_boxed_3461_, v_b_3459_);
lean_dec_ref(v_as_3456_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3463_, size_t v_i_3464_, size_t v_stop_3465_, lean_object* v_b_3466_){
_start:
{
lean_object* v___y_3468_; uint8_t v___x_3472_; 
v___x_3472_ = lean_usize_dec_eq(v_i_3464_, v_stop_3465_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3473_ = lean_array_uget_borrowed(v_as_3463_, v_i_3464_);
v___x_3474_ = lean_unsigned_to_nat(0u);
v___x_3475_ = lean_array_get_size(v___x_3473_);
v___x_3476_ = lean_nat_dec_lt(v___x_3474_, v___x_3475_);
if (v___x_3476_ == 0)
{
v___y_3468_ = v_b_3466_;
goto v___jp_3467_;
}
else
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_nat_dec_le(v___x_3475_, v___x_3475_);
if (v___x_3477_ == 0)
{
if (v___x_3476_ == 0)
{
v___y_3468_ = v_b_3466_;
goto v___jp_3467_;
}
else
{
size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = ((size_t)0ULL);
v___x_3479_ = lean_usize_of_nat(v___x_3475_);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3473_, v___x_3478_, v___x_3479_, v_b_3466_);
v___y_3468_ = v___x_3480_;
goto v___jp_3467_;
}
}
else
{
size_t v___x_3481_; size_t v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((size_t)0ULL);
v___x_3482_ = lean_usize_of_nat(v___x_3475_);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3473_, v___x_3481_, v___x_3482_, v_b_3466_);
v___y_3468_ = v___x_3483_;
goto v___jp_3467_;
}
}
}
else
{
return v_b_3466_;
}
v___jp_3467_:
{
size_t v___x_3469_; size_t v___x_3470_; 
v___x_3469_ = ((size_t)1ULL);
v___x_3470_ = lean_usize_add(v_i_3464_, v___x_3469_);
v_i_3464_ = v___x_3470_;
v_b_3466_ = v___y_3468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3484_, lean_object* v_i_3485_, lean_object* v_stop_3486_, lean_object* v_b_3487_){
_start:
{
size_t v_i_boxed_3488_; size_t v_stop_boxed_3489_; lean_object* v_res_3490_; 
v_i_boxed_3488_ = lean_unbox_usize(v_i_3485_);
lean_dec(v_i_3485_);
v_stop_boxed_3489_ = lean_unbox_usize(v_stop_3486_);
lean_dec(v_stop_3486_);
v_res_3490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3484_, v_i_boxed_3488_, v_stop_boxed_3489_, v_b_3487_);
lean_dec_ref(v_as_3484_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3491_){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3492_ = lean_unsigned_to_nat(0u);
v___x_3493_ = lean_array_get_size(v_mr_3491_);
v___x_3494_ = lean_nat_dec_lt(v___x_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
return v___x_3492_;
}
else
{
uint8_t v___x_3495_; 
v___x_3495_ = lean_nat_dec_le(v___x_3493_, v___x_3493_);
if (v___x_3495_ == 0)
{
if (v___x_3494_ == 0)
{
return v___x_3492_;
}
else
{
size_t v___x_3496_; size_t v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = ((size_t)0ULL);
v___x_3497_ = lean_usize_of_nat(v___x_3493_);
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3491_, v___x_3496_, v___x_3497_, v___x_3492_);
return v___x_3498_;
}
}
else
{
size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = lean_usize_of_nat(v___x_3493_);
v___x_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3491_, v___x_3499_, v___x_3500_, v___x_3492_);
return v___x_3501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3502_);
lean_dec_ref(v_mr_3502_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3504_, lean_object* v_mr_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3507_, lean_object* v_mr_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3507_, v_mr_3508_);
lean_dec_ref(v_mr_3508_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3510_, lean_object* v_as_3511_, size_t v_i_3512_, size_t v_stop_3513_, lean_object* v_b_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3511_, v_i_3512_, v_stop_3513_, v_b_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3516_, lean_object* v_as_3517_, lean_object* v_i_3518_, lean_object* v_stop_3519_, lean_object* v_b_3520_){
_start:
{
size_t v_i_boxed_3521_; size_t v_stop_boxed_3522_; lean_object* v_res_3523_; 
v_i_boxed_3521_ = lean_unbox_usize(v_i_3518_);
lean_dec(v_i_3518_);
v_stop_boxed_3522_ = lean_unbox_usize(v_stop_3519_);
lean_dec(v_stop_3519_);
v_res_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3516_, v_as_3517_, v_i_boxed_3521_, v_stop_boxed_3522_, v_b_3520_);
lean_dec_ref(v_as_3517_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3524_, lean_object* v_as_3525_, size_t v_i_3526_, size_t v_stop_3527_, lean_object* v_b_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3525_, v_i_3526_, v_stop_3527_, v_b_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3530_, lean_object* v_as_3531_, lean_object* v_i_3532_, lean_object* v_stop_3533_, lean_object* v_b_3534_){
_start:
{
size_t v_i_boxed_3535_; size_t v_stop_boxed_3536_; lean_object* v_res_3537_; 
v_i_boxed_3535_ = lean_unbox_usize(v_i_3532_);
lean_dec(v_i_3532_);
v_stop_boxed_3536_ = lean_unbox_usize(v_stop_3533_);
lean_dec(v_stop_3533_);
v_res_3537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3530_, v_as_3531_, v_i_boxed_3535_, v_stop_boxed_3536_, v_b_3534_);
lean_dec_ref(v_as_3531_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3538_, lean_object* v_j_3539_, lean_object* v_x_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_apply_2(v_f_3538_, v_j_3539_, v_x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3561_, lean_object* v_x1_3562_, lean_object* v_x2_3563_){
_start:
{
lean_object* v___x_3564_; size_t v_sz_3565_; size_t v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3564_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3565_ = lean_array_size(v_x2_3563_);
v___x_3566_ = ((size_t)0ULL);
v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3564_, v___f_3561_, v_sz_3565_, v___x_3566_, v_x2_3563_);
v___x_3568_ = l_Array_append___redArg(v_x1_3562_, v___x_3567_);
lean_dec(v___x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3569_, lean_object* v_mr_3570_, lean_object* v_f_3571_, lean_object* v_i_3572_, lean_object* v_x_3573_, lean_object* v_r_3574_){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v_j_3577_; lean_object* v_b_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3575_ = lean_unsigned_to_nat(1u);
v___x_3576_ = lean_nat_sub(v_n_3569_, v___x_3575_);
v_j_3577_ = lean_nat_sub(v___x_3576_, v_i_3572_);
lean_dec(v___x_3576_);
v_b_3578_ = lean_array_fget_borrowed(v_mr_3570_, v_j_3577_);
v___x_3579_ = lean_unsigned_to_nat(0u);
v___x_3580_ = lean_array_get_size(v_b_3578_);
v___x_3581_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3582_ = lean_nat_dec_lt(v___x_3579_, v___x_3580_);
if (v___x_3582_ == 0)
{
lean_dec(v_j_3577_);
lean_dec(v_f_3571_);
return v_r_3574_;
}
else
{
lean_object* v___f_3583_; lean_object* v___f_3584_; uint8_t v___x_3585_; 
v___f_3583_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3583_, 0, v_f_3571_);
lean_closure_set(v___f_3583_, 1, v_j_3577_);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3584_, 0, v___f_3583_);
v___x_3585_ = lean_nat_dec_le(v___x_3580_, v___x_3580_);
if (v___x_3585_ == 0)
{
if (v___x_3582_ == 0)
{
lean_dec_ref(v___f_3584_);
return v_r_3574_;
}
else
{
size_t v___x_3586_; size_t v___x_3587_; lean_object* v___x_3588_; 
v___x_3586_ = ((size_t)0ULL);
v___x_3587_ = lean_usize_of_nat(v___x_3580_);
lean_inc(v_b_3578_);
v___x_3588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3581_, v___f_3584_, v_b_3578_, v___x_3586_, v___x_3587_, v_r_3574_);
return v___x_3588_;
}
}
else
{
size_t v___x_3589_; size_t v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = ((size_t)0ULL);
v___x_3590_ = lean_usize_of_nat(v___x_3580_);
lean_inc(v_b_3578_);
v___x_3591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3581_, v___f_3584_, v_b_3578_, v___x_3589_, v___x_3590_, v_r_3574_);
return v___x_3591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3592_, lean_object* v_mr_3593_, lean_object* v_f_3594_, lean_object* v_i_3595_, lean_object* v_x_3596_, lean_object* v_r_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3592_, v_mr_3593_, v_f_3594_, v_i_3595_, v_x_3596_, v_r_3597_);
lean_dec(v_i_3595_);
lean_dec_ref(v_mr_3593_);
lean_dec(v_n_3592_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3599_, lean_object* v_a_3600_, lean_object* v_f_3601_){
_start:
{
lean_object* v_n_3602_; lean_object* v___f_3603_; lean_object* v___x_3604_; 
v_n_3602_ = lean_array_get_size(v_mr_3599_);
v___f_3603_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3603_, 0, v_n_3602_);
lean_closure_set(v___f_3603_, 1, v_mr_3599_);
lean_closure_set(v___f_3603_, 2, v_f_3601_);
v___x_3604_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3602_, v___f_3603_, v_n_3602_, lean_box(0), v_a_3600_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3605_, lean_object* v_00_u03b2_3606_, lean_object* v_mr_3607_, lean_object* v_a_3608_, lean_object* v_f_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3607_, v_a_3608_, v_f_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3611_, size_t v_i_3612_, lean_object* v_bs_3613_){
_start:
{
uint8_t v___x_3614_; 
v___x_3614_ = lean_usize_dec_lt(v_i_3612_, v_sz_3611_);
if (v___x_3614_ == 0)
{
return v_bs_3613_;
}
else
{
lean_object* v_v_3615_; lean_object* v___x_3616_; lean_object* v_bs_x27_3617_; size_t v___x_3618_; size_t v___x_3619_; lean_object* v___x_3620_; 
v_v_3615_ = lean_array_uget(v_bs_3613_, v_i_3612_);
v___x_3616_ = lean_unsigned_to_nat(0u);
v_bs_x27_3617_ = lean_array_uset(v_bs_3613_, v_i_3612_, v___x_3616_);
v___x_3618_ = ((size_t)1ULL);
v___x_3619_ = lean_usize_add(v_i_3612_, v___x_3618_);
v___x_3620_ = lean_array_uset(v_bs_x27_3617_, v_i_3612_, v_v_3615_);
v_i_3612_ = v___x_3619_;
v_bs_3613_ = v___x_3620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3622_, lean_object* v_i_3623_, lean_object* v_bs_3624_){
_start:
{
size_t v_sz_boxed_3625_; size_t v_i_boxed_3626_; lean_object* v_res_3627_; 
v_sz_boxed_3625_ = lean_unbox_usize(v_sz_3622_);
lean_dec(v_sz_3622_);
v_i_boxed_3626_ = lean_unbox_usize(v_i_3623_);
lean_dec(v_i_3623_);
v_res_3627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3625_, v_i_boxed_3626_, v_bs_3624_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3628_, size_t v_i_3629_, size_t v_stop_3630_, lean_object* v_b_3631_){
_start:
{
uint8_t v___x_3632_; 
v___x_3632_ = lean_usize_dec_eq(v_i_3629_, v_stop_3630_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; size_t v_sz_3634_; size_t v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; 
v___x_3633_ = lean_array_uget_borrowed(v_as_3628_, v_i_3629_);
v_sz_3634_ = lean_array_size(v___x_3633_);
v___x_3635_ = ((size_t)0ULL);
lean_inc(v___x_3633_);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3634_, v___x_3635_, v___x_3633_);
v___x_3637_ = l_Array_append___redArg(v_b_3631_, v___x_3636_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = ((size_t)1ULL);
v___x_3639_ = lean_usize_add(v_i_3629_, v___x_3638_);
v_i_3629_ = v___x_3639_;
v_b_3631_ = v___x_3637_;
goto _start;
}
else
{
return v_b_3631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3641_, lean_object* v_i_3642_, lean_object* v_stop_3643_, lean_object* v_b_3644_){
_start:
{
size_t v_i_boxed_3645_; size_t v_stop_boxed_3646_; lean_object* v_res_3647_; 
v_i_boxed_3645_ = lean_unbox_usize(v_i_3642_);
lean_dec(v_i_3642_);
v_stop_boxed_3646_ = lean_unbox_usize(v_stop_3643_);
lean_dec(v_stop_3643_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3641_, v_i_boxed_3645_, v_stop_boxed_3646_, v_b_3644_);
lean_dec_ref(v_as_3641_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3648_, lean_object* v_aa_3649_, lean_object* v_n_3650_, lean_object* v_j_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_zero_3653_; uint8_t v_isZero_3654_; 
v_zero_3653_ = lean_unsigned_to_nat(0u);
v_isZero_3654_ = lean_nat_dec_eq(v_j_3651_, v_zero_3653_);
if (v_isZero_3654_ == 1)
{
lean_dec(v_j_3651_);
return v_a_3652_;
}
else
{
lean_object* v_one_3655_; lean_object* v_n_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_j_3659_; lean_object* v_b_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v_one_3655_ = lean_unsigned_to_nat(1u);
v_n_3656_ = lean_nat_sub(v_j_3651_, v_one_3655_);
v___x_3657_ = lean_nat_sub(v_n_3650_, v_j_3651_);
lean_dec(v_j_3651_);
v___x_3658_ = lean_nat_sub(v_n_3648_, v_one_3655_);
v_j_3659_ = lean_nat_sub(v___x_3658_, v___x_3657_);
lean_dec(v___x_3657_);
lean_dec(v___x_3658_);
v_b_3660_ = lean_array_fget_borrowed(v_aa_3649_, v_j_3659_);
lean_dec(v_j_3659_);
v___x_3661_ = lean_array_get_size(v_b_3660_);
v___x_3662_ = lean_nat_dec_lt(v_zero_3653_, v___x_3661_);
if (v___x_3662_ == 0)
{
v_j_3651_ = v_n_3656_;
goto _start;
}
else
{
size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = ((size_t)0ULL);
v___x_3665_ = lean_usize_of_nat(v___x_3661_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3660_, v___x_3664_, v___x_3665_, v_a_3652_);
v_j_3651_ = v_n_3656_;
v_a_3652_ = v___x_3666_;
goto _start;
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
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v_ca_3787_; lean_object* v_todo_3788_; lean_object* v_score_3789_; lean_object* v_c_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3855_; 
v___x_3784_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3785_ = lean_unsigned_to_nat(1u);
v___x_3786_ = lean_nat_sub(v___x_3781_, v___x_3785_);
v_ca_3787_ = lean_array_get(v___x_3784_, v_cases_3773_, v___x_3786_);
lean_dec(v___x_3786_);
v_todo_3788_ = lean_ctor_get(v_ca_3787_, 0);
v_score_3789_ = lean_ctor_get(v_ca_3787_, 1);
v_c_3790_ = lean_ctor_get(v_ca_3787_, 2);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_ca_3787_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3792_ = v_ca_3787_;
v_isShared_3793_ = v_isSharedCheck_3855_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_c_3790_);
lean_inc(v_score_3789_);
lean_inc(v_todo_3788_);
lean_dec(v_ca_3787_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3855_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3790_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_c_3790_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; uint8_t v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v_snd_3823_; lean_object* v_fst_3824_; lean_object* v_fst_3825_; lean_object* v_snd_3826_; lean_object* v_cases_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
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
v___x_3829_ = lean_nat_dec_eq(v___x_3828_, v___x_3782_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; uint8_t v___x_3831_; uint8_t v___y_3833_; 
lean_dec(v_fst_3824_);
v___x_3830_ = l_Lean_instInhabitedExpr;
v___x_3831_ = lean_nat_dec_eq(v_fst_3825_, v___x_3782_);
if (v___x_3831_ == 0)
{
v___y_3833_ = v___x_3829_;
goto v___jp_3832_;
}
else
{
lean_object* v_size_3842_; uint8_t v___x_3843_; 
v_size_3842_ = lean_ctor_get(v_snd_3826_, 0);
v___x_3843_ = lean_nat_dec_eq(v_size_3842_, v___x_3782_);
if (v___x_3843_ == 0)
{
v___y_3833_ = v___x_3843_;
goto v___jp_3832_;
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
v___jp_3832_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___f_3837_; 
v___x_3834_ = lean_nat_sub(v___x_3828_, v___x_3785_);
v___x_3835_ = lean_array_get(v___x_3830_, v_todo_3788_, v___x_3834_);
lean_dec(v___x_3834_);
v___x_3836_ = lean_array_pop(v_todo_3788_);
lean_inc(v_score_3789_);
lean_inc_ref(v___x_3836_);
v___f_3837_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3837_, 0, v_snd_3826_);
lean_closure_set(v___f_3837_, 1, v___x_3836_);
lean_closure_set(v___f_3837_, 2, v_score_3789_);
lean_closure_set(v___f_3837_, 3, v___x_3785_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3839_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 2, v_fst_3825_);
lean_ctor_set(v___x_3792_, 0, v___x_3836_);
v___x_3839_ = v___x_3792_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_score_3789_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v_fst_3825_);
v___x_3839_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_array_push(v_cases_3827_, v___x_3839_);
v___y_3797_ = v___y_3833_;
v___y_3798_ = v___f_3837_;
v___y_3799_ = v___x_3835_;
v___y_3800_ = v___x_3840_;
goto v___jp_3796_;
}
}
else
{
lean_dec_ref(v___x_3836_);
lean_dec(v_fst_3825_);
lean_del_object(v___x_3792_);
lean_dec(v_score_3789_);
v___y_3797_ = v___y_3833_;
v___y_3798_ = v___f_3837_;
v___y_3799_ = v___x_3835_;
v___y_3800_ = v_cases_3827_;
goto v___jp_3796_;
}
}
}
else
{
lean_object* v___x_3845_; 
lean_dec(v_snd_3826_);
lean_dec(v_fst_3825_);
lean_del_object(v___x_3792_);
lean_dec_ref(v_todo_3788_);
v___x_3845_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3774_, v_score_3789_, v_fst_3824_);
lean_dec(v_score_3789_);
v_cases_3773_ = v_cases_3827_;
v_result_3774_ = v___x_3845_;
goto _start;
}
v___jp_3796_:
{
uint8_t v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = 1;
v___x_3802_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3799_, v___x_3801_, v___y_3797_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
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
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_del_object(v___x_3792_);
lean_dec(v_score_3789_);
lean_dec_ref(v_todo_3788_);
lean_dec_ref(v_result_3774_);
lean_dec_ref(v_cases_3773_);
v_a_3847_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3794_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3794_);
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
}
else
{
lean_object* v___x_3856_; 
lean_dec_ref(v_cases_3773_);
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_result_3774_);
return v___x_3856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3857_, lean_object* v_result_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3857_, v_result_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3866_, lean_object* v_cases_3867_, lean_object* v_result_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3867_, v_result_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3876_, lean_object* v_cases_3877_, lean_object* v_result_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3876_, v_cases_3877_, v_result_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = lean_box(3);
v___x_3896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3888_, v___x_3895_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3900_; 
v_val_3899_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3900_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3899_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
lean_dec(v_val_3899_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3912_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3912_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3912_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v_fst_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
v_fst_3905_ = lean_ctor_get(v_a_3901_, 0);
lean_inc(v_fst_3905_);
lean_dec(v_a_3901_);
v___x_3906_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3907_ = lean_unsigned_to_nat(1u);
v___x_3908_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3906_, v___x_3907_, v_fst_3905_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3908_);
v___x_3910_ = v___x_3903_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
v_a_3913_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3900_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3900_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_root_3921_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3929_, lean_object* v_root_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3938_, lean_object* v_root_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3938_, v_root_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_root_3939_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3947_, lean_object* v_k_3948_, lean_object* v_args_3949_, lean_object* v_cases_3950_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3947_, v_k_3948_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_dec_ref(v_args_3949_);
return v_cases_3950_;
}
else
{
lean_object* v_val_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_val_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_val_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3954_, 0, v_args_3949_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
lean_ctor_set(v___x_3954_, 2, v_val_3952_);
v___x_3955_ = lean_array_push(v_cases_3950_, v___x_3954_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3956_, lean_object* v_k_3957_, lean_object* v_args_3958_, lean_object* v_cases_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3956_, v_k_3957_, v_args_3958_, v_cases_3959_);
lean_dec(v_k_3957_);
lean_dec_ref(v_r_3956_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3963_, lean_object* v_e_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3963_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref_known(v___x_3971_, 1);
v___x_3973_ = 1;
v___x_3974_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3964_, v___x_3973_, v___x_3973_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v_fst_3976_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v_fst_3976_ = lean_ctor_get(v_a_3975_, 0);
lean_inc(v_fst_3976_);
switch(lean_obj_tag(v_fst_3976_))
{
case 3:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec(v_a_3975_);
v___x_3977_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3978_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3977_, v_a_3972_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
return v___x_3978_;
}
case 5:
{
lean_object* v_snd_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_snd_3979_ = lean_ctor_get(v_a_3975_, 1);
lean_inc(v_snd_3979_);
lean_dec(v_a_3975_);
v___x_3980_ = lean_box(4);
v___x_3981_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3982_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3963_, v___x_3980_, v___x_3981_, v___x_3981_);
v___x_3983_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3963_, v_fst_3976_, v_snd_3979_, v___x_3982_);
v___x_3984_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3983_, v_a_3972_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
return v___x_3984_;
}
default: 
{
lean_object* v_snd_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_snd_3985_ = lean_ctor_get(v_a_3975_, 1);
lean_inc(v_snd_3985_);
lean_dec(v_a_3975_);
v___x_3986_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3987_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3963_, v_fst_3976_, v_snd_3985_, v___x_3986_);
lean_dec(v_fst_3976_);
v___x_3988_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3987_, v_a_3972_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
return v___x_3988_;
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_dec(v_a_3972_);
v_a_3989_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3974_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3974_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
else
{
lean_dec_ref(v_e_3964_);
return v___x_3971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3997_, lean_object* v_e_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3997_, v_e_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec_ref(v_root_3997_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4006_, lean_object* v_root_4007_, lean_object* v_e_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4007_, v_e_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4016_, lean_object* v_root_4017_, lean_object* v_e_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4016_, v_root_4017_, v_e_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec(v_a_4019_);
lean_dec_ref(v_root_4017_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4026_, lean_object* v_e_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v___y_4034_; lean_object* v_roots_4051_; lean_object* v___x_4052_; uint8_t v_transparency_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; uint8_t v___x_4056_; 
v_roots_4051_ = lean_ctor_get(v_d_4026_, 1);
v___x_4052_ = l_Lean_Meta_Context_config(v_a_4028_);
v_transparency_4053_ = lean_ctor_get_uint8(v___x_4052_, 9);
lean_dec_ref(v___x_4052_);
lean_inc_ref(v_roots_4051_);
v___x_4054_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4054_, 0, lean_box(0));
lean_closure_set(v___x_4054_, 1, v_roots_4051_);
lean_closure_set(v___x_4054_, 2, v_e_4027_);
v___x_4055_ = 2;
v___x_4056_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4053_, v___x_4055_);
if (v___x_4056_ == 0)
{
lean_object* v_keyedConfig_4057_; uint8_t v_trackZetaDelta_4058_; lean_object* v_zetaDeltaSet_4059_; lean_object* v_lctx_4060_; lean_object* v_localInstances_4061_; lean_object* v_defEqCtx_x3f_4062_; lean_object* v_synthPendingDepth_4063_; lean_object* v_customCanUnfoldPredicate_x3f_4064_; uint8_t v_univApprox_4065_; uint8_t v_inTypeClassResolution_4066_; uint8_t v_cacheInferType_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v_keyedConfig_4057_ = lean_ctor_get(v_a_4028_, 0);
v_trackZetaDelta_4058_ = lean_ctor_get_uint8(v_a_4028_, sizeof(void*)*7);
v_zetaDeltaSet_4059_ = lean_ctor_get(v_a_4028_, 1);
v_lctx_4060_ = lean_ctor_get(v_a_4028_, 2);
v_localInstances_4061_ = lean_ctor_get(v_a_4028_, 3);
v_defEqCtx_x3f_4062_ = lean_ctor_get(v_a_4028_, 4);
v_synthPendingDepth_4063_ = lean_ctor_get(v_a_4028_, 5);
v_customCanUnfoldPredicate_x3f_4064_ = lean_ctor_get(v_a_4028_, 6);
v_univApprox_4065_ = lean_ctor_get_uint8(v_a_4028_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4066_ = lean_ctor_get_uint8(v_a_4028_, sizeof(void*)*7 + 2);
v_cacheInferType_4067_ = lean_ctor_get_uint8(v_a_4028_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4057_);
v___x_4068_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4055_, v_keyedConfig_4057_);
lean_inc(v_customCanUnfoldPredicate_x3f_4064_);
lean_inc(v_synthPendingDepth_4063_);
lean_inc(v_defEqCtx_x3f_4062_);
lean_inc_ref(v_localInstances_4061_);
lean_inc_ref(v_lctx_4060_);
lean_inc(v_zetaDeltaSet_4059_);
v___x_4069_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
lean_ctor_set(v___x_4069_, 1, v_zetaDeltaSet_4059_);
lean_ctor_set(v___x_4069_, 2, v_lctx_4060_);
lean_ctor_set(v___x_4069_, 3, v_localInstances_4061_);
lean_ctor_set(v___x_4069_, 4, v_defEqCtx_x3f_4062_);
lean_ctor_set(v___x_4069_, 5, v_synthPendingDepth_4063_);
lean_ctor_set(v___x_4069_, 6, v_customCanUnfoldPredicate_x3f_4064_);
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*7, v_trackZetaDelta_4058_);
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*7 + 1, v_univApprox_4065_);
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4066_);
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*7 + 3, v_cacheInferType_4067_);
v___x_4070_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4026_, v___x_4054_, v___x_4069_, v_a_4029_, v_a_4030_, v_a_4031_);
lean_dec_ref_known(v___x_4069_, 7);
v___y_4034_ = v___x_4070_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4026_, v___x_4054_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
v___y_4034_ = v___x_4071_;
goto v___jp_4033_;
}
v___jp_4033_:
{
if (lean_obj_tag(v___y_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_a_4035_ = lean_ctor_get(v___y_4034_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___y_4034_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___y_4034_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___y_4034_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_a_4043_ = lean_ctor_get(v___y_4034_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___y_4034_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___y_4034_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___y_4034_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4072_, lean_object* v_e_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4072_, v_e_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4080_, lean_object* v_d_4081_, lean_object* v_e_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4081_, v_e_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4089_, lean_object* v_d_4090_, lean_object* v_e_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4089_, v_d_4090_, v_e_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
return v_res_4097_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4101_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v___x_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4104_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4106_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4108_, lean_object* v_k_4109_, lean_object* v_f_4110_){
_start:
{
lean_object* v_roots_4111_; lean_object* v_tries_4112_; lean_object* v___x_4113_; 
v_roots_4111_ = lean_ctor_get(v_d_4108_, 0);
v_tries_4112_ = lean_ctor_get(v_d_4108_, 1);
v___x_4113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4111_, v_k_4109_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4125_; 
lean_inc_ref(v_tries_4112_);
lean_inc_ref(v_roots_4111_);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_d_4108_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; lean_object* v_unused_4127_; 
v_unused_4126_ = lean_ctor_get(v_d_4108_, 1);
lean_dec(v_unused_4126_);
v_unused_4127_ = lean_ctor_get(v_d_4108_, 0);
lean_dec(v_unused_4127_);
v___x_4115_ = v_d_4108_;
v_isShared_4116_ = v_isSharedCheck_4125_;
goto v_resetjp_4114_;
}
else
{
lean_dec(v_d_4108_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4125_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4117_; lean_object* v_roots_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4117_ = lean_array_get_size(v_tries_4112_);
v_roots_4118_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4111_, v_k_4109_, v___x_4117_);
v___x_4119_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_4120_ = lean_apply_1(v_f_4110_, v___x_4119_);
v___x_4121_ = lean_array_push(v_tries_4112_, v___x_4120_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 1, v___x_4121_);
lean_ctor_set(v___x_4115_, 0, v_roots_4118_);
v___x_4123_ = v___x_4115_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_roots_4118_);
lean_ctor_set(v_reuseFailAlloc_4124_, 1, v___x_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
else
{
lean_object* v_val_4128_; lean_object* v___x_4129_; uint8_t v___x_4130_; 
lean_dec(v_k_4109_);
v_val_4128_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_val_4128_);
lean_dec_ref_known(v___x_4113_, 1);
v___x_4129_ = lean_array_get_size(v_tries_4112_);
v___x_4130_ = lean_nat_dec_lt(v_val_4128_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_dec(v_val_4128_);
lean_dec_ref(v_f_4110_);
return v_d_4108_;
}
else
{
lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4142_; 
lean_inc_ref(v_tries_4112_);
lean_inc_ref(v_roots_4111_);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_d_4108_);
if (v_isSharedCheck_4142_ == 0)
{
lean_object* v_unused_4143_; lean_object* v_unused_4144_; 
v_unused_4143_ = lean_ctor_get(v_d_4108_, 1);
lean_dec(v_unused_4143_);
v_unused_4144_ = lean_ctor_get(v_d_4108_, 0);
lean_dec(v_unused_4144_);
v___x_4132_ = v_d_4108_;
v_isShared_4133_ = v_isSharedCheck_4142_;
goto v_resetjp_4131_;
}
else
{
lean_dec(v_d_4108_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4142_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v_v_4134_; lean_object* v___x_4135_; lean_object* v_xs_x27_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4140_; 
v_v_4134_ = lean_array_fget(v_tries_4112_, v_val_4128_);
v___x_4135_ = lean_box(0);
v_xs_x27_4136_ = lean_array_fset(v_tries_4112_, v_val_4128_, v___x_4135_);
v___x_4137_ = lean_apply_1(v_f_4110_, v_v_4134_);
v___x_4138_ = lean_array_fset(v_xs_x27_4136_, v_val_4128_, v___x_4137_);
lean_dec(v_val_4128_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 1, v___x_4138_);
v___x_4140_ = v___x_4132_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_roots_4111_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4145_, lean_object* v_d_4146_, lean_object* v_k_4147_, lean_object* v_f_4148_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4146_, v_k_4147_, v_f_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4150_, lean_object* v_x_4151_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = lean_array_push(v_x_4151_, v_e_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4153_, lean_object* v_k_4154_, lean_object* v_e_4155_){
_start:
{
lean_object* v___f_4156_; lean_object* v___x_4157_; 
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4156_, 0, v_e_4155_);
v___x_4157_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4153_, v_k_4154_, v___f_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4158_, lean_object* v_d_4159_, lean_object* v_k_4160_, lean_object* v_e_4161_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4159_, v_k_4160_, v_e_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4163_, size_t v_i_4164_, lean_object* v_bs_4165_){
_start:
{
uint8_t v___x_4166_; 
v___x_4166_ = lean_usize_dec_lt(v_i_4164_, v_sz_4163_);
if (v___x_4166_ == 0)
{
return v_bs_4165_;
}
else
{
lean_object* v_v_4167_; lean_object* v___x_4168_; lean_object* v_bs_x27_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; size_t v___x_4173_; size_t v___x_4174_; lean_object* v___x_4175_; 
v_v_4167_ = lean_array_uget(v_bs_4165_, v_i_4164_);
v___x_4168_ = lean_unsigned_to_nat(0u);
v_bs_x27_4169_ = lean_array_uset(v_bs_4165_, v_i_4164_, v___x_4168_);
v___x_4170_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4171_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4172_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4170_);
lean_ctor_set(v___x_4172_, 1, v___x_4168_);
lean_ctor_set(v___x_4172_, 2, v___x_4171_);
lean_ctor_set(v___x_4172_, 3, v_v_4167_);
v___x_4173_ = ((size_t)1ULL);
v___x_4174_ = lean_usize_add(v_i_4164_, v___x_4173_);
v___x_4175_ = lean_array_uset(v_bs_x27_4169_, v_i_4164_, v___x_4172_);
v_i_4164_ = v___x_4174_;
v_bs_4165_ = v___x_4175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4177_, lean_object* v_i_4178_, lean_object* v_bs_4179_){
_start:
{
size_t v_sz_boxed_4180_; size_t v_i_boxed_4181_; lean_object* v_res_4182_; 
v_sz_boxed_4180_ = lean_unbox_usize(v_sz_4177_);
lean_dec(v_sz_4177_);
v_i_boxed_4181_ = lean_unbox_usize(v_i_4178_);
lean_dec(v_i_4178_);
v_res_4182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4180_, v_i_boxed_4181_, v_bs_4179_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4183_, lean_object* v_x_4184_){
_start:
{
if (lean_obj_tag(v_x_4184_) == 0)
{
return v_x_4183_;
}
else
{
lean_object* v_key_4185_; lean_object* v_value_4186_; lean_object* v_tail_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_key_4185_ = lean_ctor_get(v_x_4184_, 0);
lean_inc(v_key_4185_);
v_value_4186_ = lean_ctor_get(v_x_4184_, 1);
lean_inc(v_value_4186_);
v_tail_4187_ = lean_ctor_get(v_x_4184_, 2);
lean_inc(v_tail_4187_);
lean_dec_ref_known(v_x_4184_, 3);
v___x_4188_ = lean_unsigned_to_nat(1u);
v___x_4189_ = lean_nat_add(v_value_4186_, v___x_4188_);
lean_dec(v_value_4186_);
v___x_4190_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4183_, v_key_4185_, v___x_4189_);
v_x_4183_ = v___x_4190_;
v_x_4184_ = v_tail_4187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4192_, size_t v_i_4193_, size_t v_stop_4194_, lean_object* v_b_4195_){
_start:
{
uint8_t v___x_4196_; 
v___x_4196_ = lean_usize_dec_eq(v_i_4193_, v_stop_4194_);
if (v___x_4196_ == 0)
{
lean_object* v___x_4197_; lean_object* v___x_4198_; size_t v___x_4199_; size_t v___x_4200_; 
v___x_4197_ = lean_array_uget_borrowed(v_as_4192_, v_i_4193_);
lean_inc(v___x_4197_);
v___x_4198_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4195_, v___x_4197_);
v___x_4199_ = ((size_t)1ULL);
v___x_4200_ = lean_usize_add(v_i_4193_, v___x_4199_);
v_i_4193_ = v___x_4200_;
v_b_4195_ = v___x_4198_;
goto _start;
}
else
{
return v_b_4195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4202_, lean_object* v_i_4203_, lean_object* v_stop_4204_, lean_object* v_b_4205_){
_start:
{
size_t v_i_boxed_4206_; size_t v_stop_boxed_4207_; lean_object* v_res_4208_; 
v_i_boxed_4206_ = lean_unbox_usize(v_i_4203_);
lean_dec(v_i_4203_);
v_stop_boxed_4207_ = lean_unbox_usize(v_stop_4204_);
lean_dec(v_stop_4204_);
v_res_4208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4202_, v_i_boxed_4206_, v_stop_boxed_4207_, v_b_4205_);
lean_dec_ref(v_as_4202_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4209_){
_start:
{
lean_object* v_roots_4210_; lean_object* v_tries_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4234_; 
v_roots_4210_ = lean_ctor_get(v_d_4209_, 0);
v_tries_4211_ = lean_ctor_get(v_d_4209_, 1);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_d_4209_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4213_ = v_d_4209_;
v_isShared_4214_ = v_isSharedCheck_4234_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_tries_4211_);
lean_inc(v_roots_4210_);
lean_dec(v_d_4209_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4234_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___y_4216_; lean_object* v_buckets_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v_buckets_4227_ = lean_ctor_get(v_roots_4210_, 1);
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = lean_array_get_size(v_buckets_4227_);
v___x_4230_ = lean_nat_dec_lt(v___x_4228_, v___x_4229_);
if (v___x_4230_ == 0)
{
v___y_4216_ = v_roots_4210_;
goto v___jp_4215_;
}
else
{
size_t v___x_4231_; size_t v___x_4232_; lean_object* v___x_4233_; 
lean_inc_ref(v_buckets_4227_);
v___x_4231_ = ((size_t)0ULL);
v___x_4232_ = lean_usize_of_nat(v___x_4229_);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4227_, v___x_4231_, v___x_4232_, v_roots_4210_);
lean_dec_ref(v_buckets_4227_);
v___y_4216_ = v___x_4233_;
goto v___jp_4215_;
}
v___jp_4215_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; size_t v_sz_4220_; size_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4225_; 
v___x_4217_ = lean_unsigned_to_nat(1u);
v___x_4218_ = lean_mk_empty_array_with_capacity(v___x_4217_);
lean_dec_ref(v___x_4218_);
v___x_4219_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4220_ = lean_array_size(v_tries_4211_);
v___x_4221_ = ((size_t)0ULL);
v___x_4222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4220_, v___x_4221_, v_tries_4211_);
v___x_4223_ = l_Array_append___redArg(v___x_4219_, v___x_4222_);
lean_dec_ref(v___x_4222_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 1, v___y_4216_);
lean_ctor_set(v___x_4213_, 0, v___x_4223_);
v___x_4225_ = v___x_4213_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v___y_4216_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4235_, lean_object* v_d_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_bs_4241_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4239_, v_i_4240_, v_bs_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4243_, lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_bs_4246_){
_start:
{
size_t v_sz_boxed_4247_; size_t v_i_boxed_4248_; lean_object* v_res_4249_; 
v_sz_boxed_4247_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4248_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4243_, v_sz_boxed_4247_, v_i_boxed_4248_, v_bs_4246_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4250_, lean_object* v_x_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Array_append___redArg(v_x_4251_, v_y_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4253_, lean_object* v_x_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4253_, v_x_4254_);
lean_dec_ref(v_y_4253_);
return v_res_4255_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Array_instInhabited(lean_box(0));
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4257_, lean_object* v_snd_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_){
_start:
{
if (lean_obj_tag(v_x_4260_) == 0)
{
lean_dec_ref(v_snd_4258_);
return v_x_4259_;
}
else
{
lean_object* v_key_4261_; lean_object* v_value_4262_; lean_object* v_tail_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v_key_4261_ = lean_ctor_get(v_x_4260_, 0);
lean_inc(v_key_4261_);
v_value_4262_ = lean_ctor_get(v_x_4260_, 1);
lean_inc(v_value_4262_);
v_tail_4263_ = lean_ctor_get(v_x_4260_, 2);
lean_inc(v_tail_4263_);
lean_dec_ref_known(v_x_4260_, 3);
v___x_4264_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4265_ = lean_array_get_borrowed(v___x_4264_, v_tries_4257_, v_value_4262_);
lean_dec(v_value_4262_);
lean_inc_ref(v_snd_4258_);
lean_inc(v___x_4265_);
v___x_4266_ = lean_apply_1(v_snd_4258_, v___x_4265_);
v___x_4267_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4259_, v_key_4261_, v___x_4266_);
v_x_4259_ = v___x_4267_;
v_x_4260_ = v_tail_4263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4269_, lean_object* v_snd_4270_, lean_object* v_x_4271_, lean_object* v_x_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4269_, v_snd_4270_, v_x_4271_, v_x_4272_);
lean_dec_ref(v_tries_4269_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4274_, lean_object* v_snd_4275_, lean_object* v_as_4276_, size_t v_i_4277_, size_t v_stop_4278_, lean_object* v_b_4279_){
_start:
{
uint8_t v___x_4280_; 
v___x_4280_ = lean_usize_dec_eq(v_i_4277_, v_stop_4278_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; size_t v___x_4283_; size_t v___x_4284_; 
v___x_4281_ = lean_array_uget_borrowed(v_as_4276_, v_i_4277_);
lean_inc(v___x_4281_);
lean_inc_ref(v_snd_4275_);
v___x_4282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4274_, v_snd_4275_, v_b_4279_, v___x_4281_);
v___x_4283_ = ((size_t)1ULL);
v___x_4284_ = lean_usize_add(v_i_4277_, v___x_4283_);
v_i_4277_ = v___x_4284_;
v_b_4279_ = v___x_4282_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4275_);
return v_b_4279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4286_, lean_object* v_snd_4287_, lean_object* v_as_4288_, lean_object* v_i_4289_, lean_object* v_stop_4290_, lean_object* v_b_4291_){
_start:
{
size_t v_i_boxed_4292_; size_t v_stop_boxed_4293_; lean_object* v_res_4294_; 
v_i_boxed_4292_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_stop_boxed_4293_ = lean_unbox_usize(v_stop_4290_);
lean_dec(v_stop_4290_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4286_, v_snd_4287_, v_as_4288_, v_i_boxed_4292_, v_stop_boxed_4293_, v_b_4291_);
lean_dec_ref(v_as_4288_);
lean_dec_ref(v_tries_4286_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4297_, lean_object* v_y_4298_){
_start:
{
lean_object* v_fst_4300_; lean_object* v_buckets_4301_; lean_object* v_tries_4302_; lean_object* v_snd_4303_; lean_object* v_roots_4310_; lean_object* v_roots_4311_; lean_object* v_tries_4312_; lean_object* v_size_4313_; lean_object* v_buckets_4314_; lean_object* v_tries_4315_; lean_object* v_size_4316_; lean_object* v_buckets_4317_; uint8_t v___x_4318_; 
v_roots_4310_ = lean_ctor_get(v_y_4298_, 0);
v_roots_4311_ = lean_ctor_get(v_x_4297_, 0);
v_tries_4312_ = lean_ctor_get(v_y_4298_, 1);
v_size_4313_ = lean_ctor_get(v_roots_4310_, 0);
v_buckets_4314_ = lean_ctor_get(v_roots_4310_, 1);
v_tries_4315_ = lean_ctor_get(v_x_4297_, 1);
v_size_4316_ = lean_ctor_get(v_roots_4311_, 0);
v_buckets_4317_ = lean_ctor_get(v_roots_4311_, 1);
v___x_4318_ = lean_nat_dec_le(v_size_4313_, v_size_4316_);
if (v___x_4318_ == 0)
{
lean_object* v___f_4319_; 
lean_inc_ref(v_buckets_4317_);
lean_inc_ref(v_tries_4315_);
lean_dec_ref(v_x_4297_);
v___f_4319_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4300_ = v_y_4298_;
v_buckets_4301_ = v_buckets_4317_;
v_tries_4302_ = v_tries_4315_;
v_snd_4303_ = v___f_4319_;
goto v___jp_4299_;
}
else
{
lean_object* v___f_4320_; 
lean_inc_ref(v_buckets_4314_);
lean_inc_ref(v_tries_4312_);
lean_dec_ref(v_y_4298_);
v___f_4320_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4300_ = v_x_4297_;
v_buckets_4301_ = v_buckets_4314_;
v_tries_4302_ = v_tries_4312_;
v_snd_4303_ = v___f_4320_;
goto v___jp_4299_;
}
v___jp_4299_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4304_ = lean_unsigned_to_nat(0u);
v___x_4305_ = lean_array_get_size(v_buckets_4301_);
v___x_4306_ = lean_nat_dec_lt(v___x_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec_ref(v_tries_4302_);
lean_dec_ref(v_buckets_4301_);
return v_fst_4300_;
}
else
{
size_t v___x_4307_; size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = ((size_t)0ULL);
v___x_4308_ = lean_usize_of_nat(v___x_4305_);
lean_inc_ref(v_snd_4303_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4302_, v_snd_4303_, v_buckets_4301_, v___x_4307_, v___x_4308_, v_fst_4300_);
lean_dec_ref(v_buckets_4301_);
lean_dec_ref(v_tries_4302_);
return v___x_4309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4321_, lean_object* v_x_4322_, lean_object* v_y_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4322_, v_y_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4325_, lean_object* v_tries_4326_, lean_object* v_snd_4327_, lean_object* v_x_4328_, lean_object* v_x_4329_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4326_, v_snd_4327_, v_x_4328_, v_x_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4331_, lean_object* v_tries_4332_, lean_object* v_snd_4333_, lean_object* v_x_4334_, lean_object* v_x_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4331_, v_tries_4332_, v_snd_4333_, v_x_4334_, v_x_4335_);
lean_dec_ref(v_tries_4332_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4337_, lean_object* v_tries_4338_, lean_object* v_snd_4339_, lean_object* v_as_4340_, size_t v_i_4341_, size_t v_stop_4342_, lean_object* v_b_4343_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4338_, v_snd_4339_, v_as_4340_, v_i_4341_, v_stop_4342_, v_b_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4345_, lean_object* v_tries_4346_, lean_object* v_snd_4347_, lean_object* v_as_4348_, lean_object* v_i_4349_, lean_object* v_stop_4350_, lean_object* v_b_4351_){
_start:
{
size_t v_i_boxed_4352_; size_t v_stop_boxed_4353_; lean_object* v_res_4354_; 
v_i_boxed_4352_ = lean_unbox_usize(v_i_4349_);
lean_dec(v_i_4349_);
v_stop_boxed_4353_ = lean_unbox_usize(v_stop_4350_);
lean_dec(v_stop_4350_);
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4345_, v_tries_4346_, v_snd_4347_, v_as_4348_, v_i_boxed_4352_, v_stop_boxed_4353_, v_b_4351_);
lean_dec_ref(v_as_4348_);
lean_dec_ref(v_tries_4346_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4356_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4358_, lean_object* v_value_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4358_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4387_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4387_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4387_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v_fst_4370_; lean_object* v_snd_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4386_; 
v_fst_4370_ = lean_ctor_get(v_a_4366_, 0);
v_snd_4371_ = lean_ctor_get(v_a_4366_, 1);
v_isSharedCheck_4386_ = !lean_is_exclusive(v_a_4366_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4373_ = v_a_4366_;
v_isShared_4374_ = v_isSharedCheck_4386_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_snd_4371_);
lean_inc(v_fst_4370_);
lean_dec(v_a_4366_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4386_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v_lctx_4375_; lean_object* v_localInstances_4376_; lean_object* v___x_4378_; 
v_lctx_4375_ = lean_ctor_get(v_a_4360_, 2);
v_localInstances_4376_ = lean_ctor_get(v_a_4360_, 3);
lean_inc_ref(v_localInstances_4376_);
lean_inc_ref(v_lctx_4375_);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 1, v_localInstances_4376_);
lean_ctor_set(v___x_4373_, 0, v_lctx_4375_);
v___x_4378_ = v___x_4373_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_lctx_4375_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_localInstances_4376_);
v___x_4378_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
lean_ctor_set(v___x_4379_, 1, v_value_4359_);
v___x_4380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4380_, 0, v_snd_4371_);
lean_ctor_set(v___x_4380_, 1, v___x_4379_);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v_fst_4370_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v___x_4381_);
v___x_4383_ = v___x_4368_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec(v_value_4359_);
v_a_4388_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4365_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4365_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4396_, lean_object* v_value_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4396_, v_value_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec(v_a_4399_);
lean_dec_ref(v_a_4398_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4404_, lean_object* v_expr_4405_, lean_object* v_value_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4405_, v_value_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4413_, lean_object* v_expr_4414_, lean_object* v_value_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4413_, v_expr_4414_, v_value_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
lean_dec(v_a_4419_);
lean_dec_ref(v_a_4418_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4422_, lean_object* v_idx_4423_, lean_object* v_value_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v_entry_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4476_; 
v_entry_4430_ = lean_ctor_get(v_e_4422_, 1);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_e_4422_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; 
v_unused_4477_ = lean_ctor_get(v_e_4422_, 0);
lean_dec(v_unused_4477_);
v___x_4432_ = v_e_4422_;
v_isShared_4433_ = v_isSharedCheck_4476_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_entry_4430_);
lean_dec(v_e_4422_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4476_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v_snd_4434_; lean_object* v_fst_4435_; lean_object* v_fst_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4474_; 
v_snd_4434_ = lean_ctor_get(v_entry_4430_, 1);
lean_inc(v_snd_4434_);
v_fst_4435_ = lean_ctor_get(v_entry_4430_, 0);
lean_inc(v_fst_4435_);
lean_dec_ref(v_entry_4430_);
v_fst_4436_ = lean_ctor_get(v_snd_4434_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_snd_4434_);
if (v_isSharedCheck_4474_ == 0)
{
lean_object* v_unused_4475_; 
v_unused_4475_ = lean_ctor_get(v_snd_4434_, 1);
lean_dec(v_unused_4475_);
v___x_4438_ = v_snd_4434_;
v_isShared_4439_ = v_isSharedCheck_4474_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_fst_4436_);
lean_dec(v_snd_4434_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4474_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = l_Lean_instInhabitedExpr;
v___x_4441_ = lean_array_get(v___x_4440_, v_fst_4435_, v_idx_4423_);
lean_dec(v_fst_4435_);
v___x_4442_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4441_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4465_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4445_ = v___x_4442_;
v_isShared_4446_ = v_isSharedCheck_4465_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4442_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4465_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v_fst_4447_; lean_object* v_snd_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4464_; 
v_fst_4447_ = lean_ctor_get(v_a_4443_, 0);
v_snd_4448_ = lean_ctor_get(v_a_4443_, 1);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_a_4443_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4450_ = v_a_4443_;
v_isShared_4451_ = v_isSharedCheck_4464_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_snd_4448_);
lean_inc(v_fst_4447_);
lean_dec(v_a_4443_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4464_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 1, v_value_4424_);
lean_ctor_set(v___x_4450_, 0, v_fst_4436_);
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_fst_4436_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v_value_4424_);
v___x_4453_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4455_; 
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 1, v___x_4453_);
lean_ctor_set(v___x_4438_, 0, v_snd_4448_);
v___x_4455_ = v___x_4438_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_snd_4448_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v___x_4453_);
v___x_4455_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4457_; 
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 1, v___x_4455_);
lean_ctor_set(v___x_4432_, 0, v_fst_4447_);
v___x_4457_ = v___x_4432_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_fst_4447_);
lean_ctor_set(v_reuseFailAlloc_4461_, 1, v___x_4455_);
v___x_4457_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 0, v___x_4457_);
v___x_4459_ = v___x_4445_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_del_object(v___x_4438_);
lean_dec(v_fst_4436_);
lean_del_object(v___x_4432_);
lean_dec(v_value_4424_);
v_a_4466_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4442_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4442_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4478_, lean_object* v_idx_4479_, lean_object* v_value_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4478_, v_idx_4479_, v_value_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_a_4482_);
lean_dec_ref(v_a_4481_);
lean_dec(v_idx_4479_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4487_, lean_object* v_e_4488_, lean_object* v_idx_4489_, lean_object* v_value_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4488_, v_idx_4489_, v_value_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4497_, lean_object* v_e_4498_, lean_object* v_idx_4499_, lean_object* v_value_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4497_, v_e_4498_, v_idx_4499_, v_value_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_idx_4499_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4511_ = lean_st_mk_ref(v___x_4510_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4513_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4514_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
return v___x_4518_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4520_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
lean_ctor_set(v___x_4520_, 1, v___x_4519_);
lean_ctor_set(v___x_4520_, 2, v___x_4519_);
lean_ctor_set(v___x_4520_, 3, v___x_4519_);
lean_ctor_set(v___x_4520_, 4, v___x_4519_);
lean_ctor_set(v___x_4520_, 5, v___x_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4521_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4522_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4523_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4524_, 0, v_ngen_4521_);
lean_ctor_set(v___x_4524_, 1, v___x_4522_);
lean_ctor_set(v___x_4524_, 2, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4525_, lean_object* v_declName_4526_){
_start:
{
uint8_t v___x_4527_; 
v___x_4527_ = l_Lean_isPrivateName(v_declName_4526_);
if (v___x_4527_ == 0)
{
return v___x_4527_;
}
else
{
lean_object* v___x_4528_; 
v___x_4528_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4525_, v_declName_4526_);
if (lean_obj_tag(v___x_4528_) == 0)
{
return v___x_4527_;
}
else
{
lean_object* v_val_4529_; lean_object* v___x_4530_; uint8_t v_isModule_4531_; lean_object* v_modules_4532_; uint8_t v___x_4533_; 
v_val_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_val_4529_);
lean_dec_ref_known(v___x_4528_, 1);
v___x_4530_ = l_Lean_Environment_header(v_env_4525_);
v_isModule_4531_ = lean_ctor_get_uint8(v___x_4530_, sizeof(void*)*7 + 4);
v_modules_4532_ = lean_ctor_get(v___x_4530_, 3);
lean_inc_ref(v_modules_4532_);
lean_dec_ref(v___x_4530_);
v___x_4533_ = 0;
if (v_isModule_4531_ == 0)
{
lean_dec_ref(v_modules_4532_);
lean_dec(v_val_4529_);
return v___x_4533_;
}
else
{
lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4534_ = lean_array_get_size(v_modules_4532_);
v___x_4535_ = lean_nat_dec_lt(v_val_4529_, v___x_4534_);
if (v___x_4535_ == 0)
{
lean_dec_ref(v_modules_4532_);
lean_dec(v_val_4529_);
return v___x_4533_;
}
else
{
lean_object* v___x_4536_; lean_object* v_toImport_4537_; uint8_t v_importAll_4538_; 
v___x_4536_ = lean_array_fget(v_modules_4532_, v_val_4529_);
lean_dec(v_val_4529_);
lean_dec_ref(v_modules_4532_);
v_toImport_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc_ref(v_toImport_4537_);
lean_dec(v___x_4536_);
v_importAll_4538_ = lean_ctor_get_uint8(v_toImport_4537_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4537_);
return v_importAll_4538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4539_, lean_object* v_declName_4540_){
_start:
{
uint8_t v_res_4541_; lean_object* v_r_4542_; 
v_res_4541_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4539_, v_declName_4540_);
lean_dec(v_declName_4540_);
lean_dec_ref(v_env_4539_);
v_r_4542_ = lean_box(v_res_4541_);
return v_r_4542_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4548_, lean_object* v_declName_4549_){
_start:
{
uint8_t v___x_4550_; 
lean_inc(v_declName_4549_);
lean_inc_ref(v_env_4548_);
v___x_4550_ = l_Lean_Meta_allowCompletion(v_env_4548_, v_declName_4549_);
if (v___x_4550_ == 0)
{
uint8_t v___x_4551_; 
lean_dec(v_declName_4549_);
lean_dec_ref(v_env_4548_);
v___x_4551_ = 1;
return v___x_4551_;
}
else
{
lean_object* v___x_4552_; uint8_t v___x_4553_; uint8_t v___y_4563_; 
v___x_4552_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4553_ = lean_name_eq(v_declName_4549_, v___x_4552_);
if (v___x_4553_ == 0)
{
uint8_t v___x_4564_; 
lean_inc(v_declName_4549_);
v___x_4564_ = l_Lean_Name_isInternalDetail(v_declName_4549_);
if (v___x_4564_ == 0)
{
lean_dec_ref(v_env_4548_);
v___y_4563_ = v___x_4564_;
goto v___jp_4562_;
}
else
{
uint8_t v___x_4565_; 
v___x_4565_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4548_, v_declName_4549_);
lean_dec_ref(v_env_4548_);
if (v___x_4565_ == 0)
{
v___y_4563_ = v___x_4564_;
goto v___jp_4562_;
}
else
{
goto v___jp_4558_;
}
}
}
else
{
lean_dec(v_declName_4549_);
lean_dec_ref(v_env_4548_);
return v___x_4553_;
}
v___jp_4554_:
{
if (lean_obj_tag(v_declName_4549_) == 1)
{
lean_object* v_str_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; 
v_str_4555_ = lean_ctor_get(v_declName_4549_, 1);
lean_inc_ref(v_str_4555_);
lean_dec_ref_known(v_declName_4549_, 2);
v___x_4556_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4557_ = lean_string_dec_eq(v_str_4555_, v___x_4556_);
lean_dec_ref(v_str_4555_);
return v___x_4557_;
}
else
{
lean_dec(v_declName_4549_);
return v___x_4553_;
}
}
v___jp_4558_:
{
if (lean_obj_tag(v_declName_4549_) == 1)
{
lean_object* v_str_4559_; lean_object* v___x_4560_; uint8_t v___x_4561_; 
v_str_4559_ = lean_ctor_get(v_declName_4549_, 1);
v___x_4560_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4561_ = lean_string_dec_eq(v_str_4559_, v___x_4560_);
if (v___x_4561_ == 0)
{
goto v___jp_4554_;
}
else
{
lean_dec_ref_known(v_declName_4549_, 2);
return v___x_4561_;
}
}
else
{
goto v___jp_4554_;
}
}
v___jp_4562_:
{
if (v___y_4563_ == 0)
{
goto v___jp_4558_;
}
else
{
lean_dec(v_declName_4549_);
return v___y_4563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4566_, lean_object* v_declName_4567_){
_start:
{
uint8_t v_res_4568_; lean_object* v_r_4569_; 
v_res_4568_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4566_, v_declName_4567_);
v_r_4569_ = lean_box(v_res_4568_);
return v_r_4569_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4570_, lean_object* v_opt_4571_){
_start:
{
lean_object* v_name_4572_; lean_object* v_defValue_4573_; lean_object* v_map_4574_; lean_object* v___x_4575_; 
v_name_4572_ = lean_ctor_get(v_opt_4571_, 0);
v_defValue_4573_ = lean_ctor_get(v_opt_4571_, 1);
v_map_4574_ = lean_ctor_get(v_opts_4570_, 0);
v___x_4575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4574_, v_name_4572_);
if (lean_obj_tag(v___x_4575_) == 0)
{
uint8_t v___x_4576_; 
v___x_4576_ = lean_unbox(v_defValue_4573_);
return v___x_4576_;
}
else
{
lean_object* v_val_4577_; 
v_val_4577_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_val_4577_);
lean_dec_ref_known(v___x_4575_, 1);
if (lean_obj_tag(v_val_4577_) == 1)
{
uint8_t v_v_4578_; 
v_v_4578_ = lean_ctor_get_uint8(v_val_4577_, 0);
lean_dec_ref_known(v_val_4577_, 0);
return v_v_4578_;
}
else
{
uint8_t v___x_4579_; 
lean_dec(v_val_4577_);
v___x_4579_ = lean_unbox(v_defValue_4573_);
return v___x_4579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4580_, lean_object* v_opt_4581_){
_start:
{
uint8_t v_res_4582_; lean_object* v_r_4583_; 
v_res_4582_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4580_, v_opt_4581_);
lean_dec_ref(v_opt_4581_);
lean_dec_ref(v_opts_4580_);
v_r_4583_ = lean_box(v_res_4582_);
return v_r_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4584_, lean_object* v_opt_4585_){
_start:
{
lean_object* v_name_4586_; lean_object* v_defValue_4587_; lean_object* v_map_4588_; lean_object* v___x_4589_; 
v_name_4586_ = lean_ctor_get(v_opt_4585_, 0);
v_defValue_4587_ = lean_ctor_get(v_opt_4585_, 1);
v_map_4588_ = lean_ctor_get(v_opts_4584_, 0);
v___x_4589_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4588_, v_name_4586_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_inc(v_defValue_4587_);
return v_defValue_4587_;
}
else
{
lean_object* v_val_4590_; 
v_val_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_val_4590_);
lean_dec_ref_known(v___x_4589_, 1);
if (lean_obj_tag(v_val_4590_) == 3)
{
lean_object* v_v_4591_; 
v_v_4591_ = lean_ctor_get(v_val_4590_, 0);
lean_inc(v_v_4591_);
lean_dec_ref_known(v_val_4590_, 1);
return v_v_4591_;
}
else
{
lean_dec(v_val_4590_);
lean_inc(v_defValue_4587_);
return v_defValue_4587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4592_, lean_object* v_opt_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4592_, v_opt_4593_);
lean_dec_ref(v_opt_4593_);
lean_dec_ref(v_opts_4592_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4595_, size_t v_i_4596_, size_t v_stop_4597_, lean_object* v_b_4598_){
_start:
{
uint8_t v___x_4599_; 
v___x_4599_ = lean_usize_dec_eq(v_i_4596_, v_stop_4597_);
if (v___x_4599_ == 0)
{
lean_object* v___x_4600_; lean_object* v_key_4601_; lean_object* v_entry_4602_; lean_object* v___x_4603_; size_t v___x_4604_; size_t v___x_4605_; 
v___x_4600_ = lean_array_uget_borrowed(v_as_4595_, v_i_4596_);
v_key_4601_ = lean_ctor_get(v___x_4600_, 0);
v_entry_4602_ = lean_ctor_get(v___x_4600_, 1);
lean_inc_ref(v_entry_4602_);
lean_inc(v_key_4601_);
v___x_4603_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4598_, v_key_4601_, v_entry_4602_);
v___x_4604_ = ((size_t)1ULL);
v___x_4605_ = lean_usize_add(v_i_4596_, v___x_4604_);
v_i_4596_ = v___x_4605_;
v_b_4598_ = v___x_4603_;
goto _start;
}
else
{
return v_b_4598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4607_, lean_object* v_i_4608_, lean_object* v_stop_4609_, lean_object* v_b_4610_){
_start:
{
size_t v_i_boxed_4611_; size_t v_stop_boxed_4612_; lean_object* v_res_4613_; 
v_i_boxed_4611_ = lean_unbox_usize(v_i_4608_);
lean_dec(v_i_4608_);
v_stop_boxed_4612_ = lean_unbox_usize(v_stop_4609_);
lean_dec(v_stop_4609_);
v_res_4613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4607_, v_i_boxed_4611_, v_stop_boxed_4612_, v_b_4610_);
lean_dec_ref(v_as_4607_);
return v_res_4613_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4614_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
return v___x_4616_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4617_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4618_ = lean_unsigned_to_nat(0u);
v___x_4619_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
lean_ctor_set(v___x_4619_, 2, v___x_4618_);
lean_ctor_set(v___x_4619_, 3, v___x_4618_);
lean_ctor_set(v___x_4619_, 4, v___x_4617_);
lean_ctor_set(v___x_4619_, 5, v___x_4617_);
lean_ctor_set(v___x_4619_, 6, v___x_4617_);
lean_ctor_set(v___x_4619_, 7, v___x_4617_);
lean_ctor_set(v___x_4619_, 8, v___x_4617_);
lean_ctor_set(v___x_4619_, 9, v___x_4617_);
lean_ctor_set(v___x_4619_, 10, v___x_4617_);
return v___x_4619_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = lean_unsigned_to_nat(32u);
v___x_4621_ = lean_mk_empty_array_with_capacity(v___x_4620_);
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
return v___x_4622_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4623_ = ((size_t)5ULL);
v___x_4624_ = lean_unsigned_to_nat(0u);
v___x_4625_ = lean_unsigned_to_nat(32u);
v___x_4626_ = lean_mk_empty_array_with_capacity(v___x_4625_);
v___x_4627_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4628_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
lean_ctor_set(v___x_4628_, 1, v___x_4626_);
lean_ctor_set(v___x_4628_, 2, v___x_4624_);
lean_ctor_set(v___x_4628_, 3, v___x_4624_);
lean_ctor_set_usize(v___x_4628_, 4, v___x_4623_);
return v___x_4628_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
lean_ctor_set(v___x_4630_, 1, v___x_4629_);
lean_ctor_set(v___x_4630_, 2, v___x_4629_);
lean_ctor_set(v___x_4630_, 3, v___x_4629_);
lean_ctor_set(v___x_4630_, 4, v___x_4629_);
return v___x_4630_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4631_ = lean_box(1);
v___x_4632_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4633_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
lean_ctor_set(v___x_4634_, 1, v___x_4632_);
lean_ctor_set(v___x_4634_, 2, v___x_4631_);
return v___x_4634_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4637_ = lean_unsigned_to_nat(1u);
v___x_4638_ = l_Lean_firstFrontendMacroScope;
v___x_4639_ = lean_nat_add(v___x_4638_, v___x_4637_);
return v___x_4639_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4644_; uint64_t v___x_4645_; lean_object* v___x_4646_; 
v___x_4644_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4645_ = 0ULL;
v___x_4646_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4646_, 0, v___x_4644_);
lean_ctor_set_uint64(v___x_4646_, sizeof(void*)*1, v___x_4645_);
return v___x_4646_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = l_Lean_NameSet_empty;
v___x_4648_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
lean_ctor_set(v___x_4649_, 1, v___x_4648_);
lean_ctor_set(v___x_4649_, 2, v___x_4647_);
return v___x_4649_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; uint8_t v___x_4652_; lean_object* v___x_4653_; 
v___x_4650_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4651_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4652_ = 1;
v___x_4653_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4653_, 0, v___x_4651_);
lean_ctor_set(v___x_4653_, 1, v___x_4651_);
lean_ctor_set(v___x_4653_, 2, v___x_4650_);
lean_ctor_set_uint8(v___x_4653_, sizeof(void*)*3, v___x_4652_);
return v___x_4653_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4654_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4654_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4656_, lean_object* v_env_4657_, lean_object* v_modName_4658_, lean_object* v_d_4659_, lean_object* v_cacheRef_4660_, lean_object* v_tree_4661_, lean_object* v_act_4662_, lean_object* v_c_4663_){
_start:
{
uint8_t v___x_4665_; 
lean_inc_ref(v_c_4663_);
v___x_4665_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4663_);
if (v___x_4665_ == 0)
{
lean_object* v_name_4666_; uint8_t v___x_4667_; 
v_name_4666_ = lean_ctor_get(v_c_4663_, 0);
lean_inc_n(v_name_4666_, 2);
lean_inc_ref(v_env_4657_);
v___x_4667_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4657_, v_name_4666_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; lean_object* v_ngen_4669_; lean_object* v_core_4670_; lean_object* v_meta_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4789_; 
v___x_4668_ = lean_st_ref_get(v_cacheRef_4660_);
v_ngen_4669_ = lean_ctor_get(v___x_4668_, 0);
v_core_4670_ = lean_ctor_get(v___x_4668_, 1);
v_meta_4671_ = lean_ctor_get(v___x_4668_, 2);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4673_ = v___x_4668_;
v_isShared_4674_ = v_isSharedCheck_4789_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_meta_4671_);
lean_inc(v_core_4670_);
lean_inc(v_ngen_4669_);
lean_dec(v___x_4668_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4789_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; uint8_t v___x_4685_; uint8_t v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v_toCold_4703_; lean_object* v_currRecDepth_4704_; lean_object* v_ref_4705_; uint8_t v_suppressElabErrors_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4788_; 
v___x_4675_ = lean_unsigned_to_nat(0u);
v___x_4676_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4677_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4678_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4669_);
v___x_4679_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4669_);
v___x_4680_ = lean_st_ref_swap(v_cacheRef_4660_, v___x_4679_);
lean_dec(v___x_4680_);
v___x_4681_ = lean_box(1);
v___x_4682_ = 1;
v___x_4683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4676_);
lean_ctor_set(v___x_4683_, 1, v_meta_4671_);
lean_ctor_set(v___x_4683_, 2, v___x_4681_);
lean_ctor_set(v___x_4683_, 3, v___x_4677_);
lean_ctor_set(v___x_4683_, 4, v___x_4678_);
v___x_4684_ = 2;
v___x_4685_ = 0;
v___x_4686_ = 2;
v___x_4687_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4687_, 0, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 1, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 2, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 3, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 4, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 5, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 6, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 7, v___x_4667_);
lean_ctor_set_uint8(v___x_4687_, 8, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 9, v___x_4684_);
lean_ctor_set_uint8(v___x_4687_, 10, v___x_4685_);
lean_ctor_set_uint8(v___x_4687_, 11, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 12, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 13, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 14, v___x_4686_);
lean_ctor_set_uint8(v___x_4687_, 15, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 16, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 17, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 18, v___x_4682_);
lean_ctor_set_uint8(v___x_4687_, 19, v___x_4667_);
v___x_4688_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4687_);
v___x_4689_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4690_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4692_, 0, v___x_4688_);
lean_ctor_set(v___x_4692_, 1, v___x_4681_);
lean_ctor_set(v___x_4692_, 2, v___x_4689_);
lean_ctor_set(v___x_4692_, 3, v___x_4690_);
lean_ctor_set(v___x_4692_, 4, v___x_4691_);
lean_ctor_set(v___x_4692_, 5, v___x_4675_);
lean_ctor_set(v___x_4692_, 6, v___x_4691_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7, v___x_4667_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 1, v___x_4667_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 2, v___x_4667_);
lean_ctor_set_uint8(v___x_4692_, sizeof(void*)*7 + 3, v___x_4682_);
v___x_4693_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4694_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4695_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4696_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4697_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4698_, 0, v_env_4657_);
lean_ctor_set(v___x_4698_, 1, v___x_4693_);
lean_ctor_set(v___x_4698_, 2, v_ngen_4669_);
lean_ctor_set(v___x_4698_, 3, v___x_4694_);
lean_ctor_set(v___x_4698_, 4, v___x_4695_);
lean_ctor_set(v___x_4698_, 5, v_core_4670_);
lean_ctor_set(v___x_4698_, 6, v___x_4696_);
lean_ctor_set(v___x_4698_, 7, v___x_4697_);
lean_ctor_set(v___x_4698_, 8, v___x_4690_);
v___x_4699_ = lean_st_mk_ref(v___x_4698_);
v___x_4700_ = l_Lean_inheritedTraceOptions;
v___x_4701_ = lean_st_ref_get(v___x_4700_);
v___x_4702_ = lean_st_ref_get(v___x_4699_);
v_toCold_4703_ = lean_ctor_get(v_cctx_4656_, 0);
v_currRecDepth_4704_ = lean_ctor_get(v_cctx_4656_, 1);
v_ref_4705_ = lean_ctor_get(v_cctx_4656_, 2);
v_suppressElabErrors_4706_ = lean_ctor_get_uint8(v_cctx_4656_, sizeof(void*)*3 + 1);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_cctx_4656_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4708_ = v_cctx_4656_;
v_isShared_4709_ = v_isSharedCheck_4788_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_ref_4705_);
lean_inc(v_currRecDepth_4704_);
lean_inc(v_toCold_4703_);
lean_dec(v_cctx_4656_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4788_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v_fileName_4710_; lean_object* v_fileMap_4711_; lean_object* v_options_4712_; lean_object* v_currNamespace_4713_; lean_object* v_openDecls_4714_; lean_object* v_initHeartbeats_4715_; lean_object* v_maxHeartbeats_4716_; lean_object* v_quotContext_4717_; lean_object* v_currMacroScope_4718_; lean_object* v_cancelTk_x3f_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4785_; 
v_fileName_4710_ = lean_ctor_get(v_toCold_4703_, 0);
v_fileMap_4711_ = lean_ctor_get(v_toCold_4703_, 1);
v_options_4712_ = lean_ctor_get(v_toCold_4703_, 2);
v_currNamespace_4713_ = lean_ctor_get(v_toCold_4703_, 4);
v_openDecls_4714_ = lean_ctor_get(v_toCold_4703_, 5);
v_initHeartbeats_4715_ = lean_ctor_get(v_toCold_4703_, 6);
v_maxHeartbeats_4716_ = lean_ctor_get(v_toCold_4703_, 7);
v_quotContext_4717_ = lean_ctor_get(v_toCold_4703_, 8);
v_currMacroScope_4718_ = lean_ctor_get(v_toCold_4703_, 9);
v_cancelTk_x3f_4719_ = lean_ctor_get(v_toCold_4703_, 10);
v_isSharedCheck_4785_ = !lean_is_exclusive(v_toCold_4703_);
if (v_isSharedCheck_4785_ == 0)
{
lean_object* v_unused_4786_; lean_object* v_unused_4787_; 
v_unused_4786_ = lean_ctor_get(v_toCold_4703_, 11);
lean_dec(v_unused_4786_);
v_unused_4787_ = lean_ctor_get(v_toCold_4703_, 3);
lean_dec(v_unused_4787_);
v___x_4721_ = v_toCold_4703_;
v_isShared_4722_ = v_isSharedCheck_4785_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_cancelTk_x3f_4719_);
lean_inc(v_currMacroScope_4718_);
lean_inc(v_quotContext_4717_);
lean_inc(v_maxHeartbeats_4716_);
lean_inc(v_initHeartbeats_4715_);
lean_inc(v_openDecls_4714_);
lean_inc(v_currNamespace_4713_);
lean_inc(v_options_4712_);
lean_inc(v_fileMap_4711_);
lean_inc(v_fileName_4710_);
lean_dec(v_toCold_4703_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4785_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v_env_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; lean_object* v___y_4727_; uint8_t v___y_4763_; uint8_t v___x_4784_; 
v_env_4723_ = lean_ctor_get(v___x_4702_, 0);
lean_inc_ref(v_env_4723_);
lean_dec(v___x_4702_);
v___x_4724_ = l_Lean_diagnostics;
v___x_4725_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4712_, v___x_4724_);
v___x_4784_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4723_);
lean_dec_ref(v_env_4723_);
if (v___x_4725_ == 0)
{
if (v___x_4784_ == 0)
{
lean_inc(v___x_4699_);
v___y_4727_ = v___x_4699_;
goto v___jp_4726_;
}
else
{
v___y_4763_ = v___x_4725_;
goto v___jp_4762_;
}
}
else
{
v___y_4763_ = v___x_4784_;
goto v___jp_4762_;
}
v___jp_4726_:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4732_; 
v___x_4728_ = lean_st_mk_ref(v___x_4683_);
v___x_4729_ = l_Lean_maxRecDepth;
v___x_4730_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4712_, v___x_4729_);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 11, v___x_4701_);
lean_ctor_set(v___x_4721_, 3, v___x_4730_);
v___x_4732_ = v___x_4721_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_fileName_4710_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v_fileMap_4711_);
lean_ctor_set(v_reuseFailAlloc_4761_, 2, v_options_4712_);
lean_ctor_set(v_reuseFailAlloc_4761_, 3, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4761_, 4, v_currNamespace_4713_);
lean_ctor_set(v_reuseFailAlloc_4761_, 5, v_openDecls_4714_);
lean_ctor_set(v_reuseFailAlloc_4761_, 6, v_initHeartbeats_4715_);
lean_ctor_set(v_reuseFailAlloc_4761_, 7, v_maxHeartbeats_4716_);
lean_ctor_set(v_reuseFailAlloc_4761_, 8, v_quotContext_4717_);
lean_ctor_set(v_reuseFailAlloc_4761_, 9, v_currMacroScope_4718_);
lean_ctor_set(v_reuseFailAlloc_4761_, 10, v_cancelTk_x3f_4719_);
lean_ctor_set(v_reuseFailAlloc_4761_, 11, v___x_4701_);
v___x_4732_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4734_; 
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 0, v___x_4732_);
v___x_4734_ = v___x_4708_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4732_);
lean_ctor_set(v_reuseFailAlloc_4760_, 1, v_currRecDepth_4704_);
lean_ctor_set(v_reuseFailAlloc_4760_, 2, v_ref_4705_);
lean_ctor_set_uint8(v_reuseFailAlloc_4760_, sizeof(void*)*3 + 1, v_suppressElabErrors_4706_);
v___x_4734_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4735_; 
lean_ctor_set_uint8(v___x_4734_, sizeof(void*)*3, v___x_4725_);
lean_inc(v___x_4728_);
lean_inc(v_name_4666_);
v___x_4735_ = lean_apply_7(v_act_4662_, v_name_4666_, v_c_4663_, v___x_4692_, v___x_4728_, v___x_4734_, v___y_4727_, lean_box(0));
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v_ngen_4739_; lean_object* v_cache_4740_; lean_object* v_cache_4741_; lean_object* v___x_4743_; 
lean_dec(v_name_4666_);
lean_dec(v_modName_4658_);
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
v___x_4737_ = lean_st_ref_get(v___x_4728_);
lean_dec(v___x_4728_);
v___x_4738_ = lean_st_ref_get(v___x_4699_);
lean_dec(v___x_4699_);
v_ngen_4739_ = lean_ctor_get(v___x_4738_, 2);
lean_inc_ref(v_ngen_4739_);
v_cache_4740_ = lean_ctor_get(v___x_4738_, 5);
lean_inc_ref(v_cache_4740_);
lean_dec(v___x_4738_);
v_cache_4741_ = lean_ctor_get(v___x_4737_, 1);
lean_inc_ref(v_cache_4741_);
lean_dec(v___x_4737_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 2, v_cache_4741_);
lean_ctor_set(v___x_4673_, 1, v_cache_4740_);
lean_ctor_set(v___x_4673_, 0, v_ngen_4739_);
v___x_4743_ = v___x_4673_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_ngen_4739_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_cache_4740_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_cache_4741_);
v___x_4743_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v___x_4744_ = lean_st_ref_swap(v_cacheRef_4660_, v___x_4743_);
lean_dec(v___x_4744_);
v___x_4745_ = lean_array_get_size(v_a_4736_);
v___x_4746_ = lean_nat_dec_lt(v___x_4675_, v___x_4745_);
if (v___x_4746_ == 0)
{
lean_dec(v_a_4736_);
return v_tree_4661_;
}
else
{
uint8_t v___x_4747_; 
v___x_4747_ = lean_nat_dec_le(v___x_4745_, v___x_4745_);
if (v___x_4747_ == 0)
{
if (v___x_4746_ == 0)
{
lean_dec(v_a_4736_);
return v_tree_4661_;
}
else
{
size_t v___x_4748_; size_t v___x_4749_; lean_object* v___x_4750_; 
v___x_4748_ = ((size_t)0ULL);
v___x_4749_ = lean_usize_of_nat(v___x_4745_);
v___x_4750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4736_, v___x_4748_, v___x_4749_, v_tree_4661_);
lean_dec(v_a_4736_);
return v___x_4750_;
}
}
else
{
size_t v___x_4751_; size_t v___x_4752_; lean_object* v___x_4753_; 
v___x_4751_ = ((size_t)0ULL);
v___x_4752_ = lean_usize_of_nat(v___x_4745_);
v___x_4753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4736_, v___x_4751_, v___x_4752_, v_tree_4661_);
lean_dec(v_a_4736_);
return v___x_4753_;
}
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec(v___x_4728_);
lean_dec(v___x_4699_);
lean_del_object(v___x_4673_);
v_a_4755_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4735_, 1);
v___x_4756_ = lean_st_ref_take(v_d_4659_);
v___x_4757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4757_, 0, v_modName_4658_);
lean_ctor_set(v___x_4757_, 1, v_name_4666_);
lean_ctor_set(v___x_4757_, 2, v_a_4755_);
v___x_4758_ = lean_array_push(v___x_4756_, v___x_4757_);
v___x_4759_ = lean_st_ref_put(v_d_4659_, v___x_4758_);
return v_tree_4661_;
}
}
}
}
v___jp_4762_:
{
if (v___y_4763_ == 0)
{
lean_object* v___x_4764_; lean_object* v_env_4765_; lean_object* v_nextMacroScope_4766_; lean_object* v_ngen_4767_; lean_object* v_auxDeclNGen_4768_; lean_object* v_traceState_4769_; lean_object* v_messages_4770_; lean_object* v_infoState_4771_; lean_object* v_snapshotTasks_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4782_; 
v___x_4764_ = lean_st_ref_take(v___x_4699_);
v_env_4765_ = lean_ctor_get(v___x_4764_, 0);
v_nextMacroScope_4766_ = lean_ctor_get(v___x_4764_, 1);
v_ngen_4767_ = lean_ctor_get(v___x_4764_, 2);
v_auxDeclNGen_4768_ = lean_ctor_get(v___x_4764_, 3);
v_traceState_4769_ = lean_ctor_get(v___x_4764_, 4);
v_messages_4770_ = lean_ctor_get(v___x_4764_, 6);
v_infoState_4771_ = lean_ctor_get(v___x_4764_, 7);
v_snapshotTasks_4772_ = lean_ctor_get(v___x_4764_, 8);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4782_ == 0)
{
lean_object* v_unused_4783_; 
v_unused_4783_ = lean_ctor_get(v___x_4764_, 5);
lean_dec(v_unused_4783_);
v___x_4774_ = v___x_4764_;
v_isShared_4775_ = v_isSharedCheck_4782_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_snapshotTasks_4772_);
lean_inc(v_infoState_4771_);
lean_inc(v_messages_4770_);
lean_inc(v_traceState_4769_);
lean_inc(v_auxDeclNGen_4768_);
lean_inc(v_ngen_4767_);
lean_inc(v_nextMacroScope_4766_);
lean_inc(v_env_4765_);
lean_dec(v___x_4764_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4782_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
v___x_4776_ = l_Lean_Kernel_enableDiag(v_env_4765_, v___x_4725_);
v___x_4777_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 5, v___x_4777_);
lean_ctor_set(v___x_4774_, 0, v___x_4776_);
v___x_4779_ = v___x_4774_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4776_);
lean_ctor_set(v_reuseFailAlloc_4781_, 1, v_nextMacroScope_4766_);
lean_ctor_set(v_reuseFailAlloc_4781_, 2, v_ngen_4767_);
lean_ctor_set(v_reuseFailAlloc_4781_, 3, v_auxDeclNGen_4768_);
lean_ctor_set(v_reuseFailAlloc_4781_, 4, v_traceState_4769_);
lean_ctor_set(v_reuseFailAlloc_4781_, 5, v___x_4777_);
lean_ctor_set(v_reuseFailAlloc_4781_, 6, v_messages_4770_);
lean_ctor_set(v_reuseFailAlloc_4781_, 7, v_infoState_4771_);
lean_ctor_set(v_reuseFailAlloc_4781_, 8, v_snapshotTasks_4772_);
v___x_4779_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_st_ref_put(v___x_4699_, v___x_4779_);
lean_inc(v___x_4699_);
v___y_4727_ = v___x_4699_;
goto v___jp_4726_;
}
}
}
else
{
lean_inc(v___x_4699_);
v___y_4727_ = v___x_4699_;
goto v___jp_4726_;
}
}
}
}
}
}
else
{
lean_dec(v_name_4666_);
lean_dec_ref(v_c_4663_);
lean_dec_ref(v_act_4662_);
lean_dec(v_modName_4658_);
lean_dec_ref(v_env_4657_);
lean_dec_ref(v_cctx_4656_);
return v_tree_4661_;
}
}
else
{
lean_dec_ref(v_c_4663_);
lean_dec_ref(v_act_4662_);
lean_dec(v_modName_4658_);
lean_dec_ref(v_env_4657_);
lean_dec_ref(v_cctx_4656_);
return v_tree_4661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4790_, lean_object* v_env_4791_, lean_object* v_modName_4792_, lean_object* v_d_4793_, lean_object* v_cacheRef_4794_, lean_object* v_tree_4795_, lean_object* v_act_4796_, lean_object* v_c_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4790_, v_env_4791_, v_modName_4792_, v_d_4793_, v_cacheRef_4794_, v_tree_4795_, v_act_4796_, v_c_4797_);
lean_dec(v_cacheRef_4794_);
lean_dec(v_d_4793_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4800_, lean_object* v_cctx_4801_, lean_object* v_env_4802_, lean_object* v_modName_4803_, lean_object* v_d_4804_, lean_object* v_cacheRef_4805_, lean_object* v_tree_4806_, lean_object* v_act_4807_, lean_object* v_c_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4801_, v_env_4802_, v_modName_4803_, v_d_4804_, v_cacheRef_4805_, v_tree_4806_, v_act_4807_, v_c_4808_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4811_, lean_object* v_cctx_4812_, lean_object* v_env_4813_, lean_object* v_modName_4814_, lean_object* v_d_4815_, lean_object* v_cacheRef_4816_, lean_object* v_tree_4817_, lean_object* v_act_4818_, lean_object* v_c_4819_, lean_object* v_a_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4811_, v_cctx_4812_, v_env_4813_, v_modName_4814_, v_d_4815_, v_cacheRef_4816_, v_tree_4817_, v_act_4818_, v_c_4819_);
lean_dec(v_cacheRef_4816_);
lean_dec(v_d_4815_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4822_, lean_object* v_as_4823_, size_t v_i_4824_, size_t v_stop_4825_, lean_object* v_b_4826_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4823_, v_i_4824_, v_stop_4825_, v_b_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4828_, lean_object* v_as_4829_, lean_object* v_i_4830_, lean_object* v_stop_4831_, lean_object* v_b_4832_){
_start:
{
size_t v_i_boxed_4833_; size_t v_stop_boxed_4834_; lean_object* v_res_4835_; 
v_i_boxed_4833_ = lean_unbox_usize(v_i_4830_);
lean_dec(v_i_4830_);
v_stop_boxed_4834_ = lean_unbox_usize(v_stop_4831_);
lean_dec(v_stop_4831_);
v_res_4835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4828_, v_as_4829_, v_i_boxed_4833_, v_stop_boxed_4834_, v_b_4832_);
lean_dec_ref(v_as_4829_);
return v_res_4835_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4836_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4837_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_4838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
lean_ctor_set(v___x_4838_, 1, v___x_4836_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4839_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4841_, lean_object* v_y_4842_){
_start:
{
lean_object* v_tree_4843_; lean_object* v_errors_4844_; lean_object* v_tree_4845_; lean_object* v_errors_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4855_; 
v_tree_4843_ = lean_ctor_get(v_x_4841_, 0);
lean_inc_ref(v_tree_4843_);
v_errors_4844_ = lean_ctor_get(v_x_4841_, 1);
lean_inc_ref(v_errors_4844_);
lean_dec_ref(v_x_4841_);
v_tree_4845_ = lean_ctor_get(v_y_4842_, 0);
v_errors_4846_ = lean_ctor_get(v_y_4842_, 1);
v_isSharedCheck_4855_ = !lean_is_exclusive(v_y_4842_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4848_ = v_y_4842_;
v_isShared_4849_ = v_isSharedCheck_4855_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_errors_4846_);
lean_inc(v_tree_4845_);
lean_dec(v_y_4842_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4855_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4853_; 
v___x_4850_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4843_, v_tree_4845_);
v___x_4851_ = l_Array_append___redArg(v_errors_4844_, v_errors_4846_);
lean_dec_ref(v_errors_4846_);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 1, v___x_4851_);
lean_ctor_set(v___x_4848_, 0, v___x_4850_);
v___x_4853_ = v___x_4848_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4850_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v___x_4851_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4856_, lean_object* v_x_4857_, lean_object* v_y_4858_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4857_, v_y_4858_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4861_){
_start:
{
lean_object* v___x_4862_; 
v___x_4862_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4863_, lean_object* v_tree_4864_){
_start:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4866_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4867_ = lean_st_ref_swap(v_d_4863_, v___x_4866_);
v___x_4868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4868_, 0, v_tree_4864_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4869_, lean_object* v_tree_4870_, lean_object* v_a_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4869_, v_tree_4870_);
lean_dec(v_d_4869_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4873_, lean_object* v_d_4874_, lean_object* v_tree_4875_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4874_, v_tree_4875_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4878_, lean_object* v_d_4879_, lean_object* v_tree_4880_, lean_object* v_a_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4878_, v_d_4879_, v_tree_4880_);
lean_dec(v_d_4879_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4883_, lean_object* v_env_4884_, lean_object* v_act_4885_, lean_object* v_d_4886_, lean_object* v_cacheRef_4887_, lean_object* v_tree_4888_, lean_object* v_mname_4889_, lean_object* v_mdata_4890_, lean_object* v_i_4891_){
_start:
{
lean_object* v_constants_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
v_constants_4893_ = lean_ctor_get(v_mdata_4890_, 2);
v___x_4894_ = lean_array_get_size(v_constants_4893_);
v___x_4895_ = lean_nat_dec_lt(v_i_4891_, v___x_4894_);
if (v___x_4895_ == 0)
{
lean_dec(v_i_4891_);
lean_dec(v_mname_4889_);
lean_dec_ref(v_act_4885_);
lean_dec_ref(v_env_4884_);
lean_dec_ref(v_cctx_4883_);
return v_tree_4888_;
}
else
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4896_ = lean_array_fget_borrowed(v_constants_4893_, v_i_4891_);
lean_inc(v___x_4896_);
v___x_4897_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4896_);
lean_inc_ref(v_act_4885_);
lean_inc(v_mname_4889_);
lean_inc_ref(v_env_4884_);
lean_inc_ref(v_cctx_4883_);
v___x_4898_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4883_, v_env_4884_, v_mname_4889_, v_d_4886_, v_cacheRef_4887_, v_tree_4888_, v_act_4885_, v___x_4897_);
v___x_4899_ = lean_unsigned_to_nat(1u);
v___x_4900_ = lean_nat_add(v_i_4891_, v___x_4899_);
lean_dec(v_i_4891_);
v_tree_4888_ = v___x_4898_;
v_i_4891_ = v___x_4900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4902_, lean_object* v_env_4903_, lean_object* v_act_4904_, lean_object* v_d_4905_, lean_object* v_cacheRef_4906_, lean_object* v_tree_4907_, lean_object* v_mname_4908_, lean_object* v_mdata_4909_, lean_object* v_i_4910_, lean_object* v_a_4911_){
_start:
{
lean_object* v_res_4912_; 
v_res_4912_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4902_, v_env_4903_, v_act_4904_, v_d_4905_, v_cacheRef_4906_, v_tree_4907_, v_mname_4908_, v_mdata_4909_, v_i_4910_);
lean_dec_ref(v_mdata_4909_);
lean_dec(v_cacheRef_4906_);
lean_dec(v_d_4905_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4913_, lean_object* v_cctx_4914_, lean_object* v_env_4915_, lean_object* v_act_4916_, lean_object* v_d_4917_, lean_object* v_cacheRef_4918_, lean_object* v_tree_4919_, lean_object* v_mname_4920_, lean_object* v_mdata_4921_, lean_object* v_i_4922_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4914_, v_env_4915_, v_act_4916_, v_d_4917_, v_cacheRef_4918_, v_tree_4919_, v_mname_4920_, v_mdata_4921_, v_i_4922_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4925_, lean_object* v_cctx_4926_, lean_object* v_env_4927_, lean_object* v_act_4928_, lean_object* v_d_4929_, lean_object* v_cacheRef_4930_, lean_object* v_tree_4931_, lean_object* v_mname_4932_, lean_object* v_mdata_4933_, lean_object* v_i_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4925_, v_cctx_4926_, v_env_4927_, v_act_4928_, v_d_4929_, v_cacheRef_4930_, v_tree_4931_, v_mname_4932_, v_mdata_4933_, v_i_4934_);
lean_dec_ref(v_mdata_4933_);
lean_dec(v_cacheRef_4930_);
lean_dec(v_d_4929_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4937_, lean_object* v_env_4938_, lean_object* v_act_4939_, lean_object* v_d_4940_, lean_object* v_cacheRef_4941_, lean_object* v_tree_4942_, lean_object* v_start_4943_, lean_object* v_stop_4944_){
_start:
{
uint8_t v___x_4946_; 
v___x_4946_ = lean_nat_dec_lt(v_start_4943_, v_stop_4944_);
if (v___x_4946_ == 0)
{
lean_object* v___x_4947_; 
lean_dec(v_start_4943_);
lean_dec_ref(v_act_4939_);
lean_dec_ref(v_env_4938_);
lean_dec_ref(v_cctx_4937_);
v___x_4947_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4940_, v_tree_4942_);
return v___x_4947_;
}
else
{
lean_object* v___x_4948_; lean_object* v_moduleData_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v_mname_4953_; lean_object* v_mdata_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4948_ = l_Lean_Environment_header(v_env_4938_);
v_moduleData_4949_ = lean_ctor_get(v___x_4948_, 6);
lean_inc_ref(v_moduleData_4949_);
v___x_4950_ = lean_box(0);
v___x_4951_ = l_Lean_instInhabitedModuleData_default;
v___x_4952_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4948_);
v_mname_4953_ = lean_array_get(v___x_4950_, v___x_4952_, v_start_4943_);
lean_dec_ref(v___x_4952_);
v_mdata_4954_ = lean_array_get(v___x_4951_, v_moduleData_4949_, v_start_4943_);
lean_dec_ref(v_moduleData_4949_);
v___x_4955_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4939_);
lean_inc_ref(v_env_4938_);
lean_inc_ref(v_cctx_4937_);
v___x_4956_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4937_, v_env_4938_, v_act_4939_, v_d_4940_, v_cacheRef_4941_, v_tree_4942_, v_mname_4953_, v_mdata_4954_, v___x_4955_);
lean_dec(v_mdata_4954_);
v___x_4957_ = lean_unsigned_to_nat(1u);
v___x_4958_ = lean_nat_add(v_start_4943_, v___x_4957_);
lean_dec(v_start_4943_);
v_tree_4942_ = v___x_4956_;
v_start_4943_ = v___x_4958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4960_, lean_object* v_env_4961_, lean_object* v_act_4962_, lean_object* v_d_4963_, lean_object* v_cacheRef_4964_, lean_object* v_tree_4965_, lean_object* v_start_4966_, lean_object* v_stop_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4960_, v_env_4961_, v_act_4962_, v_d_4963_, v_cacheRef_4964_, v_tree_4965_, v_start_4966_, v_stop_4967_);
lean_dec(v_stop_4967_);
lean_dec(v_cacheRef_4964_);
lean_dec(v_d_4963_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_4970_, lean_object* v_cctx_4971_, lean_object* v_env_4972_, lean_object* v_act_4973_, lean_object* v_d_4974_, lean_object* v_cacheRef_4975_, lean_object* v_tree_4976_, lean_object* v_start_4977_, lean_object* v_stop_4978_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4971_, v_env_4972_, v_act_4973_, v_d_4974_, v_cacheRef_4975_, v_tree_4976_, v_start_4977_, v_stop_4978_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_4981_, lean_object* v_cctx_4982_, lean_object* v_env_4983_, lean_object* v_act_4984_, lean_object* v_d_4985_, lean_object* v_cacheRef_4986_, lean_object* v_tree_4987_, lean_object* v_start_4988_, lean_object* v_stop_4989_, lean_object* v_a_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_4981_, v_cctx_4982_, v_env_4983_, v_act_4984_, v_d_4985_, v_cacheRef_4986_, v_tree_4987_, v_start_4988_, v_stop_4989_);
lean_dec(v_stop_4989_);
lean_dec(v_cacheRef_4986_);
lean_dec(v_d_4985_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_4992_, lean_object* v_ngen_4993_, lean_object* v_env_4994_, lean_object* v_act_4995_, lean_object* v_start_4996_, lean_object* v_stop_4997_){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_4999_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4993_);
v___x_5000_ = lean_st_mk_ref(v___x_4999_);
v___x_5001_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5002_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_5003_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4992_, v_env_4994_, v_act_4995_, v___x_5001_, v___x_5000_, v___x_5002_, v_start_4996_, v_stop_4997_);
lean_dec(v___x_5000_);
lean_dec(v___x_5001_);
return v___x_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5004_, lean_object* v_ngen_5005_, lean_object* v_env_5006_, lean_object* v_act_5007_, lean_object* v_start_5008_, lean_object* v_stop_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5004_, v_ngen_5005_, v_env_5006_, v_act_5007_, v_start_5008_, v_stop_5009_);
lean_dec(v_stop_5009_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5012_, lean_object* v_cctx_5013_, lean_object* v_ngen_5014_, lean_object* v_env_5015_, lean_object* v_act_5016_, lean_object* v_start_5017_, lean_object* v_stop_5018_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5013_, v_ngen_5014_, v_env_5015_, v_act_5016_, v_start_5017_, v_stop_5018_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5021_, lean_object* v_cctx_5022_, lean_object* v_ngen_5023_, lean_object* v_env_5024_, lean_object* v_act_5025_, lean_object* v_start_5026_, lean_object* v_stop_5027_, lean_object* v_a_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5021_, v_cctx_5022_, v_ngen_5023_, v_env_5024_, v_act_5025_, v_start_5026_, v_stop_5027_);
lean_dec(v_stop_5027_);
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5030_, lean_object* v_x1_5031_, lean_object* v_x2_5032_){
_start:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = lean_task_get_own(v_x2_5032_);
v___x_5034_ = lean_apply_2(v_inst_5030_, v_x1_5031_, v___x_5033_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5035_, lean_object* v_z_5036_, lean_object* v_tasks_5037_){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; 
v___x_5038_ = lean_unsigned_to_nat(0u);
v___x_5039_ = lean_array_get_size(v_tasks_5037_);
v___x_5040_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5041_ = lean_nat_dec_lt(v___x_5038_, v___x_5039_);
if (v___x_5041_ == 0)
{
lean_dec_ref(v_tasks_5037_);
lean_dec(v_inst_5035_);
return v_z_5036_;
}
else
{
lean_object* v___f_5042_; uint8_t v___x_5043_; 
v___f_5042_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5042_, 0, v_inst_5035_);
v___x_5043_ = lean_nat_dec_le(v___x_5039_, v___x_5039_);
if (v___x_5043_ == 0)
{
if (v___x_5041_ == 0)
{
lean_dec_ref(v___f_5042_);
lean_dec_ref(v_tasks_5037_);
return v_z_5036_;
}
else
{
size_t v___x_5044_; size_t v___x_5045_; lean_object* v___x_5046_; 
v___x_5044_ = ((size_t)0ULL);
v___x_5045_ = lean_usize_of_nat(v___x_5039_);
v___x_5046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5040_, v___f_5042_, v_tasks_5037_, v___x_5044_, v___x_5045_, v_z_5036_);
return v___x_5046_;
}
}
else
{
size_t v___x_5047_; size_t v___x_5048_; lean_object* v___x_5049_; 
v___x_5047_ = ((size_t)0ULL);
v___x_5048_ = lean_usize_of_nat(v___x_5039_);
v___x_5049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5040_, v___f_5042_, v_tasks_5037_, v___x_5047_, v___x_5048_, v_z_5036_);
return v___x_5049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5050_, lean_object* v_inst_5051_, lean_object* v_z_5052_, lean_object* v_tasks_5053_){
_start:
{
lean_object* v___x_5054_; 
v___x_5054_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5051_, v_z_5052_, v_tasks_5053_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5055_, lean_object* v___x_5056_, lean_object* v_____r_5057_){
_start:
{
lean_object* v___x_5058_; 
v___x_5058_ = lean_apply_2(v_toPure_5055_, lean_box(0), v___x_5056_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5059_, lean_object* v_setNGen_5060_, lean_object* v_toBind_5061_, lean_object* v_ngen_5062_){
_start:
{
lean_object* v_namePrefix_5063_; lean_object* v_idx_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5078_; 
v_namePrefix_5063_ = lean_ctor_get(v_ngen_5062_, 0);
v_idx_5064_ = lean_ctor_get(v_ngen_5062_, 1);
v_isSharedCheck_5078_ = !lean_is_exclusive(v_ngen_5062_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5066_ = v_ngen_5062_;
v_isShared_5067_ = v_isSharedCheck_5078_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_idx_5064_);
lean_inc(v_namePrefix_5063_);
lean_dec(v_ngen_5062_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5078_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5071_; 
lean_inc(v_idx_5064_);
lean_inc(v_namePrefix_5063_);
v___x_5068_ = l_Lean_Name_num___override(v_namePrefix_5063_, v_idx_5064_);
v___x_5069_ = lean_unsigned_to_nat(1u);
if (v_isShared_5067_ == 0)
{
lean_ctor_set(v___x_5066_, 1, v___x_5069_);
lean_ctor_set(v___x_5066_, 0, v___x_5068_);
v___x_5071_ = v___x_5066_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5068_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
lean_object* v___f_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___f_5072_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5072_, 0, v_toPure_5059_);
lean_closure_set(v___f_5072_, 1, v___x_5071_);
v___x_5073_ = lean_nat_add(v_idx_5064_, v___x_5069_);
lean_dec(v_idx_5064_);
v___x_5074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5074_, 0, v_namePrefix_5063_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
v___x_5075_ = lean_apply_1(v_setNGen_5060_, v___x_5074_);
v___x_5076_ = lean_apply_4(v_toBind_5061_, lean_box(0), lean_box(0), v___x_5075_, v___f_5072_);
return v___x_5076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5079_, lean_object* v_inst_5080_){
_start:
{
lean_object* v_toApplicative_5081_; lean_object* v_toBind_5082_; lean_object* v_getNGen_5083_; lean_object* v_setNGen_5084_; lean_object* v_toPure_5085_; lean_object* v___f_5086_; lean_object* v___x_5087_; 
v_toApplicative_5081_ = lean_ctor_get(v_inst_5079_, 0);
lean_inc_ref(v_toApplicative_5081_);
v_toBind_5082_ = lean_ctor_get(v_inst_5079_, 1);
lean_inc_n(v_toBind_5082_, 2);
lean_dec_ref(v_inst_5079_);
v_getNGen_5083_ = lean_ctor_get(v_inst_5080_, 0);
lean_inc(v_getNGen_5083_);
v_setNGen_5084_ = lean_ctor_get(v_inst_5080_, 1);
lean_inc(v_setNGen_5084_);
lean_dec_ref(v_inst_5080_);
v_toPure_5085_ = lean_ctor_get(v_toApplicative_5081_, 1);
lean_inc(v_toPure_5085_);
lean_dec_ref(v_toApplicative_5081_);
v___f_5086_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5086_, 0, v_toPure_5085_);
lean_closure_set(v___f_5086_, 1, v_setNGen_5084_);
lean_closure_set(v___f_5086_, 2, v_toBind_5082_);
v___x_5087_ = lean_apply_4(v_toBind_5082_, lean_box(0), lean_box(0), v_getNGen_5083_, v___f_5086_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5088_, lean_object* v_inst_5089_, lean_object* v_inst_5090_){
_start:
{
lean_object* v___x_5091_; 
v___x_5091_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5089_, v_inst_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5092_, lean_object* v_env_5093_, lean_object* v_modName_5094_, lean_object* v_d_5095_, lean_object* v_val_5096_, lean_object* v_act_5097_, lean_object* v_as_5098_, size_t v_sz_5099_, size_t v_i_5100_, lean_object* v_b_5101_){
_start:
{
uint8_t v___x_5103_; 
v___x_5103_ = lean_usize_dec_lt(v_i_5100_, v_sz_5099_);
if (v___x_5103_ == 0)
{
lean_dec_ref(v_act_5097_);
lean_dec(v_modName_5094_);
lean_dec_ref(v_env_5093_);
lean_dec_ref(v_cctx_5092_);
return v_b_5101_;
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5105_; size_t v___x_5106_; size_t v___x_5107_; 
v_a_5104_ = lean_array_uget_borrowed(v_as_5098_, v_i_5100_);
lean_inc(v_a_5104_);
lean_inc_ref(v_act_5097_);
lean_inc(v_modName_5094_);
lean_inc_ref(v_env_5093_);
lean_inc_ref(v_cctx_5092_);
v___x_5105_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5092_, v_env_5093_, v_modName_5094_, v_d_5095_, v_val_5096_, v_b_5101_, v_act_5097_, v_a_5104_);
v___x_5106_ = ((size_t)1ULL);
v___x_5107_ = lean_usize_add(v_i_5100_, v___x_5106_);
v_i_5100_ = v___x_5107_;
v_b_5101_ = v___x_5105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5109_, lean_object* v_env_5110_, lean_object* v_modName_5111_, lean_object* v_d_5112_, lean_object* v_val_5113_, lean_object* v_act_5114_, lean_object* v_as_5115_, lean_object* v_sz_5116_, lean_object* v_i_5117_, lean_object* v_b_5118_, lean_object* v___y_5119_){
_start:
{
size_t v_sz_boxed_5120_; size_t v_i_boxed_5121_; lean_object* v_res_5122_; 
v_sz_boxed_5120_ = lean_unbox_usize(v_sz_5116_);
lean_dec(v_sz_5116_);
v_i_boxed_5121_ = lean_unbox_usize(v_i_5117_);
lean_dec(v_i_5117_);
v_res_5122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5109_, v_env_5110_, v_modName_5111_, v_d_5112_, v_val_5113_, v_act_5114_, v_as_5115_, v_sz_boxed_5120_, v_i_boxed_5121_, v_b_5118_);
lean_dec_ref(v_as_5115_);
lean_dec(v_val_5113_);
lean_dec(v_d_5112_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5123_, lean_object* v_ngen_5124_, lean_object* v_env_5125_, lean_object* v_d_5126_, lean_object* v_act_5127_){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v_mainModule_5134_; lean_object* v___x_5135_; size_t v_sz_5136_; size_t v___x_5137_; lean_object* v___x_5138_; 
v___x_5129_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5124_);
v___x_5130_ = lean_st_mk_ref(v___x_5129_);
v___x_5131_ = 1;
v___x_5132_ = l_Lean_Environment_getLocalConstantInfos(v_env_5125_, v___x_5131_);
v___x_5133_ = l_Lean_Environment_header(v_env_5125_);
v_mainModule_5134_ = lean_ctor_get(v___x_5133_, 0);
lean_inc(v_mainModule_5134_);
lean_dec_ref(v___x_5133_);
v___x_5135_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v_sz_5136_ = lean_array_size(v___x_5132_);
v___x_5137_ = ((size_t)0ULL);
v___x_5138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5123_, v_env_5125_, v_mainModule_5134_, v_d_5126_, v___x_5130_, v_act_5127_, v___x_5132_, v_sz_5136_, v___x_5137_, v___x_5135_);
lean_dec_ref(v___x_5132_);
lean_dec(v___x_5130_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5139_, lean_object* v_ngen_5140_, lean_object* v_env_5141_, lean_object* v_d_5142_, lean_object* v_act_5143_, lean_object* v_a_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5139_, v_ngen_5140_, v_env_5141_, v_d_5142_, v_act_5143_);
lean_dec(v_d_5142_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5146_, lean_object* v_cctx_5147_, lean_object* v_ngen_5148_, lean_object* v_env_5149_, lean_object* v_d_5150_, lean_object* v_act_5151_){
_start:
{
lean_object* v___x_5153_; 
v___x_5153_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5147_, v_ngen_5148_, v_env_5149_, v_d_5150_, v_act_5151_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5154_, lean_object* v_cctx_5155_, lean_object* v_ngen_5156_, lean_object* v_env_5157_, lean_object* v_d_5158_, lean_object* v_act_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5154_, v_cctx_5155_, v_ngen_5156_, v_env_5157_, v_d_5158_, v_act_5159_);
lean_dec(v_d_5158_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5162_, lean_object* v_cctx_5163_, lean_object* v_env_5164_, lean_object* v_modName_5165_, lean_object* v_d_5166_, lean_object* v_val_5167_, lean_object* v_act_5168_, lean_object* v_as_5169_, size_t v_sz_5170_, size_t v_i_5171_, lean_object* v_b_5172_){
_start:
{
lean_object* v___x_5174_; 
v___x_5174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5163_, v_env_5164_, v_modName_5165_, v_d_5166_, v_val_5167_, v_act_5168_, v_as_5169_, v_sz_5170_, v_i_5171_, v_b_5172_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5175_, lean_object* v_cctx_5176_, lean_object* v_env_5177_, lean_object* v_modName_5178_, lean_object* v_d_5179_, lean_object* v_val_5180_, lean_object* v_act_5181_, lean_object* v_as_5182_, lean_object* v_sz_5183_, lean_object* v_i_5184_, lean_object* v_b_5185_, lean_object* v___y_5186_){
_start:
{
size_t v_sz_boxed_5187_; size_t v_i_boxed_5188_; lean_object* v_res_5189_; 
v_sz_boxed_5187_ = lean_unbox_usize(v_sz_5183_);
lean_dec(v_sz_5183_);
v_i_boxed_5188_ = lean_unbox_usize(v_i_5184_);
lean_dec(v_i_5184_);
v_res_5189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5175_, v_cctx_5176_, v_env_5177_, v_modName_5178_, v_d_5179_, v_val_5180_, v_act_5181_, v_as_5182_, v_sz_boxed_5187_, v_i_boxed_5188_, v_b_5185_);
lean_dec_ref(v_as_5182_);
lean_dec(v_val_5180_);
lean_dec(v_d_5179_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5190_, lean_object* v_x_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_){
_start:
{
if (lean_obj_tag(v_x_5191_) == 0)
{
lean_object* v___x_5197_; 
v___x_5197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5197_, 0, v_x_5190_);
return v___x_5197_;
}
else
{
lean_object* v_head_5198_; lean_object* v_tail_5199_; lean_object* v___x_5200_; 
v_head_5198_ = lean_ctor_get(v_x_5191_, 0);
lean_inc(v_head_5198_);
v_tail_5199_ = lean_ctor_get(v_x_5191_, 1);
lean_inc(v_tail_5199_);
lean_dec_ref_known(v_x_5191_, 2);
v___x_5200_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5190_, v_head_5198_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5200_, 1);
v_x_5190_ = v_a_5201_;
v_x_5191_ = v_tail_5199_;
goto _start;
}
else
{
lean_dec(v_tail_5199_);
return v___x_5200_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5203_, lean_object* v_x_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5203_, v_x_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5211_, lean_object* v_keys_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_){
_start:
{
lean_object* v___x_5218_; 
v___x_5218_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5211_, v_keys_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5219_, lean_object* v_keys_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5219_, v_keys_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v_a_5221_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5227_, lean_object* v_t_5228_, lean_object* v_keys_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5228_, v_keys_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5236_, lean_object* v_t_5237_, lean_object* v_keys_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5236_, v_t_5237_, v_keys_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
lean_dec(v_a_5242_);
lean_dec_ref(v_a_5241_);
lean_dec(v_a_5240_);
lean_dec_ref(v_a_5239_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5245_, lean_object* v_x_5246_, lean_object* v_x_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v___x_5253_; 
v___x_5253_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5246_, v_x_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5254_, lean_object* v_x_5255_, lean_object* v_x_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5254_, v_x_5255_, v_x_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_);
lean_dec(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5263_, size_t v_sz_5264_, size_t v_i_5265_, lean_object* v_b_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
uint8_t v___x_5273_; 
v___x_5273_ = lean_usize_dec_lt(v_i_5265_, v_sz_5264_);
if (v___x_5273_ == 0)
{
lean_object* v___x_5274_; 
v___x_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5274_, 0, v_b_5266_);
return v___x_5274_;
}
else
{
lean_object* v_a_5275_; lean_object* v___x_5276_; 
v_a_5275_ = lean_array_uget_borrowed(v_as_5263_, v_i_5265_);
v___x_5276_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5275_, v_b_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_);
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5289_; 
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5289_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5289_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
if (lean_obj_tag(v_a_5277_) == 0)
{
lean_object* v_a_5281_; lean_object* v___x_5283_; 
v_a_5281_ = lean_ctor_get(v_a_5277_, 0);
lean_inc(v_a_5281_);
lean_dec_ref_known(v_a_5277_, 1);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 0, v_a_5281_);
v___x_5283_ = v___x_5279_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_a_5281_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
else
{
lean_object* v_a_5285_; size_t v___x_5286_; size_t v___x_5287_; 
lean_del_object(v___x_5279_);
v_a_5285_ = lean_ctor_get(v_a_5277_, 0);
lean_inc(v_a_5285_);
lean_dec_ref_known(v_a_5277_, 1);
v___x_5286_ = ((size_t)1ULL);
v___x_5287_ = lean_usize_add(v_i_5265_, v___x_5286_);
v_i_5265_ = v___x_5287_;
v_b_5266_ = v_a_5285_;
goto _start;
}
}
}
else
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5297_; 
v_a_5290_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5292_ = v___x_5276_;
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5276_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5295_; 
if (v_isShared_5293_ == 0)
{
v___x_5295_ = v___x_5292_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_){
_start:
{
lean_object* v___x_5305_; uint8_t v___x_5306_; 
v___x_5305_ = lean_unsigned_to_nat(0u);
v___x_5306_ = lean_nat_dec_eq(v_next_5298_, v___x_5305_);
if (v___x_5306_ == 0)
{
lean_object* v___x_5307_; 
v___x_5307_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v_snd_5309_; lean_object* v_fst_5310_; lean_object* v_fst_5311_; lean_object* v_snd_5312_; lean_object* v___x_5313_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref_known(v___x_5307_, 1);
v_snd_5309_ = lean_ctor_get(v_a_5308_, 1);
lean_inc(v_snd_5309_);
v_fst_5310_ = lean_ctor_get(v_a_5308_, 0);
lean_inc(v_fst_5310_);
lean_dec(v_a_5308_);
v_fst_5311_ = lean_ctor_get(v_snd_5309_, 0);
lean_inc(v_fst_5311_);
v_snd_5312_ = lean_ctor_get(v_snd_5309_, 1);
lean_inc(v_snd_5312_);
lean_dec(v_snd_5309_);
v___x_5313_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5311_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; lean_object* v_buckets_5315_; lean_object* v___x_5316_; size_t v_sz_5317_; size_t v___x_5318_; lean_object* v___x_5319_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_a_5314_);
lean_dec_ref_known(v___x_5313_, 1);
v_buckets_5315_ = lean_ctor_get(v_snd_5312_, 1);
v___x_5316_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5317_ = lean_array_size(v_buckets_5315_);
v___x_5318_ = ((size_t)0ULL);
v___x_5319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5315_, v_sz_5317_, v___x_5318_, v___x_5316_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
if (lean_obj_tag(v___x_5319_) == 0)
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5333_; 
v_a_5320_ = lean_ctor_get(v___x_5319_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5319_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5322_ = v___x_5319_;
v_isShared_5323_ = v_isSharedCheck_5333_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5319_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5333_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5331_; 
v___x_5324_ = lean_st_ref_take(v_a_5299_);
v___x_5325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5325_, 0, v___x_5316_);
lean_ctor_set(v___x_5325_, 1, v_fst_5311_);
lean_ctor_set(v___x_5325_, 2, v_snd_5312_);
lean_ctor_set(v___x_5325_, 3, v___x_5316_);
v___x_5326_ = lean_array_set(v___x_5324_, v_next_5298_, v___x_5325_);
v___x_5327_ = lean_st_ref_put(v_a_5299_, v___x_5326_);
v___x_5328_ = l_Array_append___redArg(v_fst_5310_, v_a_5314_);
lean_dec(v_a_5314_);
v___x_5329_ = l_Array_append___redArg(v___x_5328_, v_a_5320_);
lean_dec(v_a_5320_);
if (v_isShared_5323_ == 0)
{
lean_ctor_set(v___x_5322_, 0, v___x_5329_);
v___x_5331_ = v___x_5322_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v___x_5329_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
else
{
lean_dec(v_a_5314_);
lean_dec(v_snd_5312_);
lean_dec(v_fst_5311_);
lean_dec(v_fst_5310_);
return v___x_5319_;
}
}
else
{
lean_dec(v_snd_5312_);
lean_dec(v_fst_5311_);
lean_dec(v_fst_5310_);
return v___x_5313_;
}
}
else
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5341_; 
v_a_5334_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5336_ = v___x_5307_;
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5307_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5339_; 
if (v_isShared_5337_ == 0)
{
v___x_5339_ = v___x_5336_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
else
{
lean_object* v___x_5342_; lean_object* v___x_5343_; 
v___x_5342_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5342_);
return v___x_5343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_){
_start:
{
if (lean_obj_tag(v_a_5344_) == 0)
{
lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5352_, 0, v_a_5345_);
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5352_);
return v___x_5353_;
}
else
{
lean_object* v_value_5354_; lean_object* v_tail_5355_; lean_object* v___x_5356_; 
v_value_5354_ = lean_ctor_get(v_a_5344_, 1);
v_tail_5355_ = lean_ctor_get(v_a_5344_, 2);
v___x_5356_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5354_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5358_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v___x_5356_, 1);
v___x_5358_ = l_Array_append___redArg(v_a_5345_, v_a_5357_);
lean_dec(v_a_5357_);
v_a_5344_ = v_tail_5355_;
v_a_5345_ = v___x_5358_;
goto _start;
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec_ref(v_a_5345_);
v_a_5360_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5356_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5356_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5368_, v_a_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec(v_a_5368_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5377_, lean_object* v_sz_5378_, lean_object* v_i_5379_, lean_object* v_b_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
size_t v_sz_boxed_5387_; size_t v_i_boxed_5388_; lean_object* v_res_5389_; 
v_sz_boxed_5387_ = lean_unbox_usize(v_sz_5378_);
lean_dec(v_sz_5378_);
v_i_boxed_5388_ = lean_unbox_usize(v_i_5379_);
lean_dec(v_i_5379_);
v_res_5389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5377_, v_sz_boxed_5387_, v_i_boxed_5388_, v_b_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v_as_5377_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_);
lean_dec(v_a_5395_);
lean_dec_ref(v_a_5394_);
lean_dec(v_a_5393_);
lean_dec_ref(v_a_5392_);
lean_dec(v_a_5391_);
lean_dec(v_next_5390_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5398_, lean_object* v_next_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_){
_start:
{
lean_object* v___x_5406_; 
v___x_5406_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_);
return v___x_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5407_, lean_object* v_next_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v_res_5415_; 
v_res_5415_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5407_, v_next_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_);
lean_dec(v_a_5413_);
lean_dec_ref(v_a_5412_);
lean_dec(v_a_5411_);
lean_dec_ref(v_a_5410_);
lean_dec(v_a_5409_);
lean_dec(v_next_5408_);
return v_res_5415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_){
_start:
{
lean_object* v___x_5425_; 
v___x_5425_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5417_, v_a_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_){
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5426_, v_a_5427_, v_a_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
lean_dec(v___y_5433_);
lean_dec_ref(v___y_5432_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
lean_dec(v___y_5429_);
lean_dec(v_a_5427_);
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5436_, lean_object* v_as_5437_, size_t v_sz_5438_, size_t v_i_5439_, lean_object* v_b_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v___x_5447_; 
v___x_5447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5437_, v_sz_5438_, v_i_5439_, v_b_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5448_, lean_object* v_as_5449_, lean_object* v_sz_5450_, lean_object* v_i_5451_, lean_object* v_b_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
size_t v_sz_boxed_5459_; size_t v_i_boxed_5460_; lean_object* v_res_5461_; 
v_sz_boxed_5459_ = lean_unbox_usize(v_sz_5450_);
lean_dec(v_sz_5450_);
v_i_boxed_5460_ = lean_unbox_usize(v_i_5451_);
lean_dec(v_i_5451_);
v_res_5461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5448_, v_as_5449_, v_sz_boxed_5459_, v_i_boxed_5460_, v_b_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5453_);
lean_dec_ref(v_as_5449_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5462_, lean_object* v_rest_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_){
_start:
{
lean_object* v___x_5470_; uint8_t v___x_5471_; 
v___x_5470_ = lean_unsigned_to_nat(0u);
v___x_5471_ = lean_nat_dec_eq(v_next_5462_, v___x_5470_);
if (v___x_5471_ == 0)
{
lean_object* v___x_5472_; 
v___x_5472_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5462_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_);
if (lean_obj_tag(v___x_5472_) == 0)
{
lean_object* v_a_5473_; lean_object* v_snd_5474_; 
v_a_5473_ = lean_ctor_get(v___x_5472_, 0);
lean_inc(v_a_5473_);
lean_dec_ref_known(v___x_5472_, 1);
v_snd_5474_ = lean_ctor_get(v_a_5473_, 1);
lean_inc(v_snd_5474_);
lean_dec(v_a_5473_);
if (lean_obj_tag(v_rest_5463_) == 0)
{
lean_object* v___x_5475_; 
lean_dec(v_snd_5474_);
v___x_5475_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5462_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_);
lean_dec(v_next_5462_);
return v___x_5475_;
}
else
{
lean_object* v_fst_5476_; lean_object* v_snd_5477_; lean_object* v_head_5478_; lean_object* v_tail_5479_; lean_object* v___x_5480_; uint8_t v___x_5481_; 
lean_dec(v_next_5462_);
v_fst_5476_ = lean_ctor_get(v_snd_5474_, 0);
lean_inc(v_fst_5476_);
v_snd_5477_ = lean_ctor_get(v_snd_5474_, 1);
lean_inc(v_snd_5477_);
lean_dec(v_snd_5474_);
v_head_5478_ = lean_ctor_get(v_rest_5463_, 0);
v_tail_5479_ = lean_ctor_get(v_rest_5463_, 1);
v___x_5480_ = lean_box(3);
v___x_5481_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5478_, v___x_5480_);
if (v___x_5481_ == 0)
{
lean_object* v___x_5482_; 
lean_dec(v_fst_5476_);
v___x_5482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5477_, v_head_5478_, v___x_5470_);
lean_dec(v_snd_5477_);
v_next_5462_ = v___x_5482_;
v_rest_5463_ = v_tail_5479_;
goto _start;
}
else
{
lean_dec(v_snd_5477_);
v_next_5462_ = v_fst_5476_;
v_rest_5463_ = v_tail_5479_;
goto _start;
}
}
}
else
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5492_; 
lean_dec(v_next_5462_);
v_a_5485_ = lean_ctor_get(v___x_5472_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5472_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5487_ = v___x_5472_;
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v___x_5472_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5488_ == 0)
{
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
else
{
lean_object* v___x_5493_; lean_object* v___x_5494_; 
lean_dec(v_next_5462_);
v___x_5493_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5494_, 0, v___x_5493_);
return v___x_5494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5495_, lean_object* v_rest_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5495_, v_rest_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
lean_dec(v_a_5501_);
lean_dec_ref(v_a_5500_);
lean_dec(v_a_5499_);
lean_dec_ref(v_a_5498_);
lean_dec(v_a_5497_);
lean_dec(v_rest_5496_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5504_, lean_object* v_next_5505_, lean_object* v_rest_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_){
_start:
{
lean_object* v___x_5513_; 
v___x_5513_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5505_, v_rest_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
return v___x_5513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5514_, lean_object* v_next_5515_, lean_object* v_rest_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5514_, v_next_5515_, v_rest_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_);
lean_dec(v_a_5521_);
lean_dec_ref(v_a_5520_);
lean_dec(v_a_5519_);
lean_dec_ref(v_a_5518_);
lean_dec(v_a_5517_);
lean_dec(v_rest_5516_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5524_, lean_object* v_path_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_){
_start:
{
if (lean_obj_tag(v_path_5525_) == 0)
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
v___x_5531_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5531_);
lean_ctor_set(v___x_5532_, 1, v_t_5524_);
v___x_5533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5533_, 0, v___x_5532_);
return v___x_5533_;
}
else
{
lean_object* v_head_5534_; lean_object* v_tail_5535_; lean_object* v_roots_5536_; lean_object* v___x_5537_; lean_object* v_idx_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; 
v_head_5534_ = lean_ctor_get(v_path_5525_, 0);
lean_inc(v_head_5534_);
v_tail_5535_ = lean_ctor_get(v_path_5525_, 1);
lean_inc(v_tail_5535_);
lean_dec_ref_known(v_path_5525_, 2);
v_roots_5536_ = lean_ctor_get(v_t_5524_, 1);
v___x_5537_ = lean_unsigned_to_nat(0u);
v_idx_5538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5536_, v_head_5534_, v___x_5537_);
lean_dec(v_head_5534_);
v___x_5539_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5539_, 0, lean_box(0));
lean_closure_set(v___x_5539_, 1, v_idx_5538_);
lean_closure_set(v___x_5539_, 2, v_tail_5535_);
v___x_5540_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5524_, v___x_5539_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
return v___x_5540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5541_, lean_object* v_path_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_){
_start:
{
lean_object* v_res_5548_; 
v_res_5548_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5541_, v_path_5542_, v_a_5543_, v_a_5544_, v_a_5545_, v_a_5546_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
lean_dec(v_a_5544_);
lean_dec_ref(v_a_5543_);
return v_res_5548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5549_, lean_object* v_t_5550_, lean_object* v_path_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_){
_start:
{
lean_object* v___x_5557_; 
v___x_5557_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5550_, v_path_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_);
return v___x_5557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5558_, lean_object* v_t_5559_, lean_object* v_path_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_){
_start:
{
lean_object* v_res_5566_; 
v_res_5566_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5558_, v_t_5559_, v_path_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_);
lean_dec(v_a_5564_);
lean_dec_ref(v_a_5563_);
lean_dec(v_a_5562_);
lean_dec_ref(v_a_5561_);
return v_res_5566_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5567_, lean_object* v_b_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_){
_start:
{
if (lean_obj_tag(v_as_x27_5567_) == 0)
{
lean_object* v___x_5574_; 
v___x_5574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5574_, 0, v_b_5568_);
return v___x_5574_;
}
else
{
lean_object* v_head_5575_; lean_object* v_tail_5576_; lean_object* v_fst_5577_; lean_object* v_snd_5578_; lean_object* v___x_5579_; 
v_head_5575_ = lean_ctor_get(v_as_x27_5567_, 0);
v_tail_5576_ = lean_ctor_get(v_as_x27_5567_, 1);
v_fst_5577_ = lean_ctor_get(v_b_5568_, 0);
lean_inc(v_fst_5577_);
v_snd_5578_ = lean_ctor_get(v_b_5568_, 1);
lean_inc(v_snd_5578_);
lean_dec_ref(v_b_5568_);
lean_inc(v_head_5575_);
v___x_5579_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5578_, v_head_5575_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v_a_5580_; lean_object* v_fst_5581_; lean_object* v_snd_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5591_; 
v_a_5580_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_a_5580_);
lean_dec_ref_known(v___x_5579_, 1);
v_fst_5581_ = lean_ctor_get(v_a_5580_, 0);
v_snd_5582_ = lean_ctor_get(v_a_5580_, 1);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_a_5580_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5584_ = v_a_5580_;
v_isShared_5585_ = v_isSharedCheck_5591_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_snd_5582_);
lean_inc(v_fst_5581_);
lean_dec(v_a_5580_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5591_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5586_; lean_object* v___x_5588_; 
v___x_5586_ = l_Array_append___redArg(v_fst_5577_, v_fst_5581_);
lean_dec(v_fst_5581_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set(v___x_5584_, 0, v___x_5586_);
v___x_5588_ = v___x_5584_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5586_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v_snd_5582_);
v___x_5588_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
v_as_x27_5567_ = v_tail_5576_;
v_b_5568_ = v___x_5588_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5577_);
return v___x_5579_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5592_, lean_object* v_b_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_){
_start:
{
lean_object* v_res_5599_; 
v_res_5599_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5592_, v_b_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
lean_dec(v_as_x27_5592_);
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5600_, lean_object* v_keys_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_){
_start:
{
lean_object* v_allExtracted_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; 
v_allExtracted_5607_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5608_, 0, v_allExtracted_5607_);
lean_ctor_set(v___x_5608_, 1, v_t_5600_);
v___x_5609_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5601_, v___x_5608_, v_a_5602_, v_a_5603_, v_a_5604_, v_a_5605_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_object* v_a_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5626_; 
v_a_5610_ = lean_ctor_get(v___x_5609_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5612_ = v___x_5609_;
v_isShared_5613_ = v_isSharedCheck_5626_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_a_5610_);
lean_dec(v___x_5609_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5626_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v_fst_5614_; lean_object* v_snd_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5625_; 
v_fst_5614_ = lean_ctor_get(v_a_5610_, 0);
v_snd_5615_ = lean_ctor_get(v_a_5610_, 1);
v_isSharedCheck_5625_ = !lean_is_exclusive(v_a_5610_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5617_ = v_a_5610_;
v_isShared_5618_ = v_isSharedCheck_5625_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_snd_5615_);
lean_inc(v_fst_5614_);
lean_dec(v_a_5610_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5625_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_fst_5614_);
lean_ctor_set(v_reuseFailAlloc_5624_, 1, v_snd_5615_);
v___x_5620_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
lean_object* v___x_5622_; 
if (v_isShared_5613_ == 0)
{
lean_ctor_set(v___x_5612_, 0, v___x_5620_);
v___x_5622_ = v___x_5612_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5620_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
}
else
{
return v___x_5609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5627_, lean_object* v_keys_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_){
_start:
{
lean_object* v_res_5634_; 
v_res_5634_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5627_, v_keys_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_);
lean_dec(v_a_5632_);
lean_dec_ref(v_a_5631_);
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
lean_dec(v_keys_5628_);
return v_res_5634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5635_, lean_object* v_t_5636_, lean_object* v_keys_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_){
_start:
{
lean_object* v___x_5643_; 
v___x_5643_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5636_, v_keys_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5644_, lean_object* v_t_5645_, lean_object* v_keys_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v_res_5652_; 
v_res_5652_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5644_, v_t_5645_, v_keys_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_a_5648_);
lean_dec_ref(v_a_5647_);
lean_dec(v_keys_5646_);
return v_res_5652_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5653_, lean_object* v_as_5654_, lean_object* v_as_x27_5655_, lean_object* v_b_5656_, lean_object* v_a_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_){
_start:
{
lean_object* v___x_5663_; 
v___x_5663_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5655_, v_b_5656_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_);
return v___x_5663_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5664_, lean_object* v_as_5665_, lean_object* v_as_x27_5666_, lean_object* v_b_5667_, lean_object* v_a_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v_res_5674_; 
v_res_5674_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5664_, v_as_5665_, v_as_x27_5666_, v_b_5667_, v_a_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_as_x27_5666_);
lean_dec(v_as_5665_);
return v_res_5674_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5676_; lean_object* v___x_5677_; 
v___x_5676_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5677_ = l_Lean_stringToMessageData(v___x_5676_);
return v___x_5677_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5679_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5680_ = l_Lean_stringToMessageData(v___x_5679_);
return v___x_5680_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5682_; lean_object* v___x_5683_; 
v___x_5682_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5683_ = l_Lean_stringToMessageData(v___x_5682_);
return v___x_5683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5684_, lean_object* v_inst_5685_, lean_object* v_inst_5686_, lean_object* v_inst_5687_, lean_object* v_f_5688_){
_start:
{
lean_object* v_module_5689_; lean_object* v_const_5690_; lean_object* v_exception_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; 
v_module_5689_ = lean_ctor_get(v_f_5688_, 0);
lean_inc(v_module_5689_);
v_const_5690_ = lean_ctor_get(v_f_5688_, 1);
lean_inc(v_const_5690_);
v_exception_5691_ = lean_ctor_get(v_f_5688_, 2);
lean_inc_ref(v_exception_5691_);
lean_dec_ref(v_f_5688_);
v___x_5692_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5693_ = l_Lean_MessageData_ofName(v_const_5690_);
v___x_5694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5692_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5694_);
lean_ctor_set(v___x_5696_, 1, v___x_5695_);
v___x_5697_ = l_Lean_MessageData_ofName(v_module_5689_);
v___x_5698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5698_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v___x_5701_ = l_Lean_Exception_toMessageData(v_exception_5691_);
v___x_5702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5700_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = l_Lean_logError___redArg(v_inst_5684_, v_inst_5685_, v_inst_5686_, v_inst_5687_, v___x_5702_);
return v___x_5703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5704_, lean_object* v_inst_5705_, lean_object* v_inst_5706_, lean_object* v_inst_5707_, lean_object* v_inst_5708_, lean_object* v_f_5709_){
_start:
{
lean_object* v___x_5710_; 
v___x_5710_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5705_, v_inst_5706_, v_inst_5707_, v_inst_5708_, v_f_5709_);
return v___x_5710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5711_, lean_object* v_toPure_5712_, lean_object* v_t_5713_){
_start:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5714_ = lean_array_push(v_tasks_5711_, v_t_5713_);
v___x_5715_ = lean_apply_2(v_toPure_5712_, lean_box(0), v___x_5714_);
return v___x_5715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5716_, lean_object* v_inst_5717_, lean_object* v_cctx_5718_, lean_object* v_env_5719_, lean_object* v_act_5720_, lean_object* v_constantsPerTask_5721_, lean_object* v_n_5722_, lean_object* v_ngen_5723_, lean_object* v_tasks_5724_, lean_object* v_start_5725_, lean_object* v_cnt_5726_, lean_object* v_idx_5727_){
_start:
{
lean_object* v___x_5728_; lean_object* v_toApplicative_5729_; lean_object* v_moduleData_5730_; lean_object* v_toBind_5731_; lean_object* v_toPure_5732_; lean_object* v___x_5733_; uint8_t v___x_5734_; 
v___x_5728_ = l_Lean_Environment_header(v_env_5719_);
v_toApplicative_5729_ = lean_ctor_get(v_inst_5716_, 0);
v_moduleData_5730_ = lean_ctor_get(v___x_5728_, 6);
lean_inc_ref(v_moduleData_5730_);
lean_dec_ref(v___x_5728_);
v_toBind_5731_ = lean_ctor_get(v_inst_5716_, 1);
v_toPure_5732_ = lean_ctor_get(v_toApplicative_5729_, 1);
v___x_5733_ = lean_array_get_size(v_moduleData_5730_);
v___x_5734_ = lean_nat_dec_lt(v_idx_5727_, v___x_5733_);
if (v___x_5734_ == 0)
{
uint8_t v___x_5735_; 
lean_inc(v_toPure_5732_);
lean_inc(v_toBind_5731_);
lean_dec_ref(v_moduleData_5730_);
lean_dec(v_idx_5727_);
lean_dec(v_cnt_5726_);
lean_dec(v_constantsPerTask_5721_);
lean_dec_ref(v_inst_5716_);
v___x_5735_ = lean_nat_dec_lt(v_start_5725_, v_n_5722_);
if (v___x_5735_ == 0)
{
lean_object* v___x_5736_; 
lean_dec(v_toBind_5731_);
lean_dec(v_start_5725_);
lean_dec_ref(v_ngen_5723_);
lean_dec(v_n_5722_);
lean_dec_ref(v_act_5720_);
lean_dec_ref(v_env_5719_);
lean_dec_ref(v_cctx_5718_);
lean_dec(v_inst_5717_);
v___x_5736_ = lean_apply_2(v_toPure_5732_, lean_box(0), v_tasks_5724_);
return v___x_5736_;
}
else
{
lean_object* v_namePrefix_5737_; lean_object* v_idx_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5753_; 
v_namePrefix_5737_ = lean_ctor_get(v_ngen_5723_, 0);
v_idx_5738_ = lean_ctor_get(v_ngen_5723_, 1);
v_isSharedCheck_5753_ = !lean_is_exclusive(v_ngen_5723_);
if (v_isSharedCheck_5753_ == 0)
{
v___x_5740_ = v_ngen_5723_;
v_isShared_5741_ = v_isSharedCheck_5753_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_idx_5738_);
lean_inc(v_namePrefix_5737_);
lean_dec(v_ngen_5723_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5753_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___f_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5746_; 
v___f_5742_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5742_, 0, v_tasks_5724_);
lean_closure_set(v___f_5742_, 1, v_toPure_5732_);
v___x_5743_ = l_Lean_Name_num___override(v_namePrefix_5737_, v_idx_5738_);
v___x_5744_ = lean_unsigned_to_nat(1u);
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 1, v___x_5744_);
lean_ctor_set(v___x_5740_, 0, v___x_5743_);
v___x_5746_ = v___x_5740_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5743_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v___x_5744_);
v___x_5746_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; 
v___x_5747_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5747_, 0, lean_box(0));
lean_closure_set(v___x_5747_, 1, v_cctx_5718_);
lean_closure_set(v___x_5747_, 2, v___x_5746_);
lean_closure_set(v___x_5747_, 3, v_env_5719_);
lean_closure_set(v___x_5747_, 4, v_act_5720_);
lean_closure_set(v___x_5747_, 5, v_start_5725_);
lean_closure_set(v___x_5747_, 6, v_n_5722_);
v___x_5748_ = lean_unsigned_to_nat(0u);
v___x_5749_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5749_, 0, lean_box(0));
lean_closure_set(v___x_5749_, 1, v___x_5747_);
lean_closure_set(v___x_5749_, 2, v___x_5748_);
v___x_5750_ = lean_apply_2(v_inst_5717_, lean_box(0), v___x_5749_);
v___x_5751_ = lean_apply_4(v_toBind_5731_, lean_box(0), lean_box(0), v___x_5750_, v___f_5742_);
return v___x_5751_;
}
}
}
}
else
{
lean_object* v_mdata_5754_; lean_object* v_constants_5755_; lean_object* v___x_5756_; lean_object* v_cnt_5757_; uint8_t v___x_5758_; 
v_mdata_5754_ = lean_array_fget(v_moduleData_5730_, v_idx_5727_);
lean_dec_ref(v_moduleData_5730_);
v_constants_5755_ = lean_ctor_get(v_mdata_5754_, 2);
lean_inc_ref(v_constants_5755_);
lean_dec(v_mdata_5754_);
v___x_5756_ = lean_array_get_size(v_constants_5755_);
lean_dec_ref(v_constants_5755_);
v_cnt_5757_ = lean_nat_add(v_cnt_5726_, v___x_5756_);
lean_dec(v_cnt_5726_);
v___x_5758_ = lean_nat_dec_lt(v_constantsPerTask_5721_, v_cnt_5757_);
if (v___x_5758_ == 0)
{
lean_object* v___x_5759_; lean_object* v___x_5760_; 
v___x_5759_ = lean_unsigned_to_nat(1u);
v___x_5760_ = lean_nat_add(v_idx_5727_, v___x_5759_);
lean_dec(v_idx_5727_);
v_cnt_5726_ = v_cnt_5757_;
v_idx_5727_ = v___x_5760_;
goto _start;
}
else
{
lean_object* v_namePrefix_5762_; lean_object* v_idx_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5781_; 
lean_inc(v_toBind_5731_);
lean_dec(v_cnt_5757_);
v_namePrefix_5762_ = lean_ctor_get(v_ngen_5723_, 0);
v_idx_5763_ = lean_ctor_get(v_ngen_5723_, 1);
v_isSharedCheck_5781_ = !lean_is_exclusive(v_ngen_5723_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5765_ = v_ngen_5723_;
v_isShared_5766_ = v_isSharedCheck_5781_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_idx_5763_);
lean_inc(v_namePrefix_5762_);
lean_dec(v_ngen_5723_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5781_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5770_; 
lean_inc(v_idx_5763_);
lean_inc(v_namePrefix_5762_);
v___x_5767_ = l_Lean_Name_num___override(v_namePrefix_5762_, v_idx_5763_);
v___x_5768_ = lean_unsigned_to_nat(1u);
if (v_isShared_5766_ == 0)
{
lean_ctor_set(v___x_5765_, 1, v___x_5768_);
lean_ctor_set(v___x_5765_, 0, v___x_5767_);
v___x_5770_ = v___x_5765_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5767_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5768_);
v___x_5770_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___f_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; 
v___x_5771_ = lean_nat_add(v_idx_5763_, v___x_5768_);
lean_dec(v_idx_5763_);
v___x_5772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5772_, 0, v_namePrefix_5762_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = lean_nat_add(v_idx_5727_, v___x_5768_);
lean_dec(v_idx_5727_);
lean_inc(v___x_5773_);
lean_inc_ref(v_act_5720_);
lean_inc_ref(v_env_5719_);
lean_inc_ref(v_cctx_5718_);
lean_inc(v_inst_5717_);
v___f_5774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5774_, 0, v_tasks_5724_);
lean_closure_set(v___f_5774_, 1, v_inst_5716_);
lean_closure_set(v___f_5774_, 2, v_inst_5717_);
lean_closure_set(v___f_5774_, 3, v_cctx_5718_);
lean_closure_set(v___f_5774_, 4, v_env_5719_);
lean_closure_set(v___f_5774_, 5, v_act_5720_);
lean_closure_set(v___f_5774_, 6, v_constantsPerTask_5721_);
lean_closure_set(v___f_5774_, 7, v_n_5722_);
lean_closure_set(v___f_5774_, 8, v___x_5772_);
lean_closure_set(v___f_5774_, 9, v___x_5773_);
v___x_5775_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5775_, 0, lean_box(0));
lean_closure_set(v___x_5775_, 1, v_cctx_5718_);
lean_closure_set(v___x_5775_, 2, v___x_5770_);
lean_closure_set(v___x_5775_, 3, v_env_5719_);
lean_closure_set(v___x_5775_, 4, v_act_5720_);
lean_closure_set(v___x_5775_, 5, v_start_5725_);
lean_closure_set(v___x_5775_, 6, v___x_5773_);
v___x_5776_ = lean_unsigned_to_nat(0u);
v___x_5777_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5777_, 0, lean_box(0));
lean_closure_set(v___x_5777_, 1, v___x_5775_);
lean_closure_set(v___x_5777_, 2, v___x_5776_);
v___x_5778_ = lean_apply_2(v_inst_5717_, lean_box(0), v___x_5777_);
v___x_5779_ = lean_apply_4(v_toBind_5731_, lean_box(0), lean_box(0), v___x_5778_, v___f_5774_);
return v___x_5779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5782_, lean_object* v_inst_5783_, lean_object* v_inst_5784_, lean_object* v_cctx_5785_, lean_object* v_env_5786_, lean_object* v_act_5787_, lean_object* v_constantsPerTask_5788_, lean_object* v_n_5789_, lean_object* v___x_5790_, lean_object* v___x_5791_, lean_object* v_t_5792_){
_start:
{
lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5793_ = lean_array_push(v_tasks_5782_, v_t_5792_);
v___x_5794_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5791_);
v___x_5795_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5783_, v_inst_5784_, v_cctx_5785_, v_env_5786_, v_act_5787_, v_constantsPerTask_5788_, v_n_5789_, v___x_5790_, v___x_5793_, v___x_5791_, v___x_5794_, v___x_5791_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5796_, lean_object* v_00_u03b1_5797_, lean_object* v_inst_5798_, lean_object* v_inst_5799_, lean_object* v_cctx_5800_, lean_object* v_env_5801_, lean_object* v_act_5802_, lean_object* v_constantsPerTask_5803_, lean_object* v_n_5804_, lean_object* v_ngen_5805_, lean_object* v_tasks_5806_, lean_object* v_start_5807_, lean_object* v_cnt_5808_, lean_object* v_idx_5809_){
_start:
{
lean_object* v___x_5810_; 
v___x_5810_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5798_, v_inst_5799_, v_cctx_5800_, v_env_5801_, v_act_5802_, v_constantsPerTask_5803_, v_n_5804_, v_ngen_5805_, v_tasks_5806_, v_start_5807_, v_cnt_5808_, v_idx_5809_);
return v___x_5810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5811_, lean_object* v_h__1_5812_){
_start:
{
lean_object* v_fst_5813_; lean_object* v_snd_5814_; lean_object* v___x_5815_; 
v_fst_5813_ = lean_ctor_get(v_x_5811_, 0);
lean_inc(v_fst_5813_);
v_snd_5814_ = lean_ctor_get(v_x_5811_, 1);
lean_inc(v_snd_5814_);
lean_dec_ref(v_x_5811_);
v___x_5815_ = lean_apply_2(v_h__1_5812_, v_fst_5813_, v_snd_5814_);
return v___x_5815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5816_, lean_object* v_x_5817_, lean_object* v_h__1_5818_){
_start:
{
lean_object* v_fst_5819_; lean_object* v_snd_5820_; lean_object* v___x_5821_; 
v_fst_5819_ = lean_ctor_get(v_x_5817_, 0);
lean_inc(v_fst_5819_);
v_snd_5820_ = lean_ctor_get(v_x_5817_, 1);
lean_inc(v_snd_5820_);
lean_dec_ref(v_x_5817_);
v___x_5821_ = lean_apply_2(v_h__1_5818_, v_fst_5819_, v_snd_5820_);
return v___x_5821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5822_, lean_object* v_inst_5823_, lean_object* v_inst_5824_, lean_object* v_inst_5825_, lean_object* v_x_5826_, lean_object* v___y_5827_){
_start:
{
lean_object* v___x_5828_; 
v___x_5828_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5822_, v_inst_5823_, v_inst_5824_, v_inst_5825_, v___y_5827_);
return v___x_5828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5829_, lean_object* v_toPure_5830_, lean_object* v_____r_5831_){
_start:
{
lean_object* v_tree_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; 
v_tree_5832_ = lean_ctor_get(v_r_5829_, 0);
lean_inc_ref(v_tree_5832_);
lean_dec_ref(v_r_5829_);
v___x_5833_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5832_);
v___x_5834_ = lean_apply_2(v_toPure_5830_, lean_box(0), v___x_5833_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5835_, lean_object* v___x_5836_, lean_object* v_toPure_5837_, lean_object* v_toBind_5838_, lean_object* v_inst_5839_, lean_object* v___f_5840_, lean_object* v_tasks_5841_){
_start:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v_r_5847_; lean_object* v_errors_5848_; lean_object* v___f_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; uint8_t v___x_5852_; 
v___x_5842_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5835_);
v___x_5843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5843_, 0, v___x_5835_);
lean_ctor_set(v___x_5843_, 1, v___x_5842_);
v___x_5844_ = lean_mk_empty_array_with_capacity(v___x_5835_);
lean_inc_ref(v___x_5844_);
v___x_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5843_);
lean_ctor_set(v___x_5845_, 1, v___x_5844_);
v___x_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5846_, 0, v___x_5845_);
lean_ctor_set(v___x_5846_, 1, v___x_5844_);
v_r_5847_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5836_, v___x_5846_, v_tasks_5841_);
v_errors_5848_ = lean_ctor_get(v_r_5847_, 1);
lean_inc_ref(v_errors_5848_);
lean_inc(v_toPure_5837_);
v___f_5849_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5849_, 0, v_r_5847_);
lean_closure_set(v___f_5849_, 1, v_toPure_5837_);
v___x_5850_ = lean_array_get_size(v_errors_5848_);
v___x_5851_ = lean_box(0);
v___x_5852_ = lean_nat_dec_lt(v___x_5835_, v___x_5850_);
lean_dec(v___x_5835_);
if (v___x_5852_ == 0)
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
lean_dec_ref(v_errors_5848_);
lean_dec(v___f_5840_);
lean_dec_ref(v_inst_5839_);
v___x_5853_ = lean_apply_2(v_toPure_5837_, lean_box(0), v___x_5851_);
v___x_5854_ = lean_apply_4(v_toBind_5838_, lean_box(0), lean_box(0), v___x_5853_, v___f_5849_);
return v___x_5854_;
}
else
{
uint8_t v___x_5855_; 
v___x_5855_ = lean_nat_dec_le(v___x_5850_, v___x_5850_);
if (v___x_5855_ == 0)
{
if (v___x_5852_ == 0)
{
lean_object* v___x_5856_; lean_object* v___x_5857_; 
lean_dec_ref(v_errors_5848_);
lean_dec(v___f_5840_);
lean_dec_ref(v_inst_5839_);
v___x_5856_ = lean_apply_2(v_toPure_5837_, lean_box(0), v___x_5851_);
v___x_5857_ = lean_apply_4(v_toBind_5838_, lean_box(0), lean_box(0), v___x_5856_, v___f_5849_);
return v___x_5857_;
}
else
{
size_t v___x_5858_; size_t v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; 
lean_dec(v_toPure_5837_);
v___x_5858_ = ((size_t)0ULL);
v___x_5859_ = lean_usize_of_nat(v___x_5850_);
v___x_5860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5839_, v___f_5840_, v_errors_5848_, v___x_5858_, v___x_5859_, v___x_5851_);
v___x_5861_ = lean_apply_4(v_toBind_5838_, lean_box(0), lean_box(0), v___x_5860_, v___f_5849_);
return v___x_5861_;
}
}
else
{
size_t v___x_5862_; size_t v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
lean_dec(v_toPure_5837_);
v___x_5862_ = ((size_t)0ULL);
v___x_5863_ = lean_usize_of_nat(v___x_5850_);
v___x_5864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5839_, v___f_5840_, v_errors_5848_, v___x_5862_, v___x_5863_, v___x_5851_);
v___x_5865_ = lean_apply_4(v_toBind_5838_, lean_box(0), lean_box(0), v___x_5864_, v___f_5849_);
return v___x_5865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5868_, lean_object* v_inst_5869_, lean_object* v_inst_5870_, lean_object* v_inst_5871_, lean_object* v_inst_5872_, lean_object* v_cctx_5873_, lean_object* v_ngen_5874_, lean_object* v_env_5875_, lean_object* v_act_5876_, lean_object* v_constantsPerTask_5877_){
_start:
{
lean_object* v___x_5878_; lean_object* v_moduleData_5879_; lean_object* v_toApplicative_5880_; lean_object* v_toBind_5881_; lean_object* v_n_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v_toPure_5886_; lean_object* v___f_5887_; lean_object* v___x_5888_; lean_object* v___f_5889_; lean_object* v___x_5890_; 
v___x_5878_ = l_Lean_Environment_header(v_env_5875_);
v_moduleData_5879_ = lean_ctor_get(v___x_5878_, 6);
lean_inc_ref(v_moduleData_5879_);
lean_dec_ref(v___x_5878_);
v_toApplicative_5880_ = lean_ctor_get(v_inst_5868_, 0);
v_toBind_5881_ = lean_ctor_get(v_inst_5868_, 1);
lean_inc_n(v_toBind_5881_, 2);
v_n_5882_ = lean_array_get_size(v_moduleData_5879_);
lean_dec_ref(v_moduleData_5879_);
v___x_5883_ = lean_unsigned_to_nat(0u);
v___x_5884_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5868_, 2);
v___x_5885_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5868_, v_inst_5872_, v_cctx_5873_, v_env_5875_, v_act_5876_, v_constantsPerTask_5877_, v_n_5882_, v_ngen_5874_, v___x_5884_, v___x_5883_, v___x_5883_, v___x_5883_);
v_toPure_5886_ = lean_ctor_get(v_toApplicative_5880_, 1);
lean_inc(v_toPure_5886_);
v___f_5887_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5887_, 0, v_inst_5868_);
lean_closure_set(v___f_5887_, 1, v_inst_5869_);
lean_closure_set(v___f_5887_, 2, v_inst_5870_);
lean_closure_set(v___f_5887_, 3, v_inst_5871_);
v___x_5888_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_5889_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5889_, 0, v___x_5883_);
lean_closure_set(v___f_5889_, 1, v___x_5888_);
lean_closure_set(v___f_5889_, 2, v_toPure_5886_);
lean_closure_set(v___f_5889_, 3, v_toBind_5881_);
lean_closure_set(v___f_5889_, 4, v_inst_5868_);
lean_closure_set(v___f_5889_, 5, v___f_5887_);
v___x_5890_ = lean_apply_4(v_toBind_5881_, lean_box(0), lean_box(0), v___x_5885_, v___f_5889_);
return v___x_5890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5891_, lean_object* v_00_u03b1_5892_, lean_object* v_inst_5893_, lean_object* v_inst_5894_, lean_object* v_inst_5895_, lean_object* v_inst_5896_, lean_object* v_inst_5897_, lean_object* v_cctx_5898_, lean_object* v_ngen_5899_, lean_object* v_env_5900_, lean_object* v_act_5901_, lean_object* v_constantsPerTask_5902_){
_start:
{
lean_object* v___x_5903_; 
v___x_5903_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5893_, v_inst_5894_, v_inst_5895_, v_inst_5896_, v_inst_5897_, v_cctx_5898_, v_ngen_5899_, v_env_5900_, v_act_5901_, v_constantsPerTask_5902_);
return v___x_5903_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5904_ = lean_box(0);
v___x_5905_ = lean_unsigned_to_nat(16u);
v___x_5906_ = lean_mk_array(v___x_5905_, v___x_5904_);
return v___x_5906_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5907_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5908_ = lean_unsigned_to_nat(0u);
v___x_5909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5908_);
lean_ctor_set(v___x_5909_, 1, v___x_5907_);
return v___x_5909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5910_){
_start:
{
lean_object* v_toCold_5911_; lean_object* v_ref_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_5946_; 
v_toCold_5911_ = lean_ctor_get(v_ctx_5910_, 0);
v_ref_5912_ = lean_ctor_get(v_ctx_5910_, 2);
v_isSharedCheck_5946_ = !lean_is_exclusive(v_ctx_5910_);
if (v_isSharedCheck_5946_ == 0)
{
lean_object* v_unused_5947_; 
v_unused_5947_ = lean_ctor_get(v_ctx_5910_, 1);
lean_dec(v_unused_5947_);
v___x_5914_ = v_ctx_5910_;
v_isShared_5915_ = v_isSharedCheck_5946_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_ref_5912_);
lean_inc(v_toCold_5911_);
lean_dec(v_ctx_5910_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_5946_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
lean_object* v_fileName_5916_; lean_object* v_fileMap_5917_; lean_object* v_options_5918_; lean_object* v_maxRecDepth_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5937_; 
v_fileName_5916_ = lean_ctor_get(v_toCold_5911_, 0);
v_fileMap_5917_ = lean_ctor_get(v_toCold_5911_, 1);
v_options_5918_ = lean_ctor_get(v_toCold_5911_, 2);
v_maxRecDepth_5919_ = lean_ctor_get(v_toCold_5911_, 3);
v_isSharedCheck_5937_ = !lean_is_exclusive(v_toCold_5911_);
if (v_isSharedCheck_5937_ == 0)
{
lean_object* v_unused_5938_; lean_object* v_unused_5939_; lean_object* v_unused_5940_; lean_object* v_unused_5941_; lean_object* v_unused_5942_; lean_object* v_unused_5943_; lean_object* v_unused_5944_; lean_object* v_unused_5945_; 
v_unused_5938_ = lean_ctor_get(v_toCold_5911_, 11);
lean_dec(v_unused_5938_);
v_unused_5939_ = lean_ctor_get(v_toCold_5911_, 10);
lean_dec(v_unused_5939_);
v_unused_5940_ = lean_ctor_get(v_toCold_5911_, 9);
lean_dec(v_unused_5940_);
v_unused_5941_ = lean_ctor_get(v_toCold_5911_, 8);
lean_dec(v_unused_5941_);
v_unused_5942_ = lean_ctor_get(v_toCold_5911_, 7);
lean_dec(v_unused_5942_);
v_unused_5943_ = lean_ctor_get(v_toCold_5911_, 6);
lean_dec(v_unused_5943_);
v_unused_5944_ = lean_ctor_get(v_toCold_5911_, 5);
lean_dec(v_unused_5944_);
v_unused_5945_ = lean_ctor_get(v_toCold_5911_, 4);
lean_dec(v_unused_5945_);
v___x_5921_ = v_toCold_5911_;
v_isShared_5922_ = v_isSharedCheck_5937_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_maxRecDepth_5919_);
lean_inc(v_options_5918_);
lean_inc(v_fileMap_5917_);
lean_inc(v_fileName_5916_);
lean_dec(v_toCold_5911_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5937_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5930_; 
v___x_5923_ = lean_box(0);
v___x_5924_ = lean_box(0);
v___x_5925_ = lean_unsigned_to_nat(0u);
v___x_5926_ = l_Lean_firstFrontendMacroScope;
v___x_5927_ = lean_box(0);
v___x_5928_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
lean_inc_ref(v_options_5918_);
if (v_isShared_5922_ == 0)
{
lean_ctor_set(v___x_5921_, 11, v___x_5928_);
lean_ctor_set(v___x_5921_, 10, v___x_5927_);
lean_ctor_set(v___x_5921_, 9, v___x_5926_);
lean_ctor_set(v___x_5921_, 8, v___x_5923_);
lean_ctor_set(v___x_5921_, 7, v___x_5925_);
lean_ctor_set(v___x_5921_, 6, v___x_5925_);
lean_ctor_set(v___x_5921_, 5, v___x_5924_);
lean_ctor_set(v___x_5921_, 4, v___x_5923_);
v___x_5930_ = v___x_5921_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_fileName_5916_);
lean_ctor_set(v_reuseFailAlloc_5936_, 1, v_fileMap_5917_);
lean_ctor_set(v_reuseFailAlloc_5936_, 2, v_options_5918_);
lean_ctor_set(v_reuseFailAlloc_5936_, 3, v_maxRecDepth_5919_);
lean_ctor_set(v_reuseFailAlloc_5936_, 4, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5936_, 5, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5936_, 6, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5936_, 7, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5936_, 8, v___x_5923_);
lean_ctor_set(v_reuseFailAlloc_5936_, 9, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5936_, 10, v___x_5927_);
lean_ctor_set(v_reuseFailAlloc_5936_, 11, v___x_5928_);
v___x_5930_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
uint8_t v___x_5931_; uint8_t v___x_5932_; lean_object* v___x_5934_; 
v___x_5931_ = l_Lean_getDiag(v_options_5918_);
lean_dec_ref(v_options_5918_);
v___x_5932_ = 0;
if (v_isShared_5915_ == 0)
{
lean_ctor_set(v___x_5914_, 1, v___x_5925_);
lean_ctor_set(v___x_5914_, 0, v___x_5930_);
v___x_5934_ = v___x_5914_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v___x_5930_);
lean_ctor_set(v_reuseFailAlloc_5935_, 1, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5935_, 2, v_ref_5912_);
v___x_5934_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*3, v___x_5931_);
lean_ctor_set_uint8(v___x_5934_, sizeof(void*)*3 + 1, v___x_5932_);
return v___x_5934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5948_, lean_object* v_opts_5949_, lean_object* v_act_5950_, lean_object* v_decl_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_){
_start:
{
lean_object* v___x_5957_; lean_object* v___x_5958_; 
lean_inc(v___y_5955_);
lean_inc_ref(v___y_5954_);
lean_inc(v___y_5953_);
lean_inc_ref(v___y_5952_);
v___x_5957_ = lean_apply_4(v_act_5950_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_);
v___x_5958_ = l_Lean_profileitIOUnsafe___redArg(v_category_5948_, v_opts_5949_, v___x_5957_, v_decl_5951_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5959_, lean_object* v_opts_5960_, lean_object* v_act_5961_, lean_object* v_decl_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_){
_start:
{
lean_object* v_res_5968_; 
v_res_5968_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5959_, v_opts_5960_, v_act_5961_, v_decl_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
lean_dec(v___y_5966_);
lean_dec_ref(v___y_5965_);
lean_dec(v___y_5964_);
lean_dec_ref(v___y_5963_);
lean_dec_ref(v_opts_5960_);
lean_dec_ref(v_category_5959_);
return v_res_5968_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_5969_, lean_object* v_category_5970_, lean_object* v_opts_5971_, lean_object* v_act_5972_, lean_object* v_decl_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_){
_start:
{
lean_object* v___x_5979_; 
v___x_5979_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5970_, v_opts_5971_, v_act_5972_, v_decl_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_);
return v___x_5979_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_5980_, lean_object* v_category_5981_, lean_object* v_opts_5982_, lean_object* v_act_5983_, lean_object* v_decl_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_){
_start:
{
lean_object* v_res_5990_; 
v_res_5990_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_5980_, v_category_5981_, v_opts_5982_, v_act_5983_, v_decl_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_);
lean_dec(v___y_5988_);
lean_dec_ref(v___y_5987_);
lean_dec(v___y_5986_);
lean_dec_ref(v___y_5985_);
lean_dec_ref(v_opts_5982_);
lean_dec_ref(v_category_5981_);
return v_res_5990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_5991_, lean_object* v_env_5992_, lean_object* v_act_5993_, lean_object* v_constantsPerTask_5994_, lean_object* v_n_5995_, lean_object* v_ngen_5996_, lean_object* v_tasks_5997_, lean_object* v_start_5998_, lean_object* v_cnt_5999_, lean_object* v_idx_6000_){
_start:
{
lean_object* v___x_6002_; lean_object* v_moduleData_6003_; lean_object* v___x_6004_; uint8_t v___x_6005_; 
v___x_6002_ = l_Lean_Environment_header(v_env_5992_);
v_moduleData_6003_ = lean_ctor_get(v___x_6002_, 6);
lean_inc_ref(v_moduleData_6003_);
lean_dec_ref(v___x_6002_);
v___x_6004_ = lean_array_get_size(v_moduleData_6003_);
v___x_6005_ = lean_nat_dec_lt(v_idx_6000_, v___x_6004_);
if (v___x_6005_ == 0)
{
uint8_t v___x_6006_; 
lean_dec_ref(v_moduleData_6003_);
lean_dec(v_idx_6000_);
lean_dec(v_cnt_5999_);
v___x_6006_ = lean_nat_dec_lt(v_start_5998_, v_n_5995_);
if (v___x_6006_ == 0)
{
lean_object* v___x_6007_; 
lean_dec(v_start_5998_);
lean_dec_ref(v_ngen_5996_);
lean_dec(v_n_5995_);
lean_dec_ref(v_act_5993_);
lean_dec_ref(v_env_5992_);
lean_dec_ref(v_cctx_5991_);
v___x_6007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6007_, 0, v_tasks_5997_);
return v___x_6007_;
}
else
{
lean_object* v_namePrefix_6008_; lean_object* v_idx_6009_; lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6023_; 
v_namePrefix_6008_ = lean_ctor_get(v_ngen_5996_, 0);
v_idx_6009_ = lean_ctor_get(v_ngen_5996_, 1);
v_isSharedCheck_6023_ = !lean_is_exclusive(v_ngen_5996_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_6011_ = v_ngen_5996_;
v_isShared_6012_ = v_isSharedCheck_6023_;
goto v_resetjp_6010_;
}
else
{
lean_inc(v_idx_6009_);
lean_inc(v_namePrefix_6008_);
lean_dec(v_ngen_5996_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6023_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6016_; 
v___x_6013_ = l_Lean_Name_num___override(v_namePrefix_6008_, v_idx_6009_);
v___x_6014_ = lean_unsigned_to_nat(1u);
if (v_isShared_6012_ == 0)
{
lean_ctor_set(v___x_6011_, 1, v___x_6014_);
lean_ctor_set(v___x_6011_, 0, v___x_6013_);
v___x_6016_ = v___x_6011_;
goto v_reusejp_6015_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6013_);
lean_ctor_set(v_reuseFailAlloc_6022_, 1, v___x_6014_);
v___x_6016_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6015_;
}
v_reusejp_6015_:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v___x_6017_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6017_, 0, lean_box(0));
lean_closure_set(v___x_6017_, 1, v_cctx_5991_);
lean_closure_set(v___x_6017_, 2, v___x_6016_);
lean_closure_set(v___x_6017_, 3, v_env_5992_);
lean_closure_set(v___x_6017_, 4, v_act_5993_);
lean_closure_set(v___x_6017_, 5, v_start_5998_);
lean_closure_set(v___x_6017_, 6, v_n_5995_);
v___x_6018_ = lean_unsigned_to_nat(0u);
v___x_6019_ = lean_io_as_task(v___x_6017_, v___x_6018_);
v___x_6020_ = lean_array_push(v_tasks_5997_, v___x_6019_);
v___x_6021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6020_);
return v___x_6021_;
}
}
}
}
else
{
lean_object* v_mdata_6024_; lean_object* v_constants_6025_; lean_object* v___x_6026_; lean_object* v_cnt_6027_; uint8_t v___x_6028_; 
v_mdata_6024_ = lean_array_fget(v_moduleData_6003_, v_idx_6000_);
lean_dec_ref(v_moduleData_6003_);
v_constants_6025_ = lean_ctor_get(v_mdata_6024_, 2);
lean_inc_ref(v_constants_6025_);
lean_dec(v_mdata_6024_);
v___x_6026_ = lean_array_get_size(v_constants_6025_);
lean_dec_ref(v_constants_6025_);
v_cnt_6027_ = lean_nat_add(v_cnt_5999_, v___x_6026_);
lean_dec(v_cnt_5999_);
v___x_6028_ = lean_nat_dec_lt(v_constantsPerTask_5994_, v_cnt_6027_);
if (v___x_6028_ == 0)
{
lean_object* v___x_6029_; lean_object* v___x_6030_; 
v___x_6029_ = lean_unsigned_to_nat(1u);
v___x_6030_ = lean_nat_add(v_idx_6000_, v___x_6029_);
lean_dec(v_idx_6000_);
v_cnt_5999_ = v_cnt_6027_;
v_idx_6000_ = v___x_6030_;
goto _start;
}
else
{
lean_object* v_namePrefix_6032_; lean_object* v_idx_6033_; lean_object* v___x_6035_; uint8_t v_isShared_6036_; uint8_t v_isSharedCheck_6050_; 
lean_dec(v_cnt_6027_);
v_namePrefix_6032_ = lean_ctor_get(v_ngen_5996_, 0);
v_idx_6033_ = lean_ctor_get(v_ngen_5996_, 1);
v_isSharedCheck_6050_ = !lean_is_exclusive(v_ngen_5996_);
if (v_isSharedCheck_6050_ == 0)
{
v___x_6035_ = v_ngen_5996_;
v_isShared_6036_ = v_isSharedCheck_6050_;
goto v_resetjp_6034_;
}
else
{
lean_inc(v_idx_6033_);
lean_inc(v_namePrefix_6032_);
lean_dec(v_ngen_5996_);
v___x_6035_ = lean_box(0);
v_isShared_6036_ = v_isSharedCheck_6050_;
goto v_resetjp_6034_;
}
v_resetjp_6034_:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6040_; 
lean_inc(v_idx_6033_);
lean_inc(v_namePrefix_6032_);
v___x_6037_ = l_Lean_Name_num___override(v_namePrefix_6032_, v_idx_6033_);
v___x_6038_ = lean_unsigned_to_nat(1u);
if (v_isShared_6036_ == 0)
{
lean_ctor_set(v___x_6035_, 1, v___x_6038_);
lean_ctor_set(v___x_6035_, 0, v___x_6037_);
v___x_6040_ = v___x_6035_;
goto v_reusejp_6039_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v___x_6037_);
lean_ctor_set(v_reuseFailAlloc_6049_, 1, v___x_6038_);
v___x_6040_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6039_;
}
v_reusejp_6039_:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v___x_6041_ = lean_nat_add(v_idx_6000_, v___x_6038_);
lean_dec(v_idx_6000_);
lean_inc_n(v___x_6041_, 2);
lean_inc_ref(v_act_5993_);
lean_inc_ref(v_env_5992_);
lean_inc_ref(v_cctx_5991_);
v___x_6042_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6042_, 0, lean_box(0));
lean_closure_set(v___x_6042_, 1, v_cctx_5991_);
lean_closure_set(v___x_6042_, 2, v___x_6040_);
lean_closure_set(v___x_6042_, 3, v_env_5992_);
lean_closure_set(v___x_6042_, 4, v_act_5993_);
lean_closure_set(v___x_6042_, 5, v_start_5998_);
lean_closure_set(v___x_6042_, 6, v___x_6041_);
v___x_6043_ = lean_unsigned_to_nat(0u);
v___x_6044_ = lean_io_as_task(v___x_6042_, v___x_6043_);
v___x_6045_ = lean_nat_add(v_idx_6033_, v___x_6038_);
lean_dec(v_idx_6033_);
v___x_6046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6046_, 0, v_namePrefix_6032_);
lean_ctor_set(v___x_6046_, 1, v___x_6045_);
v___x_6047_ = lean_array_push(v_tasks_5997_, v___x_6044_);
v_ngen_5996_ = v___x_6046_;
v_tasks_5997_ = v___x_6047_;
v_start_5998_ = v___x_6041_;
v_cnt_5999_ = v___x_6043_;
v_idx_6000_ = v___x_6041_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6051_, lean_object* v_env_6052_, lean_object* v_act_6053_, lean_object* v_constantsPerTask_6054_, lean_object* v_n_6055_, lean_object* v_ngen_6056_, lean_object* v_tasks_6057_, lean_object* v_start_6058_, lean_object* v_cnt_6059_, lean_object* v_idx_6060_, lean_object* v___y_6061_){
_start:
{
lean_object* v_res_6062_; 
v_res_6062_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6051_, v_env_6052_, v_act_6053_, v_constantsPerTask_6054_, v_n_6055_, v_ngen_6056_, v_tasks_6057_, v_start_6058_, v_cnt_6059_, v_idx_6060_);
lean_dec(v_constantsPerTask_6054_);
return v_res_6062_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6071_, uint8_t v___y_6072_, lean_object* v_x_6073_){
_start:
{
if (lean_obj_tag(v_x_6073_) == 1)
{
lean_object* v_pre_6074_; 
v_pre_6074_ = lean_ctor_get(v_x_6073_, 0);
switch(lean_obj_tag(v_pre_6074_))
{
case 1:
{
lean_object* v_pre_6075_; 
v_pre_6075_ = lean_ctor_get(v_pre_6074_, 0);
switch(lean_obj_tag(v_pre_6075_))
{
case 0:
{
lean_object* v_str_6076_; lean_object* v_str_6077_; lean_object* v___x_6078_; uint8_t v___x_6079_; 
v_str_6076_ = lean_ctor_get(v_x_6073_, 1);
v_str_6077_ = lean_ctor_get(v_pre_6074_, 1);
v___x_6078_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6079_ = lean_string_dec_eq(v_str_6077_, v___x_6078_);
if (v___x_6079_ == 0)
{
lean_object* v___x_6080_; uint8_t v___x_6081_; 
v___x_6080_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6081_ = lean_string_dec_eq(v_str_6077_, v___x_6080_);
if (v___x_6081_ == 0)
{
return v___x_6081_;
}
else
{
lean_object* v___x_6082_; uint8_t v___x_6083_; 
v___x_6082_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6083_ = lean_string_dec_eq(v_str_6076_, v___x_6082_);
if (v___x_6083_ == 0)
{
return v___x_6083_;
}
else
{
return v_suppressElabErrors_6071_;
}
}
}
else
{
lean_object* v___x_6084_; uint8_t v___x_6085_; 
v___x_6084_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6085_ = lean_string_dec_eq(v_str_6076_, v___x_6084_);
if (v___x_6085_ == 0)
{
return v___x_6085_;
}
else
{
return v_suppressElabErrors_6071_;
}
}
}
case 1:
{
lean_object* v_pre_6086_; 
v_pre_6086_ = lean_ctor_get(v_pre_6075_, 0);
if (lean_obj_tag(v_pre_6086_) == 0)
{
lean_object* v_str_6087_; lean_object* v_str_6088_; lean_object* v_str_6089_; lean_object* v___x_6090_; uint8_t v___x_6091_; 
v_str_6087_ = lean_ctor_get(v_x_6073_, 1);
v_str_6088_ = lean_ctor_get(v_pre_6074_, 1);
v_str_6089_ = lean_ctor_get(v_pre_6075_, 1);
v___x_6090_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6091_ = lean_string_dec_eq(v_str_6089_, v___x_6090_);
if (v___x_6091_ == 0)
{
return v___x_6091_;
}
else
{
lean_object* v___x_6092_; uint8_t v___x_6093_; 
v___x_6092_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6093_ = lean_string_dec_eq(v_str_6088_, v___x_6092_);
if (v___x_6093_ == 0)
{
return v___x_6093_;
}
else
{
lean_object* v___x_6094_; uint8_t v___x_6095_; 
v___x_6094_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6095_ = lean_string_dec_eq(v_str_6087_, v___x_6094_);
if (v___x_6095_ == 0)
{
return v___x_6095_;
}
else
{
return v_suppressElabErrors_6071_;
}
}
}
}
else
{
return v___y_6072_;
}
}
default: 
{
return v___y_6072_;
}
}
}
case 0:
{
lean_object* v_str_6096_; lean_object* v___x_6097_; uint8_t v___x_6098_; 
v_str_6096_ = lean_ctor_get(v_x_6073_, 1);
v___x_6097_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6098_ = lean_string_dec_eq(v_str_6096_, v___x_6097_);
if (v___x_6098_ == 0)
{
return v___x_6098_;
}
else
{
return v_suppressElabErrors_6071_;
}
}
default: 
{
return v___y_6072_;
}
}
}
else
{
return v___y_6072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6099_, lean_object* v___y_6100_, lean_object* v_x_6101_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6102_; uint8_t v___y_8081__boxed_6103_; uint8_t v_res_6104_; lean_object* v_r_6105_; 
v_suppressElabErrors_boxed_6102_ = lean_unbox(v_suppressElabErrors_6099_);
v___y_8081__boxed_6103_ = lean_unbox(v___y_6100_);
v_res_6104_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6102_, v___y_8081__boxed_6103_, v_x_6101_);
lean_dec(v_x_6101_);
v_r_6105_ = lean_box(v_res_6104_);
return v_r_6105_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6107_, lean_object* v_msgData_6108_, uint8_t v_severity_6109_, uint8_t v_isSilent_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_){
_start:
{
lean_object* v___y_6117_; lean_object* v___y_6118_; lean_object* v___y_6119_; lean_object* v___y_6120_; uint8_t v___y_6121_; uint8_t v___y_6122_; lean_object* v___y_6123_; lean_object* v___y_6124_; lean_object* v___y_6125_; lean_object* v___y_6154_; uint8_t v___y_6155_; lean_object* v___y_6156_; uint8_t v___y_6157_; uint8_t v___y_6158_; lean_object* v___y_6159_; lean_object* v___y_6160_; lean_object* v___y_6161_; lean_object* v___y_6179_; lean_object* v___y_6180_; lean_object* v___y_6181_; uint8_t v___y_6182_; lean_object* v___y_6183_; uint8_t v___y_6184_; uint8_t v___y_6185_; lean_object* v___y_6186_; lean_object* v___y_6190_; lean_object* v___y_6191_; uint8_t v___y_6192_; lean_object* v___y_6193_; uint8_t v___y_6194_; lean_object* v___y_6195_; uint8_t v___y_6196_; uint8_t v___x_6201_; lean_object* v___y_6203_; lean_object* v___y_6204_; lean_object* v___y_6205_; lean_object* v___y_6206_; uint8_t v___y_6207_; uint8_t v___y_6208_; uint8_t v___y_6209_; uint8_t v___y_6211_; uint8_t v___x_6227_; 
v___x_6201_ = 2;
v___x_6227_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6109_, v___x_6201_);
if (v___x_6227_ == 0)
{
v___y_6211_ = v___x_6227_;
goto v___jp_6210_;
}
else
{
uint8_t v___x_6228_; 
lean_inc_ref(v_msgData_6108_);
v___x_6228_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6108_);
v___y_6211_ = v___x_6228_;
goto v___jp_6210_;
}
v___jp_6116_:
{
lean_object* v___x_6126_; lean_object* v_toCold_6127_; lean_object* v_currNamespace_6128_; lean_object* v_openDecls_6129_; lean_object* v_env_6130_; lean_object* v_nextMacroScope_6131_; lean_object* v_ngen_6132_; lean_object* v_auxDeclNGen_6133_; lean_object* v_traceState_6134_; lean_object* v_cache_6135_; lean_object* v_messages_6136_; lean_object* v_infoState_6137_; lean_object* v_snapshotTasks_6138_; lean_object* v___x_6140_; uint8_t v_isShared_6141_; uint8_t v_isSharedCheck_6152_; 
v___x_6126_ = lean_st_ref_take(v___y_6125_);
v_toCold_6127_ = lean_ctor_get(v___y_6124_, 0);
v_currNamespace_6128_ = lean_ctor_get(v_toCold_6127_, 4);
v_openDecls_6129_ = lean_ctor_get(v_toCold_6127_, 5);
v_env_6130_ = lean_ctor_get(v___x_6126_, 0);
v_nextMacroScope_6131_ = lean_ctor_get(v___x_6126_, 1);
v_ngen_6132_ = lean_ctor_get(v___x_6126_, 2);
v_auxDeclNGen_6133_ = lean_ctor_get(v___x_6126_, 3);
v_traceState_6134_ = lean_ctor_get(v___x_6126_, 4);
v_cache_6135_ = lean_ctor_get(v___x_6126_, 5);
v_messages_6136_ = lean_ctor_get(v___x_6126_, 6);
v_infoState_6137_ = lean_ctor_get(v___x_6126_, 7);
v_snapshotTasks_6138_ = lean_ctor_get(v___x_6126_, 8);
v_isSharedCheck_6152_ = !lean_is_exclusive(v___x_6126_);
if (v_isSharedCheck_6152_ == 0)
{
v___x_6140_ = v___x_6126_;
v_isShared_6141_ = v_isSharedCheck_6152_;
goto v_resetjp_6139_;
}
else
{
lean_inc(v_snapshotTasks_6138_);
lean_inc(v_infoState_6137_);
lean_inc(v_messages_6136_);
lean_inc(v_cache_6135_);
lean_inc(v_traceState_6134_);
lean_inc(v_auxDeclNGen_6133_);
lean_inc(v_ngen_6132_);
lean_inc(v_nextMacroScope_6131_);
lean_inc(v_env_6130_);
lean_dec(v___x_6126_);
v___x_6140_ = lean_box(0);
v_isShared_6141_ = v_isSharedCheck_6152_;
goto v_resetjp_6139_;
}
v_resetjp_6139_:
{
lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6147_; 
lean_inc(v_openDecls_6129_);
lean_inc(v_currNamespace_6128_);
v___x_6142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6142_, 0, v_currNamespace_6128_);
lean_ctor_set(v___x_6142_, 1, v_openDecls_6129_);
v___x_6143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set(v___x_6143_, 1, v___y_6118_);
lean_inc_ref(v___y_6123_);
lean_inc_ref(v___y_6119_);
v___x_6144_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6144_, 0, v___y_6119_);
lean_ctor_set(v___x_6144_, 1, v___y_6117_);
lean_ctor_set(v___x_6144_, 2, v___y_6120_);
lean_ctor_set(v___x_6144_, 3, v___y_6123_);
lean_ctor_set(v___x_6144_, 4, v___x_6143_);
lean_ctor_set_uint8(v___x_6144_, sizeof(void*)*5, v___y_6122_);
lean_ctor_set_uint8(v___x_6144_, sizeof(void*)*5 + 1, v___y_6121_);
lean_ctor_set_uint8(v___x_6144_, sizeof(void*)*5 + 2, v_isSilent_6110_);
v___x_6145_ = l_Lean_MessageLog_add(v___x_6144_, v_messages_6136_);
if (v_isShared_6141_ == 0)
{
lean_ctor_set(v___x_6140_, 6, v___x_6145_);
v___x_6147_ = v___x_6140_;
goto v_reusejp_6146_;
}
else
{
lean_object* v_reuseFailAlloc_6151_; 
v_reuseFailAlloc_6151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6151_, 0, v_env_6130_);
lean_ctor_set(v_reuseFailAlloc_6151_, 1, v_nextMacroScope_6131_);
lean_ctor_set(v_reuseFailAlloc_6151_, 2, v_ngen_6132_);
lean_ctor_set(v_reuseFailAlloc_6151_, 3, v_auxDeclNGen_6133_);
lean_ctor_set(v_reuseFailAlloc_6151_, 4, v_traceState_6134_);
lean_ctor_set(v_reuseFailAlloc_6151_, 5, v_cache_6135_);
lean_ctor_set(v_reuseFailAlloc_6151_, 6, v___x_6145_);
lean_ctor_set(v_reuseFailAlloc_6151_, 7, v_infoState_6137_);
lean_ctor_set(v_reuseFailAlloc_6151_, 8, v_snapshotTasks_6138_);
v___x_6147_ = v_reuseFailAlloc_6151_;
goto v_reusejp_6146_;
}
v_reusejp_6146_:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6148_ = lean_st_ref_put(v___y_6125_, v___x_6147_);
v___x_6149_ = lean_box(0);
v___x_6150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6149_);
return v___x_6150_;
}
}
}
v___jp_6153_:
{
lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v_a_6164_; lean_object* v___x_6166_; uint8_t v_isShared_6167_; uint8_t v_isSharedCheck_6177_; 
v___x_6162_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6108_);
v___x_6163_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6162_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
v_a_6164_ = lean_ctor_get(v___x_6163_, 0);
v_isSharedCheck_6177_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6177_ == 0)
{
v___x_6166_ = v___x_6163_;
v_isShared_6167_ = v_isSharedCheck_6177_;
goto v_resetjp_6165_;
}
else
{
lean_inc(v_a_6164_);
lean_dec(v___x_6163_);
v___x_6166_ = lean_box(0);
v_isShared_6167_ = v_isSharedCheck_6177_;
goto v_resetjp_6165_;
}
v_resetjp_6165_:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; 
lean_inc_ref_n(v___y_6159_, 2);
v___x_6168_ = l_Lean_FileMap_toPosition(v___y_6159_, v___y_6160_);
lean_dec(v___y_6160_);
v___x_6169_ = l_Lean_FileMap_toPosition(v___y_6159_, v___y_6161_);
lean_dec(v___y_6161_);
v___x_6170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6169_);
v___x_6171_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6155_ == 0)
{
lean_del_object(v___x_6166_);
lean_dec_ref(v___y_6154_);
v___y_6117_ = v___x_6168_;
v___y_6118_ = v_a_6164_;
v___y_6119_ = v___y_6156_;
v___y_6120_ = v___x_6170_;
v___y_6121_ = v___y_6158_;
v___y_6122_ = v___y_6157_;
v___y_6123_ = v___x_6171_;
v___y_6124_ = v___y_6113_;
v___y_6125_ = v___y_6114_;
goto v___jp_6116_;
}
else
{
uint8_t v___x_6172_; 
lean_inc(v_a_6164_);
v___x_6172_ = l_Lean_MessageData_hasTag(v___y_6154_, v_a_6164_);
if (v___x_6172_ == 0)
{
lean_object* v___x_6173_; lean_object* v___x_6175_; 
lean_dec_ref_known(v___x_6170_, 1);
lean_dec_ref(v___x_6168_);
lean_dec(v_a_6164_);
v___x_6173_ = lean_box(0);
if (v_isShared_6167_ == 0)
{
lean_ctor_set(v___x_6166_, 0, v___x_6173_);
v___x_6175_ = v___x_6166_;
goto v_reusejp_6174_;
}
else
{
lean_object* v_reuseFailAlloc_6176_; 
v_reuseFailAlloc_6176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6176_, 0, v___x_6173_);
v___x_6175_ = v_reuseFailAlloc_6176_;
goto v_reusejp_6174_;
}
v_reusejp_6174_:
{
return v___x_6175_;
}
}
else
{
lean_del_object(v___x_6166_);
v___y_6117_ = v___x_6168_;
v___y_6118_ = v_a_6164_;
v___y_6119_ = v___y_6156_;
v___y_6120_ = v___x_6170_;
v___y_6121_ = v___y_6158_;
v___y_6122_ = v___y_6157_;
v___y_6123_ = v___x_6171_;
v___y_6124_ = v___y_6113_;
v___y_6125_ = v___y_6114_;
goto v___jp_6116_;
}
}
}
}
v___jp_6178_:
{
lean_object* v___x_6187_; 
v___x_6187_ = l_Lean_Syntax_getTailPos_x3f(v___y_6180_, v___y_6185_);
lean_dec(v___y_6180_);
if (lean_obj_tag(v___x_6187_) == 0)
{
lean_inc(v___y_6186_);
v___y_6154_ = v___y_6179_;
v___y_6155_ = v___y_6182_;
v___y_6156_ = v___y_6181_;
v___y_6157_ = v___y_6185_;
v___y_6158_ = v___y_6184_;
v___y_6159_ = v___y_6183_;
v___y_6160_ = v___y_6186_;
v___y_6161_ = v___y_6186_;
goto v___jp_6153_;
}
else
{
lean_object* v_val_6188_; 
v_val_6188_ = lean_ctor_get(v___x_6187_, 0);
lean_inc(v_val_6188_);
lean_dec_ref_known(v___x_6187_, 1);
v___y_6154_ = v___y_6179_;
v___y_6155_ = v___y_6182_;
v___y_6156_ = v___y_6181_;
v___y_6157_ = v___y_6185_;
v___y_6158_ = v___y_6184_;
v___y_6159_ = v___y_6183_;
v___y_6160_ = v___y_6186_;
v___y_6161_ = v_val_6188_;
goto v___jp_6153_;
}
}
v___jp_6189_:
{
lean_object* v_ref_6197_; lean_object* v___x_6198_; 
v_ref_6197_ = l_Lean_replaceRef(v_ref_6107_, v___y_6191_);
v___x_6198_ = l_Lean_Syntax_getPos_x3f(v_ref_6197_, v___y_6194_);
if (lean_obj_tag(v___x_6198_) == 0)
{
lean_object* v___x_6199_; 
v___x_6199_ = lean_unsigned_to_nat(0u);
v___y_6179_ = v___y_6190_;
v___y_6180_ = v_ref_6197_;
v___y_6181_ = v___y_6193_;
v___y_6182_ = v___y_6192_;
v___y_6183_ = v___y_6195_;
v___y_6184_ = v___y_6196_;
v___y_6185_ = v___y_6194_;
v___y_6186_ = v___x_6199_;
goto v___jp_6178_;
}
else
{
lean_object* v_val_6200_; 
v_val_6200_ = lean_ctor_get(v___x_6198_, 0);
lean_inc(v_val_6200_);
lean_dec_ref_known(v___x_6198_, 1);
v___y_6179_ = v___y_6190_;
v___y_6180_ = v_ref_6197_;
v___y_6181_ = v___y_6193_;
v___y_6182_ = v___y_6192_;
v___y_6183_ = v___y_6195_;
v___y_6184_ = v___y_6196_;
v___y_6185_ = v___y_6194_;
v___y_6186_ = v_val_6200_;
goto v___jp_6178_;
}
}
v___jp_6202_:
{
if (v___y_6209_ == 0)
{
v___y_6190_ = v___y_6205_;
v___y_6191_ = v___y_6206_;
v___y_6192_ = v___y_6207_;
v___y_6193_ = v___y_6203_;
v___y_6194_ = v___y_6208_;
v___y_6195_ = v___y_6204_;
v___y_6196_ = v_severity_6109_;
goto v___jp_6189_;
}
else
{
v___y_6190_ = v___y_6205_;
v___y_6191_ = v___y_6206_;
v___y_6192_ = v___y_6207_;
v___y_6193_ = v___y_6203_;
v___y_6194_ = v___y_6208_;
v___y_6195_ = v___y_6204_;
v___y_6196_ = v___x_6201_;
goto v___jp_6189_;
}
}
v___jp_6210_:
{
if (v___y_6211_ == 0)
{
lean_object* v_toCold_6212_; lean_object* v_ref_6213_; uint8_t v_suppressElabErrors_6214_; lean_object* v_fileName_6215_; lean_object* v_fileMap_6216_; lean_object* v_options_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___f_6220_; uint8_t v___x_6221_; uint8_t v___x_6222_; 
v_toCold_6212_ = lean_ctor_get(v___y_6113_, 0);
v_ref_6213_ = lean_ctor_get(v___y_6113_, 2);
v_suppressElabErrors_6214_ = lean_ctor_get_uint8(v___y_6113_, sizeof(void*)*3 + 1);
v_fileName_6215_ = lean_ctor_get(v_toCold_6212_, 0);
v_fileMap_6216_ = lean_ctor_get(v_toCold_6212_, 1);
v_options_6217_ = lean_ctor_get(v_toCold_6212_, 2);
v___x_6218_ = lean_box(v_suppressElabErrors_6214_);
v___x_6219_ = lean_box(v___y_6211_);
v___f_6220_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6220_, 0, v___x_6218_);
lean_closure_set(v___f_6220_, 1, v___x_6219_);
v___x_6221_ = 1;
v___x_6222_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6109_, v___x_6221_);
if (v___x_6222_ == 0)
{
v___y_6203_ = v_fileName_6215_;
v___y_6204_ = v_fileMap_6216_;
v___y_6205_ = v___f_6220_;
v___y_6206_ = v_ref_6213_;
v___y_6207_ = v_suppressElabErrors_6214_;
v___y_6208_ = v___y_6211_;
v___y_6209_ = v___x_6222_;
goto v___jp_6202_;
}
else
{
lean_object* v___x_6223_; uint8_t v___x_6224_; 
v___x_6223_ = l_Lean_warningAsError;
v___x_6224_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6217_, v___x_6223_);
v___y_6203_ = v_fileName_6215_;
v___y_6204_ = v_fileMap_6216_;
v___y_6205_ = v___f_6220_;
v___y_6206_ = v_ref_6213_;
v___y_6207_ = v_suppressElabErrors_6214_;
v___y_6208_ = v___y_6211_;
v___y_6209_ = v___x_6224_;
goto v___jp_6202_;
}
}
else
{
lean_object* v___x_6225_; lean_object* v___x_6226_; 
lean_dec_ref(v_msgData_6108_);
v___x_6225_ = lean_box(0);
v___x_6226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6225_);
return v___x_6226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6229_, lean_object* v_msgData_6230_, lean_object* v_severity_6231_, lean_object* v_isSilent_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
uint8_t v_severity_boxed_6238_; uint8_t v_isSilent_boxed_6239_; lean_object* v_res_6240_; 
v_severity_boxed_6238_ = lean_unbox(v_severity_6231_);
v_isSilent_boxed_6239_ = lean_unbox(v_isSilent_6232_);
v_res_6240_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6229_, v_msgData_6230_, v_severity_boxed_6238_, v_isSilent_boxed_6239_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_);
lean_dec(v___y_6236_);
lean_dec_ref(v___y_6235_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
lean_dec(v_ref_6229_);
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6241_, uint8_t v_severity_6242_, uint8_t v_isSilent_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_){
_start:
{
lean_object* v_ref_6249_; lean_object* v___x_6250_; 
v_ref_6249_ = lean_ctor_get(v___y_6246_, 2);
v___x_6250_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6249_, v_msgData_6241_, v_severity_6242_, v_isSilent_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
return v___x_6250_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6251_, lean_object* v_severity_6252_, lean_object* v_isSilent_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_){
_start:
{
uint8_t v_severity_boxed_6259_; uint8_t v_isSilent_boxed_6260_; lean_object* v_res_6261_; 
v_severity_boxed_6259_ = lean_unbox(v_severity_6252_);
v_isSilent_boxed_6260_ = lean_unbox(v_isSilent_6253_);
v_res_6261_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6251_, v_severity_boxed_6259_, v_isSilent_boxed_6260_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_);
lean_dec(v___y_6257_);
lean_dec_ref(v___y_6256_);
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
return v_res_6261_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_){
_start:
{
uint8_t v___x_6268_; uint8_t v___x_6269_; lean_object* v___x_6270_; 
v___x_6268_ = 2;
v___x_6269_ = 0;
v___x_6270_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6262_, v___x_6268_, v___x_6269_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
return v___x_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_){
_start:
{
lean_object* v_res_6277_; 
v_res_6277_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
return v_res_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_){
_start:
{
lean_object* v_module_6284_; lean_object* v_const_6285_; lean_object* v_exception_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v_module_6284_ = lean_ctor_get(v_f_6278_, 0);
lean_inc(v_module_6284_);
v_const_6285_ = lean_ctor_get(v_f_6278_, 1);
lean_inc(v_const_6285_);
v_exception_6286_ = lean_ctor_get(v_f_6278_, 2);
lean_inc_ref(v_exception_6286_);
lean_dec_ref(v_f_6278_);
v___x_6287_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6288_ = l_Lean_MessageData_ofName(v_const_6285_);
v___x_6289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6289_, 0, v___x_6287_);
lean_ctor_set(v___x_6289_, 1, v___x_6288_);
v___x_6290_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6291_, 0, v___x_6289_);
lean_ctor_set(v___x_6291_, 1, v___x_6290_);
v___x_6292_ = l_Lean_MessageData_ofName(v_module_6284_);
v___x_6293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6293_, 0, v___x_6291_);
lean_ctor_set(v___x_6293_, 1, v___x_6292_);
v___x_6294_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6295_, 0, v___x_6293_);
lean_ctor_set(v___x_6295_, 1, v___x_6294_);
v___x_6296_ = l_Lean_Exception_toMessageData(v_exception_6286_);
v___x_6297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6297_, 0, v___x_6295_);
lean_ctor_set(v___x_6297_, 1, v___x_6296_);
v___x_6298_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6297_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_);
return v___x_6298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_){
_start:
{
lean_object* v_res_6305_; 
v_res_6305_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6299_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
lean_dec(v___y_6303_);
lean_dec_ref(v___y_6302_);
lean_dec(v___y_6301_);
lean_dec_ref(v___y_6300_);
return v_res_6305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6306_, size_t v_i_6307_, size_t v_stop_6308_, lean_object* v_b_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_){
_start:
{
uint8_t v___x_6315_; 
v___x_6315_ = lean_usize_dec_eq(v_i_6307_, v_stop_6308_);
if (v___x_6315_ == 0)
{
lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6316_ = lean_array_uget_borrowed(v_as_6306_, v_i_6307_);
lean_inc(v___x_6316_);
v___x_6317_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6316_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
if (lean_obj_tag(v___x_6317_) == 0)
{
lean_object* v_a_6318_; size_t v___x_6319_; size_t v___x_6320_; 
v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
lean_inc(v_a_6318_);
lean_dec_ref_known(v___x_6317_, 1);
v___x_6319_ = ((size_t)1ULL);
v___x_6320_ = lean_usize_add(v_i_6307_, v___x_6319_);
v_i_6307_ = v___x_6320_;
v_b_6309_ = v_a_6318_;
goto _start;
}
else
{
return v___x_6317_;
}
}
else
{
lean_object* v___x_6322_; 
v___x_6322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6322_, 0, v_b_6309_);
return v___x_6322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6323_, lean_object* v_i_6324_, lean_object* v_stop_6325_, lean_object* v_b_6326_, lean_object* v___y_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_){
_start:
{
size_t v_i_boxed_6332_; size_t v_stop_boxed_6333_; lean_object* v_res_6334_; 
v_i_boxed_6332_ = lean_unbox_usize(v_i_6324_);
lean_dec(v_i_6324_);
v_stop_boxed_6333_ = lean_unbox_usize(v_stop_6325_);
lean_dec(v_stop_6325_);
v_res_6334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6323_, v_i_boxed_6332_, v_stop_boxed_6333_, v_b_6326_, v___y_6327_, v___y_6328_, v___y_6329_, v___y_6330_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
lean_dec(v___y_6328_);
lean_dec_ref(v___y_6327_);
lean_dec_ref(v_as_6323_);
return v_res_6334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6335_, size_t v_i_6336_, size_t v_stop_6337_, lean_object* v_b_6338_){
_start:
{
uint8_t v___x_6339_; 
v___x_6339_ = lean_usize_dec_eq(v_i_6336_, v_stop_6337_);
if (v___x_6339_ == 0)
{
lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; size_t v___x_6343_; size_t v___x_6344_; 
v___x_6340_ = lean_array_uget_borrowed(v_as_6335_, v_i_6336_);
lean_inc(v___x_6340_);
v___x_6341_ = lean_task_get_own(v___x_6340_);
v___x_6342_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6338_, v___x_6341_);
v___x_6343_ = ((size_t)1ULL);
v___x_6344_ = lean_usize_add(v_i_6336_, v___x_6343_);
v_i_6336_ = v___x_6344_;
v_b_6338_ = v___x_6342_;
goto _start;
}
else
{
return v_b_6338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6346_, lean_object* v_i_6347_, lean_object* v_stop_6348_, lean_object* v_b_6349_){
_start:
{
size_t v_i_boxed_6350_; size_t v_stop_boxed_6351_; lean_object* v_res_6352_; 
v_i_boxed_6350_ = lean_unbox_usize(v_i_6347_);
lean_dec(v_i_6347_);
v_stop_boxed_6351_ = lean_unbox_usize(v_stop_6348_);
lean_dec(v_stop_6348_);
v_res_6352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6346_, v_i_boxed_6350_, v_stop_boxed_6351_, v_b_6349_);
lean_dec_ref(v_as_6346_);
return v_res_6352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6353_, lean_object* v_tasks_6354_){
_start:
{
lean_object* v___x_6355_; lean_object* v___x_6356_; uint8_t v___x_6357_; 
v___x_6355_ = lean_unsigned_to_nat(0u);
v___x_6356_ = lean_array_get_size(v_tasks_6354_);
v___x_6357_ = lean_nat_dec_lt(v___x_6355_, v___x_6356_);
if (v___x_6357_ == 0)
{
return v_z_6353_;
}
else
{
size_t v___x_6358_; size_t v___x_6359_; lean_object* v___x_6360_; 
v___x_6358_ = ((size_t)0ULL);
v___x_6359_ = lean_usize_of_nat(v___x_6356_);
v___x_6360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6354_, v___x_6358_, v___x_6359_, v_z_6353_);
return v___x_6360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6361_, lean_object* v_tasks_6362_){
_start:
{
lean_object* v_res_6363_; 
v_res_6363_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6361_, v_tasks_6362_);
lean_dec_ref(v_tasks_6362_);
return v_res_6363_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; 
v___x_6364_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6365_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6366_, 0, v___x_6365_);
lean_ctor_set(v___x_6366_, 1, v___x_6364_);
return v___x_6366_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; 
v___x_6367_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6368_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6369_, 0, v___x_6368_);
lean_ctor_set(v___x_6369_, 1, v___x_6367_);
return v___x_6369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6370_, lean_object* v_ngen_6371_, lean_object* v_env_6372_, lean_object* v_act_6373_, lean_object* v_constantsPerTask_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_){
_start:
{
lean_object* v___x_6380_; lean_object* v_moduleData_6381_; lean_object* v_n_6382_; lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v_a_6386_; lean_object* v___x_6388_; uint8_t v_isShared_6389_; uint8_t v_isSharedCheck_6421_; 
v___x_6380_ = l_Lean_Environment_header(v_env_6372_);
v_moduleData_6381_ = lean_ctor_get(v___x_6380_, 6);
lean_inc_ref(v_moduleData_6381_);
lean_dec_ref(v___x_6380_);
v_n_6382_ = lean_array_get_size(v_moduleData_6381_);
lean_dec_ref(v_moduleData_6381_);
v___x_6383_ = lean_unsigned_to_nat(0u);
v___x_6384_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6385_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6370_, v_env_6372_, v_act_6373_, v_constantsPerTask_6374_, v_n_6382_, v_ngen_6371_, v___x_6384_, v___x_6383_, v___x_6383_, v___x_6383_);
v_a_6386_ = lean_ctor_get(v___x_6385_, 0);
v_isSharedCheck_6421_ = !lean_is_exclusive(v___x_6385_);
if (v_isSharedCheck_6421_ == 0)
{
v___x_6388_ = v___x_6385_;
v_isShared_6389_ = v_isSharedCheck_6421_;
goto v_resetjp_6387_;
}
else
{
lean_inc(v_a_6386_);
lean_dec(v___x_6385_);
v___x_6388_ = lean_box(0);
v_isShared_6389_ = v_isSharedCheck_6421_;
goto v_resetjp_6387_;
}
v_resetjp_6387_:
{
lean_object* v___x_6390_; lean_object* v_r_6391_; lean_object* v_tree_6392_; lean_object* v_errors_6393_; lean_object* v___x_6394_; uint8_t v___x_6395_; 
v___x_6390_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6391_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6390_, v_a_6386_);
lean_dec(v_a_6386_);
v_tree_6392_ = lean_ctor_get(v_r_6391_, 0);
lean_inc_ref(v_tree_6392_);
v_errors_6393_ = lean_ctor_get(v_r_6391_, 1);
lean_inc_ref(v_errors_6393_);
lean_dec_ref(v_r_6391_);
v___x_6394_ = lean_array_get_size(v_errors_6393_);
v___x_6395_ = lean_nat_dec_lt(v___x_6383_, v___x_6394_);
if (v___x_6395_ == 0)
{
lean_object* v___x_6396_; lean_object* v___x_6398_; 
lean_dec_ref(v_errors_6393_);
v___x_6396_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6392_);
if (v_isShared_6389_ == 0)
{
lean_ctor_set(v___x_6388_, 0, v___x_6396_);
v___x_6398_ = v___x_6388_;
goto v_reusejp_6397_;
}
else
{
lean_object* v_reuseFailAlloc_6399_; 
v_reuseFailAlloc_6399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6399_, 0, v___x_6396_);
v___x_6398_ = v_reuseFailAlloc_6399_;
goto v_reusejp_6397_;
}
v_reusejp_6397_:
{
return v___x_6398_;
}
}
else
{
lean_object* v___x_6400_; size_t v___x_6401_; size_t v___x_6402_; lean_object* v___x_6403_; 
lean_del_object(v___x_6388_);
v___x_6400_ = lean_box(0);
v___x_6401_ = ((size_t)0ULL);
v___x_6402_ = lean_usize_of_nat(v___x_6394_);
v___x_6403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6393_, v___x_6401_, v___x_6402_, v___x_6400_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_);
lean_dec_ref(v_errors_6393_);
if (lean_obj_tag(v___x_6403_) == 0)
{
lean_object* v___x_6405_; uint8_t v_isShared_6406_; uint8_t v_isSharedCheck_6411_; 
v_isSharedCheck_6411_ = !lean_is_exclusive(v___x_6403_);
if (v_isSharedCheck_6411_ == 0)
{
lean_object* v_unused_6412_; 
v_unused_6412_ = lean_ctor_get(v___x_6403_, 0);
lean_dec(v_unused_6412_);
v___x_6405_ = v___x_6403_;
v_isShared_6406_ = v_isSharedCheck_6411_;
goto v_resetjp_6404_;
}
else
{
lean_dec(v___x_6403_);
v___x_6405_ = lean_box(0);
v_isShared_6406_ = v_isSharedCheck_6411_;
goto v_resetjp_6404_;
}
v_resetjp_6404_:
{
lean_object* v___x_6407_; lean_object* v___x_6409_; 
v___x_6407_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6392_);
if (v_isShared_6406_ == 0)
{
lean_ctor_set(v___x_6405_, 0, v___x_6407_);
v___x_6409_ = v___x_6405_;
goto v_reusejp_6408_;
}
else
{
lean_object* v_reuseFailAlloc_6410_; 
v_reuseFailAlloc_6410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6410_, 0, v___x_6407_);
v___x_6409_ = v_reuseFailAlloc_6410_;
goto v_reusejp_6408_;
}
v_reusejp_6408_:
{
return v___x_6409_;
}
}
}
else
{
lean_object* v_a_6413_; lean_object* v___x_6415_; uint8_t v_isShared_6416_; uint8_t v_isSharedCheck_6420_; 
lean_dec_ref(v_tree_6392_);
v_a_6413_ = lean_ctor_get(v___x_6403_, 0);
v_isSharedCheck_6420_ = !lean_is_exclusive(v___x_6403_);
if (v_isSharedCheck_6420_ == 0)
{
v___x_6415_ = v___x_6403_;
v_isShared_6416_ = v_isSharedCheck_6420_;
goto v_resetjp_6414_;
}
else
{
lean_inc(v_a_6413_);
lean_dec(v___x_6403_);
v___x_6415_ = lean_box(0);
v_isShared_6416_ = v_isSharedCheck_6420_;
goto v_resetjp_6414_;
}
v_resetjp_6414_:
{
lean_object* v___x_6418_; 
if (v_isShared_6416_ == 0)
{
v___x_6418_ = v___x_6415_;
goto v_reusejp_6417_;
}
else
{
lean_object* v_reuseFailAlloc_6419_; 
v_reuseFailAlloc_6419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_a_6413_);
v___x_6418_ = v_reuseFailAlloc_6419_;
goto v_reusejp_6417_;
}
v_reusejp_6417_:
{
return v___x_6418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6422_, lean_object* v_ngen_6423_, lean_object* v_env_6424_, lean_object* v_act_6425_, lean_object* v_constantsPerTask_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_){
_start:
{
lean_object* v_res_6432_; 
v_res_6432_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6422_, v_ngen_6423_, v_env_6424_, v_act_6425_, v_constantsPerTask_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
lean_dec(v___y_6430_);
lean_dec_ref(v___y_6429_);
lean_dec(v___y_6428_);
lean_dec_ref(v___y_6427_);
lean_dec(v_constantsPerTask_6426_);
return v_res_6432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6433_, lean_object* v___x_6434_, lean_object* v_addEntry_6435_, lean_object* v_constantsPerTask_6436_, lean_object* v_droppedEntriesRef_6437_, lean_object* v_droppedKeys_6438_, lean_object* v___y_6439_, lean_object* v___y_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_){
_start:
{
lean_object* v___x_6444_; lean_object* v_env_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; 
v___x_6444_ = lean_st_ref_get(v___y_6442_);
v_env_6445_ = lean_ctor_get(v___x_6444_, 0);
lean_inc_ref(v_env_6445_);
lean_dec(v___x_6444_);
lean_inc_ref(v_a_6433_);
v___x_6446_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6433_);
v___x_6447_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6446_, v___x_6434_, v_env_6445_, v_addEntry_6435_, v_constantsPerTask_6436_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
if (lean_obj_tag(v___x_6447_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6437_) == 1)
{
lean_object* v_a_6448_; lean_object* v_val_6449_; lean_object* v___x_6451_; uint8_t v_isShared_6452_; uint8_t v_isSharedCheck_6482_; 
v_a_6448_ = lean_ctor_get(v___x_6447_, 0);
lean_inc(v_a_6448_);
lean_dec_ref_known(v___x_6447_, 1);
v_val_6449_ = lean_ctor_get(v_droppedEntriesRef_6437_, 0);
v_isSharedCheck_6482_ = !lean_is_exclusive(v_droppedEntriesRef_6437_);
if (v_isSharedCheck_6482_ == 0)
{
v___x_6451_ = v_droppedEntriesRef_6437_;
v_isShared_6452_ = v_isSharedCheck_6482_;
goto v_resetjp_6450_;
}
else
{
lean_inc(v_val_6449_);
lean_dec(v_droppedEntriesRef_6437_);
v___x_6451_ = lean_box(0);
v_isShared_6452_ = v_isSharedCheck_6482_;
goto v_resetjp_6450_;
}
v_resetjp_6450_:
{
lean_object* v___x_6453_; 
v___x_6453_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6448_, v_droppedKeys_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
lean_dec(v_droppedKeys_6438_);
if (lean_obj_tag(v___x_6453_) == 0)
{
lean_object* v_a_6454_; lean_object* v___x_6456_; uint8_t v_isShared_6457_; uint8_t v_isSharedCheck_6473_; 
v_a_6454_ = lean_ctor_get(v___x_6453_, 0);
v_isSharedCheck_6473_ = !lean_is_exclusive(v___x_6453_);
if (v_isSharedCheck_6473_ == 0)
{
v___x_6456_ = v___x_6453_;
v_isShared_6457_ = v_isSharedCheck_6473_;
goto v_resetjp_6455_;
}
else
{
lean_inc(v_a_6454_);
lean_dec(v___x_6453_);
v___x_6456_ = lean_box(0);
v_isShared_6457_ = v_isSharedCheck_6473_;
goto v_resetjp_6455_;
}
v_resetjp_6455_:
{
lean_object* v_fst_6458_; lean_object* v_snd_6459_; lean_object* v___x_6460_; lean_object* v___y_6462_; 
v_fst_6458_ = lean_ctor_get(v_a_6454_, 0);
lean_inc(v_fst_6458_);
v_snd_6459_ = lean_ctor_get(v_a_6454_, 1);
lean_inc(v_snd_6459_);
lean_dec(v_a_6454_);
v___x_6460_ = lean_st_ref_get(v_val_6449_);
if (lean_obj_tag(v___x_6460_) == 0)
{
lean_object* v___x_6471_; 
v___x_6471_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6462_ = v___x_6471_;
goto v___jp_6461_;
}
else
{
lean_object* v_val_6472_; 
v_val_6472_ = lean_ctor_get(v___x_6460_, 0);
lean_inc(v_val_6472_);
lean_dec_ref_known(v___x_6460_, 1);
v___y_6462_ = v_val_6472_;
goto v___jp_6461_;
}
v___jp_6461_:
{
lean_object* v___x_6463_; lean_object* v___x_6465_; 
v___x_6463_ = l_Array_append___redArg(v___y_6462_, v_fst_6458_);
lean_dec(v_fst_6458_);
if (v_isShared_6452_ == 0)
{
lean_ctor_set(v___x_6451_, 0, v___x_6463_);
v___x_6465_ = v___x_6451_;
goto v_reusejp_6464_;
}
else
{
lean_object* v_reuseFailAlloc_6470_; 
v_reuseFailAlloc_6470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6470_, 0, v___x_6463_);
v___x_6465_ = v_reuseFailAlloc_6470_;
goto v_reusejp_6464_;
}
v_reusejp_6464_:
{
lean_object* v___x_6466_; lean_object* v___x_6468_; 
v___x_6466_ = lean_st_ref_swap(v_val_6449_, v___x_6465_);
lean_dec(v_val_6449_);
lean_dec(v___x_6466_);
if (v_isShared_6457_ == 0)
{
lean_ctor_set(v___x_6456_, 0, v_snd_6459_);
v___x_6468_ = v___x_6456_;
goto v_reusejp_6467_;
}
else
{
lean_object* v_reuseFailAlloc_6469_; 
v_reuseFailAlloc_6469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6469_, 0, v_snd_6459_);
v___x_6468_ = v_reuseFailAlloc_6469_;
goto v_reusejp_6467_;
}
v_reusejp_6467_:
{
return v___x_6468_;
}
}
}
}
}
else
{
lean_object* v_a_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6481_; 
lean_del_object(v___x_6451_);
lean_dec(v_val_6449_);
v_a_6474_ = lean_ctor_get(v___x_6453_, 0);
v_isSharedCheck_6481_ = !lean_is_exclusive(v___x_6453_);
if (v_isSharedCheck_6481_ == 0)
{
v___x_6476_ = v___x_6453_;
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_a_6474_);
lean_dec(v___x_6453_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v___x_6479_; 
if (v_isShared_6477_ == 0)
{
v___x_6479_ = v___x_6476_;
goto v_reusejp_6478_;
}
else
{
lean_object* v_reuseFailAlloc_6480_; 
v_reuseFailAlloc_6480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6480_, 0, v_a_6474_);
v___x_6479_ = v_reuseFailAlloc_6480_;
goto v_reusejp_6478_;
}
v_reusejp_6478_:
{
return v___x_6479_;
}
}
}
}
}
else
{
lean_object* v_a_6483_; lean_object* v___x_6484_; 
lean_dec(v_droppedEntriesRef_6437_);
v_a_6483_ = lean_ctor_get(v___x_6447_, 0);
lean_inc(v_a_6483_);
lean_dec_ref_known(v___x_6447_, 1);
v___x_6484_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6483_, v_droppedKeys_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_);
return v___x_6484_;
}
}
else
{
lean_dec(v_droppedKeys_6438_);
lean_dec(v_droppedEntriesRef_6437_);
return v___x_6447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6485_, lean_object* v___x_6486_, lean_object* v_addEntry_6487_, lean_object* v_constantsPerTask_6488_, lean_object* v_droppedEntriesRef_6489_, lean_object* v_droppedKeys_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_){
_start:
{
lean_object* v_res_6496_; 
v_res_6496_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6485_, v___x_6486_, v_addEntry_6487_, v_constantsPerTask_6488_, v_droppedEntriesRef_6489_, v_droppedKeys_6490_, v___y_6491_, v___y_6492_, v___y_6493_, v___y_6494_);
lean_dec(v___y_6494_);
lean_dec_ref(v___y_6493_);
lean_dec(v___y_6492_);
lean_dec_ref(v___y_6491_);
lean_dec(v_constantsPerTask_6488_);
lean_dec_ref(v_a_6485_);
return v_res_6496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6498_, lean_object* v_addEntry_6499_, lean_object* v_droppedKeys_6500_, lean_object* v_constantsPerTask_6501_, lean_object* v_droppedEntriesRef_6502_, lean_object* v_ty_6503_, lean_object* v_a_6504_, lean_object* v_a_6505_, lean_object* v_a_6506_, lean_object* v_a_6507_){
_start:
{
lean_object* v_a_6510_; lean_object* v___x_6532_; lean_object* v_ngen_6533_; lean_object* v_namePrefix_6534_; lean_object* v_idx_6535_; lean_object* v___x_6537_; uint8_t v_isShared_6538_; uint8_t v_isSharedCheck_6581_; 
v___x_6532_ = lean_st_ref_get(v_a_6507_);
v_ngen_6533_ = lean_ctor_get(v___x_6532_, 2);
lean_inc_ref(v_ngen_6533_);
lean_dec(v___x_6532_);
v_namePrefix_6534_ = lean_ctor_get(v_ngen_6533_, 0);
v_idx_6535_ = lean_ctor_get(v_ngen_6533_, 1);
v_isSharedCheck_6581_ = !lean_is_exclusive(v_ngen_6533_);
if (v_isSharedCheck_6581_ == 0)
{
v___x_6537_ = v_ngen_6533_;
v_isShared_6538_ = v_isSharedCheck_6581_;
goto v_resetjp_6536_;
}
else
{
lean_inc(v_idx_6535_);
lean_inc(v_namePrefix_6534_);
lean_dec(v_ngen_6533_);
v___x_6537_ = lean_box(0);
v_isShared_6538_ = v_isSharedCheck_6581_;
goto v_resetjp_6536_;
}
v___jp_6509_:
{
lean_object* v___x_6511_; 
v___x_6511_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6510_, v_ty_6503_, v_a_6504_, v_a_6505_, v_a_6506_, v_a_6507_);
if (lean_obj_tag(v___x_6511_) == 0)
{
lean_object* v_a_6512_; lean_object* v___x_6514_; uint8_t v_isShared_6515_; uint8_t v_isSharedCheck_6523_; 
v_a_6512_ = lean_ctor_get(v___x_6511_, 0);
v_isSharedCheck_6523_ = !lean_is_exclusive(v___x_6511_);
if (v_isSharedCheck_6523_ == 0)
{
v___x_6514_ = v___x_6511_;
v_isShared_6515_ = v_isSharedCheck_6523_;
goto v_resetjp_6513_;
}
else
{
lean_inc(v_a_6512_);
lean_dec(v___x_6511_);
v___x_6514_ = lean_box(0);
v_isShared_6515_ = v_isSharedCheck_6523_;
goto v_resetjp_6513_;
}
v_resetjp_6513_:
{
lean_object* v_fst_6516_; lean_object* v_snd_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6521_; 
v_fst_6516_ = lean_ctor_get(v_a_6512_, 0);
lean_inc(v_fst_6516_);
v_snd_6517_ = lean_ctor_get(v_a_6512_, 1);
lean_inc(v_snd_6517_);
lean_dec(v_a_6512_);
v___x_6518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6518_, 0, v_snd_6517_);
v___x_6519_ = lean_st_ref_swap(v_ref_6498_, v___x_6518_);
lean_dec(v___x_6519_);
if (v_isShared_6515_ == 0)
{
lean_ctor_set(v___x_6514_, 0, v_fst_6516_);
v___x_6521_ = v___x_6514_;
goto v_reusejp_6520_;
}
else
{
lean_object* v_reuseFailAlloc_6522_; 
v_reuseFailAlloc_6522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6522_, 0, v_fst_6516_);
v___x_6521_ = v_reuseFailAlloc_6522_;
goto v_reusejp_6520_;
}
v_reusejp_6520_:
{
return v___x_6521_;
}
}
}
else
{
lean_object* v_a_6524_; lean_object* v___x_6526_; uint8_t v_isShared_6527_; uint8_t v_isSharedCheck_6531_; 
v_a_6524_ = lean_ctor_get(v___x_6511_, 0);
v_isSharedCheck_6531_ = !lean_is_exclusive(v___x_6511_);
if (v_isSharedCheck_6531_ == 0)
{
v___x_6526_ = v___x_6511_;
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
else
{
lean_inc(v_a_6524_);
lean_dec(v___x_6511_);
v___x_6526_ = lean_box(0);
v_isShared_6527_ = v_isSharedCheck_6531_;
goto v_resetjp_6525_;
}
v_resetjp_6525_:
{
lean_object* v___x_6529_; 
if (v_isShared_6527_ == 0)
{
v___x_6529_ = v___x_6526_;
goto v_reusejp_6528_;
}
else
{
lean_object* v_reuseFailAlloc_6530_; 
v_reuseFailAlloc_6530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6530_, 0, v_a_6524_);
v___x_6529_ = v_reuseFailAlloc_6530_;
goto v_reusejp_6528_;
}
v_reusejp_6528_:
{
return v___x_6529_;
}
}
}
}
v_resetjp_6536_:
{
lean_object* v___x_6539_; lean_object* v_env_6540_; lean_object* v_nextMacroScope_6541_; lean_object* v_auxDeclNGen_6542_; lean_object* v_traceState_6543_; lean_object* v_cache_6544_; lean_object* v_messages_6545_; lean_object* v_infoState_6546_; lean_object* v_snapshotTasks_6547_; lean_object* v___x_6549_; uint8_t v_isShared_6550_; uint8_t v_isSharedCheck_6579_; 
v___x_6539_ = lean_st_ref_take(v_a_6507_);
v_env_6540_ = lean_ctor_get(v___x_6539_, 0);
v_nextMacroScope_6541_ = lean_ctor_get(v___x_6539_, 1);
v_auxDeclNGen_6542_ = lean_ctor_get(v___x_6539_, 3);
v_traceState_6543_ = lean_ctor_get(v___x_6539_, 4);
v_cache_6544_ = lean_ctor_get(v___x_6539_, 5);
v_messages_6545_ = lean_ctor_get(v___x_6539_, 6);
v_infoState_6546_ = lean_ctor_get(v___x_6539_, 7);
v_snapshotTasks_6547_ = lean_ctor_get(v___x_6539_, 8);
v_isSharedCheck_6579_ = !lean_is_exclusive(v___x_6539_);
if (v_isSharedCheck_6579_ == 0)
{
lean_object* v_unused_6580_; 
v_unused_6580_ = lean_ctor_get(v___x_6539_, 2);
lean_dec(v_unused_6580_);
v___x_6549_ = v___x_6539_;
v_isShared_6550_ = v_isSharedCheck_6579_;
goto v_resetjp_6548_;
}
else
{
lean_inc(v_snapshotTasks_6547_);
lean_inc(v_infoState_6546_);
lean_inc(v_messages_6545_);
lean_inc(v_cache_6544_);
lean_inc(v_traceState_6543_);
lean_inc(v_auxDeclNGen_6542_);
lean_inc(v_nextMacroScope_6541_);
lean_inc(v_env_6540_);
lean_dec(v___x_6539_);
v___x_6549_ = lean_box(0);
v_isShared_6550_ = v_isSharedCheck_6579_;
goto v_resetjp_6548_;
}
v_resetjp_6548_:
{
lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6555_; 
lean_inc(v_idx_6535_);
lean_inc(v_namePrefix_6534_);
v___x_6551_ = l_Lean_Name_num___override(v_namePrefix_6534_, v_idx_6535_);
v___x_6552_ = lean_unsigned_to_nat(1u);
v___x_6553_ = lean_nat_add(v_idx_6535_, v___x_6552_);
lean_dec(v_idx_6535_);
if (v_isShared_6538_ == 0)
{
lean_ctor_set(v___x_6537_, 1, v___x_6553_);
v___x_6555_ = v___x_6537_;
goto v_reusejp_6554_;
}
else
{
lean_object* v_reuseFailAlloc_6578_; 
v_reuseFailAlloc_6578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6578_, 0, v_namePrefix_6534_);
lean_ctor_set(v_reuseFailAlloc_6578_, 1, v___x_6553_);
v___x_6555_ = v_reuseFailAlloc_6578_;
goto v_reusejp_6554_;
}
v_reusejp_6554_:
{
lean_object* v___x_6557_; 
if (v_isShared_6550_ == 0)
{
lean_ctor_set(v___x_6549_, 2, v___x_6555_);
v___x_6557_ = v___x_6549_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6577_; 
v_reuseFailAlloc_6577_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6577_, 0, v_env_6540_);
lean_ctor_set(v_reuseFailAlloc_6577_, 1, v_nextMacroScope_6541_);
lean_ctor_set(v_reuseFailAlloc_6577_, 2, v___x_6555_);
lean_ctor_set(v_reuseFailAlloc_6577_, 3, v_auxDeclNGen_6542_);
lean_ctor_set(v_reuseFailAlloc_6577_, 4, v_traceState_6543_);
lean_ctor_set(v_reuseFailAlloc_6577_, 5, v_cache_6544_);
lean_ctor_set(v_reuseFailAlloc_6577_, 6, v_messages_6545_);
lean_ctor_set(v_reuseFailAlloc_6577_, 7, v_infoState_6546_);
lean_ctor_set(v_reuseFailAlloc_6577_, 8, v_snapshotTasks_6547_);
v___x_6557_ = v_reuseFailAlloc_6577_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
lean_object* v___x_6558_; lean_object* v___x_6559_; 
v___x_6558_ = lean_st_ref_put(v_a_6507_, v___x_6557_);
v___x_6559_ = lean_st_ref_get(v_ref_6498_);
if (lean_obj_tag(v___x_6559_) == 0)
{
lean_object* v_toCold_6560_; lean_object* v_options_6561_; lean_object* v___x_6562_; lean_object* v___f_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; 
v_toCold_6560_ = lean_ctor_get(v_a_6506_, 0);
v_options_6561_ = lean_ctor_get(v_toCold_6560_, 2);
v___x_6562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6562_, 0, v___x_6551_);
lean_ctor_set(v___x_6562_, 1, v___x_6552_);
lean_inc_ref(v_a_6506_);
v___f_6563_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6563_, 0, v_a_6506_);
lean_closure_set(v___f_6563_, 1, v___x_6562_);
lean_closure_set(v___f_6563_, 2, v_addEntry_6499_);
lean_closure_set(v___f_6563_, 3, v_constantsPerTask_6501_);
lean_closure_set(v___f_6563_, 4, v_droppedEntriesRef_6502_);
lean_closure_set(v___f_6563_, 5, v_droppedKeys_6500_);
v___x_6564_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6565_ = lean_box(0);
v___x_6566_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6564_, v_options_6561_, v___f_6563_, v___x_6565_, v_a_6504_, v_a_6505_, v_a_6506_, v_a_6507_);
if (lean_obj_tag(v___x_6566_) == 0)
{
lean_object* v_a_6567_; 
v_a_6567_ = lean_ctor_get(v___x_6566_, 0);
lean_inc(v_a_6567_);
lean_dec_ref_known(v___x_6566_, 1);
v_a_6510_ = v_a_6567_;
goto v___jp_6509_;
}
else
{
lean_object* v_a_6568_; lean_object* v___x_6570_; uint8_t v_isShared_6571_; uint8_t v_isSharedCheck_6575_; 
lean_dec_ref(v_ty_6503_);
v_a_6568_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6575_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6575_ == 0)
{
v___x_6570_ = v___x_6566_;
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
else
{
lean_inc(v_a_6568_);
lean_dec(v___x_6566_);
v___x_6570_ = lean_box(0);
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
v_resetjp_6569_:
{
lean_object* v___x_6573_; 
if (v_isShared_6571_ == 0)
{
v___x_6573_ = v___x_6570_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v_a_6568_);
v___x_6573_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6572_;
}
v_reusejp_6572_:
{
return v___x_6573_;
}
}
}
}
else
{
lean_object* v_val_6576_; 
lean_dec(v___x_6551_);
lean_dec(v_droppedEntriesRef_6502_);
lean_dec(v_constantsPerTask_6501_);
lean_dec(v_droppedKeys_6500_);
lean_dec_ref(v_addEntry_6499_);
v_val_6576_ = lean_ctor_get(v___x_6559_, 0);
lean_inc(v_val_6576_);
lean_dec_ref_known(v___x_6559_, 1);
v_a_6510_ = v_val_6576_;
goto v___jp_6509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6582_, lean_object* v_addEntry_6583_, lean_object* v_droppedKeys_6584_, lean_object* v_constantsPerTask_6585_, lean_object* v_droppedEntriesRef_6586_, lean_object* v_ty_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_){
_start:
{
lean_object* v_res_6593_; 
v_res_6593_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6582_, v_addEntry_6583_, v_droppedKeys_6584_, v_constantsPerTask_6585_, v_droppedEntriesRef_6586_, v_ty_6587_, v_a_6588_, v_a_6589_, v_a_6590_, v_a_6591_);
lean_dec(v_a_6591_);
lean_dec_ref(v_a_6590_);
lean_dec(v_a_6589_);
lean_dec_ref(v_a_6588_);
lean_dec(v_ref_6582_);
return v_res_6593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6594_, lean_object* v_ref_6595_, lean_object* v_addEntry_6596_, lean_object* v_droppedKeys_6597_, lean_object* v_constantsPerTask_6598_, lean_object* v_droppedEntriesRef_6599_, lean_object* v_ty_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_, lean_object* v_a_6603_, lean_object* v_a_6604_){
_start:
{
lean_object* v___x_6606_; 
v___x_6606_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6595_, v_addEntry_6596_, v_droppedKeys_6597_, v_constantsPerTask_6598_, v_droppedEntriesRef_6599_, v_ty_6600_, v_a_6601_, v_a_6602_, v_a_6603_, v_a_6604_);
return v___x_6606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6607_, lean_object* v_ref_6608_, lean_object* v_addEntry_6609_, lean_object* v_droppedKeys_6610_, lean_object* v_constantsPerTask_6611_, lean_object* v_droppedEntriesRef_6612_, lean_object* v_ty_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_){
_start:
{
lean_object* v_res_6619_; 
v_res_6619_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6607_, v_ref_6608_, v_addEntry_6609_, v_droppedKeys_6610_, v_constantsPerTask_6611_, v_droppedEntriesRef_6612_, v_ty_6613_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_);
lean_dec(v_a_6617_);
lean_dec_ref(v_a_6616_);
lean_dec(v_a_6615_);
lean_dec_ref(v_a_6614_);
lean_dec(v_ref_6608_);
return v_res_6619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6620_, lean_object* v_cctx_6621_, lean_object* v_ngen_6622_, lean_object* v_env_6623_, lean_object* v_act_6624_, lean_object* v_constantsPerTask_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_){
_start:
{
lean_object* v___x_6631_; 
v___x_6631_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6621_, v_ngen_6622_, v_env_6623_, v_act_6624_, v_constantsPerTask_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
return v___x_6631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6632_, lean_object* v_cctx_6633_, lean_object* v_ngen_6634_, lean_object* v_env_6635_, lean_object* v_act_6636_, lean_object* v_constantsPerTask_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_, lean_object* v___y_6640_, lean_object* v___y_6641_, lean_object* v___y_6642_){
_start:
{
lean_object* v_res_6643_; 
v_res_6643_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6632_, v_cctx_6633_, v_ngen_6634_, v_env_6635_, v_act_6636_, v_constantsPerTask_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_);
lean_dec(v___y_6641_);
lean_dec_ref(v___y_6640_);
lean_dec(v___y_6639_);
lean_dec_ref(v___y_6638_);
lean_dec(v_constantsPerTask_6637_);
return v_res_6643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6644_, lean_object* v_cctx_6645_, lean_object* v_env_6646_, lean_object* v_act_6647_, lean_object* v_constantsPerTask_6648_, lean_object* v_n_6649_, lean_object* v_ngen_6650_, lean_object* v_tasks_6651_, lean_object* v_start_6652_, lean_object* v_cnt_6653_, lean_object* v_idx_6654_, lean_object* v___y_6655_, lean_object* v___y_6656_, lean_object* v___y_6657_, lean_object* v___y_6658_){
_start:
{
lean_object* v___x_6660_; 
v___x_6660_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6645_, v_env_6646_, v_act_6647_, v_constantsPerTask_6648_, v_n_6649_, v_ngen_6650_, v_tasks_6651_, v_start_6652_, v_cnt_6653_, v_idx_6654_);
return v___x_6660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6661_, lean_object* v_cctx_6662_, lean_object* v_env_6663_, lean_object* v_act_6664_, lean_object* v_constantsPerTask_6665_, lean_object* v_n_6666_, lean_object* v_ngen_6667_, lean_object* v_tasks_6668_, lean_object* v_start_6669_, lean_object* v_cnt_6670_, lean_object* v_idx_6671_, lean_object* v___y_6672_, lean_object* v___y_6673_, lean_object* v___y_6674_, lean_object* v___y_6675_, lean_object* v___y_6676_){
_start:
{
lean_object* v_res_6677_; 
v_res_6677_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6661_, v_cctx_6662_, v_env_6663_, v_act_6664_, v_constantsPerTask_6665_, v_n_6666_, v_ngen_6667_, v_tasks_6668_, v_start_6669_, v_cnt_6670_, v_idx_6671_, v___y_6672_, v___y_6673_, v___y_6674_, v___y_6675_);
lean_dec(v___y_6675_);
lean_dec_ref(v___y_6674_);
lean_dec(v___y_6673_);
lean_dec_ref(v___y_6672_);
lean_dec(v_constantsPerTask_6665_);
return v_res_6677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6678_, lean_object* v_z_6679_, lean_object* v_tasks_6680_){
_start:
{
lean_object* v___x_6681_; 
v___x_6681_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6679_, v_tasks_6680_);
return v___x_6681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6682_, lean_object* v_z_6683_, lean_object* v_tasks_6684_){
_start:
{
lean_object* v_res_6685_; 
v_res_6685_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6682_, v_z_6683_, v_tasks_6684_);
lean_dec_ref(v_tasks_6684_);
return v_res_6685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6686_, lean_object* v_as_6687_, size_t v_i_6688_, size_t v_stop_6689_, lean_object* v_b_6690_){
_start:
{
lean_object* v___x_6691_; 
v___x_6691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6687_, v_i_6688_, v_stop_6689_, v_b_6690_);
return v___x_6691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6692_, lean_object* v_as_6693_, lean_object* v_i_6694_, lean_object* v_stop_6695_, lean_object* v_b_6696_){
_start:
{
size_t v_i_boxed_6697_; size_t v_stop_boxed_6698_; lean_object* v_res_6699_; 
v_i_boxed_6697_ = lean_unbox_usize(v_i_6694_);
lean_dec(v_i_6694_);
v_stop_boxed_6698_ = lean_unbox_usize(v_stop_6695_);
lean_dec(v_stop_6695_);
v_res_6699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6692_, v_as_6693_, v_i_boxed_6697_, v_stop_boxed_6698_, v_b_6696_);
lean_dec_ref(v_as_6693_);
return v_res_6699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6700_){
_start:
{
lean_object* v___x_6702_; lean_object* v_ngen_6703_; lean_object* v_namePrefix_6704_; lean_object* v_idx_6705_; lean_object* v___x_6707_; uint8_t v_isShared_6708_; uint8_t v_isSharedCheck_6735_; 
v___x_6702_ = lean_st_ref_get(v___y_6700_);
v_ngen_6703_ = lean_ctor_get(v___x_6702_, 2);
lean_inc_ref(v_ngen_6703_);
lean_dec(v___x_6702_);
v_namePrefix_6704_ = lean_ctor_get(v_ngen_6703_, 0);
v_idx_6705_ = lean_ctor_get(v_ngen_6703_, 1);
v_isSharedCheck_6735_ = !lean_is_exclusive(v_ngen_6703_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6707_ = v_ngen_6703_;
v_isShared_6708_ = v_isSharedCheck_6735_;
goto v_resetjp_6706_;
}
else
{
lean_inc(v_idx_6705_);
lean_inc(v_namePrefix_6704_);
lean_dec(v_ngen_6703_);
v___x_6707_ = lean_box(0);
v_isShared_6708_ = v_isSharedCheck_6735_;
goto v_resetjp_6706_;
}
v_resetjp_6706_:
{
lean_object* v___x_6709_; lean_object* v_env_6710_; lean_object* v_nextMacroScope_6711_; lean_object* v_auxDeclNGen_6712_; lean_object* v_traceState_6713_; lean_object* v_cache_6714_; lean_object* v_messages_6715_; lean_object* v_infoState_6716_; lean_object* v_snapshotTasks_6717_; lean_object* v___x_6719_; uint8_t v_isShared_6720_; uint8_t v_isSharedCheck_6733_; 
v___x_6709_ = lean_st_ref_take(v___y_6700_);
v_env_6710_ = lean_ctor_get(v___x_6709_, 0);
v_nextMacroScope_6711_ = lean_ctor_get(v___x_6709_, 1);
v_auxDeclNGen_6712_ = lean_ctor_get(v___x_6709_, 3);
v_traceState_6713_ = lean_ctor_get(v___x_6709_, 4);
v_cache_6714_ = lean_ctor_get(v___x_6709_, 5);
v_messages_6715_ = lean_ctor_get(v___x_6709_, 6);
v_infoState_6716_ = lean_ctor_get(v___x_6709_, 7);
v_snapshotTasks_6717_ = lean_ctor_get(v___x_6709_, 8);
v_isSharedCheck_6733_ = !lean_is_exclusive(v___x_6709_);
if (v_isSharedCheck_6733_ == 0)
{
lean_object* v_unused_6734_; 
v_unused_6734_ = lean_ctor_get(v___x_6709_, 2);
lean_dec(v_unused_6734_);
v___x_6719_ = v___x_6709_;
v_isShared_6720_ = v_isSharedCheck_6733_;
goto v_resetjp_6718_;
}
else
{
lean_inc(v_snapshotTasks_6717_);
lean_inc(v_infoState_6716_);
lean_inc(v_messages_6715_);
lean_inc(v_cache_6714_);
lean_inc(v_traceState_6713_);
lean_inc(v_auxDeclNGen_6712_);
lean_inc(v_nextMacroScope_6711_);
lean_inc(v_env_6710_);
lean_dec(v___x_6709_);
v___x_6719_ = lean_box(0);
v_isShared_6720_ = v_isSharedCheck_6733_;
goto v_resetjp_6718_;
}
v_resetjp_6718_:
{
lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6725_; 
lean_inc(v_idx_6705_);
lean_inc(v_namePrefix_6704_);
v___x_6721_ = l_Lean_Name_num___override(v_namePrefix_6704_, v_idx_6705_);
v___x_6722_ = lean_unsigned_to_nat(1u);
v___x_6723_ = lean_nat_add(v_idx_6705_, v___x_6722_);
lean_dec(v_idx_6705_);
if (v_isShared_6708_ == 0)
{
lean_ctor_set(v___x_6707_, 1, v___x_6723_);
v___x_6725_ = v___x_6707_;
goto v_reusejp_6724_;
}
else
{
lean_object* v_reuseFailAlloc_6732_; 
v_reuseFailAlloc_6732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6732_, 0, v_namePrefix_6704_);
lean_ctor_set(v_reuseFailAlloc_6732_, 1, v___x_6723_);
v___x_6725_ = v_reuseFailAlloc_6732_;
goto v_reusejp_6724_;
}
v_reusejp_6724_:
{
lean_object* v___x_6727_; 
if (v_isShared_6720_ == 0)
{
lean_ctor_set(v___x_6719_, 2, v___x_6725_);
v___x_6727_ = v___x_6719_;
goto v_reusejp_6726_;
}
else
{
lean_object* v_reuseFailAlloc_6731_; 
v_reuseFailAlloc_6731_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6731_, 0, v_env_6710_);
lean_ctor_set(v_reuseFailAlloc_6731_, 1, v_nextMacroScope_6711_);
lean_ctor_set(v_reuseFailAlloc_6731_, 2, v___x_6725_);
lean_ctor_set(v_reuseFailAlloc_6731_, 3, v_auxDeclNGen_6712_);
lean_ctor_set(v_reuseFailAlloc_6731_, 4, v_traceState_6713_);
lean_ctor_set(v_reuseFailAlloc_6731_, 5, v_cache_6714_);
lean_ctor_set(v_reuseFailAlloc_6731_, 6, v_messages_6715_);
lean_ctor_set(v_reuseFailAlloc_6731_, 7, v_infoState_6716_);
lean_ctor_set(v_reuseFailAlloc_6731_, 8, v_snapshotTasks_6717_);
v___x_6727_ = v_reuseFailAlloc_6731_;
goto v_reusejp_6726_;
}
v_reusejp_6726_:
{
lean_object* v___x_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; 
v___x_6728_ = lean_st_ref_put(v___y_6700_, v___x_6727_);
v___x_6729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6729_, 0, v___x_6721_);
lean_ctor_set(v___x_6729_, 1, v___x_6722_);
v___x_6730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6730_, 0, v___x_6729_);
return v___x_6730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6736_, lean_object* v___y_6737_){
_start:
{
lean_object* v_res_6738_; 
v_res_6738_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6736_);
lean_dec(v___y_6736_);
return v_res_6738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6739_, lean_object* v___y_6740_){
_start:
{
lean_object* v___x_6742_; 
v___x_6742_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6740_);
return v___x_6742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6743_, lean_object* v___y_6744_, lean_object* v___y_6745_){
_start:
{
lean_object* v_res_6746_; 
v_res_6746_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6743_, v___y_6744_);
lean_dec(v___y_6744_);
lean_dec_ref(v___y_6743_);
return v_res_6746_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6747_; lean_object* v___x_6748_; lean_object* v___x_6749_; 
v___x_6747_ = lean_unsigned_to_nat(32u);
v___x_6748_ = lean_mk_empty_array_with_capacity(v___x_6747_);
v___x_6749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6749_, 0, v___x_6748_);
return v___x_6749_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6750_; lean_object* v___x_6751_; lean_object* v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; 
v___x_6750_ = ((size_t)5ULL);
v___x_6751_ = lean_unsigned_to_nat(0u);
v___x_6752_ = lean_unsigned_to_nat(32u);
v___x_6753_ = lean_mk_empty_array_with_capacity(v___x_6752_);
v___x_6754_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6755_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6755_, 0, v___x_6754_);
lean_ctor_set(v___x_6755_, 1, v___x_6753_);
lean_ctor_set(v___x_6755_, 2, v___x_6751_);
lean_ctor_set(v___x_6755_, 3, v___x_6751_);
lean_ctor_set_usize(v___x_6755_, 4, v___x_6750_);
return v___x_6755_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6756_; lean_object* v___x_6757_; lean_object* v___x_6758_; lean_object* v___x_6759_; 
v___x_6756_ = lean_box(1);
v___x_6757_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6758_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6759_, 0, v___x_6758_);
lean_ctor_set(v___x_6759_, 1, v___x_6757_);
lean_ctor_set(v___x_6759_, 2, v___x_6756_);
return v___x_6759_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6760_, lean_object* v___y_6761_, lean_object* v___y_6762_){
_start:
{
lean_object* v___x_6764_; lean_object* v_toCold_6765_; lean_object* v_env_6766_; lean_object* v_options_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; 
v___x_6764_ = lean_st_ref_get(v___y_6762_);
v_toCold_6765_ = lean_ctor_get(v___y_6761_, 0);
v_env_6766_ = lean_ctor_get(v___x_6764_, 0);
lean_inc_ref(v_env_6766_);
lean_dec(v___x_6764_);
v_options_6767_ = lean_ctor_get(v_toCold_6765_, 2);
v___x_6768_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6769_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6767_);
v___x_6770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6770_, 0, v_env_6766_);
lean_ctor_set(v___x_6770_, 1, v___x_6768_);
lean_ctor_set(v___x_6770_, 2, v___x_6769_);
lean_ctor_set(v___x_6770_, 3, v_options_6767_);
v___x_6771_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6771_, 0, v___x_6770_);
lean_ctor_set(v___x_6771_, 1, v_msgData_6760_);
v___x_6772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6772_, 0, v___x_6771_);
return v___x_6772_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6773_, lean_object* v___y_6774_, lean_object* v___y_6775_, lean_object* v___y_6776_){
_start:
{
lean_object* v_res_6777_; 
v_res_6777_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6773_, v___y_6774_, v___y_6775_);
lean_dec(v___y_6775_);
lean_dec_ref(v___y_6774_);
return v_res_6777_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6778_, lean_object* v_msgData_6779_, uint8_t v_severity_6780_, uint8_t v_isSilent_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_){
_start:
{
uint8_t v___y_6786_; lean_object* v___y_6787_; lean_object* v___y_6788_; lean_object* v___y_6789_; uint8_t v___y_6790_; lean_object* v___y_6791_; lean_object* v___y_6792_; lean_object* v___y_6793_; lean_object* v___y_6794_; lean_object* v___y_6823_; uint8_t v___y_6824_; uint8_t v___y_6825_; lean_object* v___y_6826_; lean_object* v___y_6827_; lean_object* v___y_6828_; uint8_t v___y_6829_; lean_object* v___y_6830_; lean_object* v___y_6848_; uint8_t v___y_6849_; uint8_t v___y_6850_; lean_object* v___y_6851_; lean_object* v___y_6852_; uint8_t v___y_6853_; lean_object* v___y_6854_; lean_object* v___y_6855_; lean_object* v___y_6859_; uint8_t v___y_6860_; uint8_t v___y_6861_; lean_object* v___y_6862_; lean_object* v___y_6863_; lean_object* v___y_6864_; uint8_t v___y_6865_; uint8_t v___x_6870_; lean_object* v___y_6872_; lean_object* v___y_6873_; lean_object* v___y_6874_; uint8_t v___y_6875_; uint8_t v___y_6876_; lean_object* v___y_6877_; uint8_t v___y_6878_; uint8_t v___y_6880_; uint8_t v___x_6896_; 
v___x_6870_ = 2;
v___x_6896_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6780_, v___x_6870_);
if (v___x_6896_ == 0)
{
v___y_6880_ = v___x_6896_;
goto v___jp_6879_;
}
else
{
uint8_t v___x_6897_; 
lean_inc_ref(v_msgData_6779_);
v___x_6897_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6779_);
v___y_6880_ = v___x_6897_;
goto v___jp_6879_;
}
v___jp_6785_:
{
lean_object* v___x_6795_; lean_object* v_toCold_6796_; lean_object* v_currNamespace_6797_; lean_object* v_openDecls_6798_; lean_object* v_env_6799_; lean_object* v_nextMacroScope_6800_; lean_object* v_ngen_6801_; lean_object* v_auxDeclNGen_6802_; lean_object* v_traceState_6803_; lean_object* v_cache_6804_; lean_object* v_messages_6805_; lean_object* v_infoState_6806_; lean_object* v_snapshotTasks_6807_; lean_object* v___x_6809_; uint8_t v_isShared_6810_; uint8_t v_isSharedCheck_6821_; 
v___x_6795_ = lean_st_ref_take(v___y_6794_);
v_toCold_6796_ = lean_ctor_get(v___y_6793_, 0);
v_currNamespace_6797_ = lean_ctor_get(v_toCold_6796_, 4);
v_openDecls_6798_ = lean_ctor_get(v_toCold_6796_, 5);
v_env_6799_ = lean_ctor_get(v___x_6795_, 0);
v_nextMacroScope_6800_ = lean_ctor_get(v___x_6795_, 1);
v_ngen_6801_ = lean_ctor_get(v___x_6795_, 2);
v_auxDeclNGen_6802_ = lean_ctor_get(v___x_6795_, 3);
v_traceState_6803_ = lean_ctor_get(v___x_6795_, 4);
v_cache_6804_ = lean_ctor_get(v___x_6795_, 5);
v_messages_6805_ = lean_ctor_get(v___x_6795_, 6);
v_infoState_6806_ = lean_ctor_get(v___x_6795_, 7);
v_snapshotTasks_6807_ = lean_ctor_get(v___x_6795_, 8);
v_isSharedCheck_6821_ = !lean_is_exclusive(v___x_6795_);
if (v_isSharedCheck_6821_ == 0)
{
v___x_6809_ = v___x_6795_;
v_isShared_6810_ = v_isSharedCheck_6821_;
goto v_resetjp_6808_;
}
else
{
lean_inc(v_snapshotTasks_6807_);
lean_inc(v_infoState_6806_);
lean_inc(v_messages_6805_);
lean_inc(v_cache_6804_);
lean_inc(v_traceState_6803_);
lean_inc(v_auxDeclNGen_6802_);
lean_inc(v_ngen_6801_);
lean_inc(v_nextMacroScope_6800_);
lean_inc(v_env_6799_);
lean_dec(v___x_6795_);
v___x_6809_ = lean_box(0);
v_isShared_6810_ = v_isSharedCheck_6821_;
goto v_resetjp_6808_;
}
v_resetjp_6808_:
{
lean_object* v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6816_; 
lean_inc(v_openDecls_6798_);
lean_inc(v_currNamespace_6797_);
v___x_6811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6811_, 0, v_currNamespace_6797_);
lean_ctor_set(v___x_6811_, 1, v_openDecls_6798_);
v___x_6812_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6812_, 0, v___x_6811_);
lean_ctor_set(v___x_6812_, 1, v___y_6787_);
lean_inc_ref(v___y_6789_);
lean_inc_ref(v___y_6791_);
v___x_6813_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6813_, 0, v___y_6791_);
lean_ctor_set(v___x_6813_, 1, v___y_6792_);
lean_ctor_set(v___x_6813_, 2, v___y_6788_);
lean_ctor_set(v___x_6813_, 3, v___y_6789_);
lean_ctor_set(v___x_6813_, 4, v___x_6812_);
lean_ctor_set_uint8(v___x_6813_, sizeof(void*)*5, v___y_6786_);
lean_ctor_set_uint8(v___x_6813_, sizeof(void*)*5 + 1, v___y_6790_);
lean_ctor_set_uint8(v___x_6813_, sizeof(void*)*5 + 2, v_isSilent_6781_);
v___x_6814_ = l_Lean_MessageLog_add(v___x_6813_, v_messages_6805_);
if (v_isShared_6810_ == 0)
{
lean_ctor_set(v___x_6809_, 6, v___x_6814_);
v___x_6816_ = v___x_6809_;
goto v_reusejp_6815_;
}
else
{
lean_object* v_reuseFailAlloc_6820_; 
v_reuseFailAlloc_6820_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6820_, 0, v_env_6799_);
lean_ctor_set(v_reuseFailAlloc_6820_, 1, v_nextMacroScope_6800_);
lean_ctor_set(v_reuseFailAlloc_6820_, 2, v_ngen_6801_);
lean_ctor_set(v_reuseFailAlloc_6820_, 3, v_auxDeclNGen_6802_);
lean_ctor_set(v_reuseFailAlloc_6820_, 4, v_traceState_6803_);
lean_ctor_set(v_reuseFailAlloc_6820_, 5, v_cache_6804_);
lean_ctor_set(v_reuseFailAlloc_6820_, 6, v___x_6814_);
lean_ctor_set(v_reuseFailAlloc_6820_, 7, v_infoState_6806_);
lean_ctor_set(v_reuseFailAlloc_6820_, 8, v_snapshotTasks_6807_);
v___x_6816_ = v_reuseFailAlloc_6820_;
goto v_reusejp_6815_;
}
v_reusejp_6815_:
{
lean_object* v___x_6817_; lean_object* v___x_6818_; lean_object* v___x_6819_; 
v___x_6817_ = lean_st_ref_put(v___y_6794_, v___x_6816_);
v___x_6818_ = lean_box(0);
v___x_6819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6819_, 0, v___x_6818_);
return v___x_6819_;
}
}
}
v___jp_6822_:
{
lean_object* v___x_6831_; lean_object* v___x_6832_; lean_object* v_a_6833_; lean_object* v___x_6835_; uint8_t v_isShared_6836_; uint8_t v_isSharedCheck_6846_; 
v___x_6831_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6779_);
v___x_6832_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6831_, v___y_6782_, v___y_6783_);
v_a_6833_ = lean_ctor_get(v___x_6832_, 0);
v_isSharedCheck_6846_ = !lean_is_exclusive(v___x_6832_);
if (v_isSharedCheck_6846_ == 0)
{
v___x_6835_ = v___x_6832_;
v_isShared_6836_ = v_isSharedCheck_6846_;
goto v_resetjp_6834_;
}
else
{
lean_inc(v_a_6833_);
lean_dec(v___x_6832_);
v___x_6835_ = lean_box(0);
v_isShared_6836_ = v_isSharedCheck_6846_;
goto v_resetjp_6834_;
}
v_resetjp_6834_:
{
lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; 
lean_inc_ref_n(v___y_6827_, 2);
v___x_6837_ = l_Lean_FileMap_toPosition(v___y_6827_, v___y_6826_);
lean_dec(v___y_6826_);
v___x_6838_ = l_Lean_FileMap_toPosition(v___y_6827_, v___y_6830_);
lean_dec(v___y_6830_);
v___x_6839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6839_, 0, v___x_6838_);
v___x_6840_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6825_ == 0)
{
lean_del_object(v___x_6835_);
lean_dec_ref(v___y_6823_);
v___y_6786_ = v___y_6824_;
v___y_6787_ = v_a_6833_;
v___y_6788_ = v___x_6839_;
v___y_6789_ = v___x_6840_;
v___y_6790_ = v___y_6829_;
v___y_6791_ = v___y_6828_;
v___y_6792_ = v___x_6837_;
v___y_6793_ = v___y_6782_;
v___y_6794_ = v___y_6783_;
goto v___jp_6785_;
}
else
{
uint8_t v___x_6841_; 
lean_inc(v_a_6833_);
v___x_6841_ = l_Lean_MessageData_hasTag(v___y_6823_, v_a_6833_);
if (v___x_6841_ == 0)
{
lean_object* v___x_6842_; lean_object* v___x_6844_; 
lean_dec_ref_known(v___x_6839_, 1);
lean_dec_ref(v___x_6837_);
lean_dec(v_a_6833_);
v___x_6842_ = lean_box(0);
if (v_isShared_6836_ == 0)
{
lean_ctor_set(v___x_6835_, 0, v___x_6842_);
v___x_6844_ = v___x_6835_;
goto v_reusejp_6843_;
}
else
{
lean_object* v_reuseFailAlloc_6845_; 
v_reuseFailAlloc_6845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6845_, 0, v___x_6842_);
v___x_6844_ = v_reuseFailAlloc_6845_;
goto v_reusejp_6843_;
}
v_reusejp_6843_:
{
return v___x_6844_;
}
}
else
{
lean_del_object(v___x_6835_);
v___y_6786_ = v___y_6824_;
v___y_6787_ = v_a_6833_;
v___y_6788_ = v___x_6839_;
v___y_6789_ = v___x_6840_;
v___y_6790_ = v___y_6829_;
v___y_6791_ = v___y_6828_;
v___y_6792_ = v___x_6837_;
v___y_6793_ = v___y_6782_;
v___y_6794_ = v___y_6783_;
goto v___jp_6785_;
}
}
}
}
v___jp_6847_:
{
lean_object* v___x_6856_; 
v___x_6856_ = l_Lean_Syntax_getTailPos_x3f(v___y_6851_, v___y_6849_);
lean_dec(v___y_6851_);
if (lean_obj_tag(v___x_6856_) == 0)
{
lean_inc(v___y_6855_);
v___y_6823_ = v___y_6848_;
v___y_6824_ = v___y_6849_;
v___y_6825_ = v___y_6850_;
v___y_6826_ = v___y_6855_;
v___y_6827_ = v___y_6852_;
v___y_6828_ = v___y_6854_;
v___y_6829_ = v___y_6853_;
v___y_6830_ = v___y_6855_;
goto v___jp_6822_;
}
else
{
lean_object* v_val_6857_; 
v_val_6857_ = lean_ctor_get(v___x_6856_, 0);
lean_inc(v_val_6857_);
lean_dec_ref_known(v___x_6856_, 1);
v___y_6823_ = v___y_6848_;
v___y_6824_ = v___y_6849_;
v___y_6825_ = v___y_6850_;
v___y_6826_ = v___y_6855_;
v___y_6827_ = v___y_6852_;
v___y_6828_ = v___y_6854_;
v___y_6829_ = v___y_6853_;
v___y_6830_ = v_val_6857_;
goto v___jp_6822_;
}
}
v___jp_6858_:
{
lean_object* v_ref_6866_; lean_object* v___x_6867_; 
v_ref_6866_ = l_Lean_replaceRef(v_ref_6778_, v___y_6863_);
v___x_6867_ = l_Lean_Syntax_getPos_x3f(v_ref_6866_, v___y_6860_);
if (lean_obj_tag(v___x_6867_) == 0)
{
lean_object* v___x_6868_; 
v___x_6868_ = lean_unsigned_to_nat(0u);
v___y_6848_ = v___y_6859_;
v___y_6849_ = v___y_6860_;
v___y_6850_ = v___y_6861_;
v___y_6851_ = v_ref_6866_;
v___y_6852_ = v___y_6862_;
v___y_6853_ = v___y_6865_;
v___y_6854_ = v___y_6864_;
v___y_6855_ = v___x_6868_;
goto v___jp_6847_;
}
else
{
lean_object* v_val_6869_; 
v_val_6869_ = lean_ctor_get(v___x_6867_, 0);
lean_inc(v_val_6869_);
lean_dec_ref_known(v___x_6867_, 1);
v___y_6848_ = v___y_6859_;
v___y_6849_ = v___y_6860_;
v___y_6850_ = v___y_6861_;
v___y_6851_ = v_ref_6866_;
v___y_6852_ = v___y_6862_;
v___y_6853_ = v___y_6865_;
v___y_6854_ = v___y_6864_;
v___y_6855_ = v_val_6869_;
goto v___jp_6847_;
}
}
v___jp_6871_:
{
if (v___y_6878_ == 0)
{
v___y_6859_ = v___y_6874_;
v___y_6860_ = v___y_6875_;
v___y_6861_ = v___y_6876_;
v___y_6862_ = v___y_6872_;
v___y_6863_ = v___y_6877_;
v___y_6864_ = v___y_6873_;
v___y_6865_ = v_severity_6780_;
goto v___jp_6858_;
}
else
{
v___y_6859_ = v___y_6874_;
v___y_6860_ = v___y_6875_;
v___y_6861_ = v___y_6876_;
v___y_6862_ = v___y_6872_;
v___y_6863_ = v___y_6877_;
v___y_6864_ = v___y_6873_;
v___y_6865_ = v___x_6870_;
goto v___jp_6858_;
}
}
v___jp_6879_:
{
if (v___y_6880_ == 0)
{
lean_object* v_toCold_6881_; lean_object* v_ref_6882_; uint8_t v_suppressElabErrors_6883_; lean_object* v_fileName_6884_; lean_object* v_fileMap_6885_; lean_object* v_options_6886_; lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___f_6889_; uint8_t v___x_6890_; uint8_t v___x_6891_; 
v_toCold_6881_ = lean_ctor_get(v___y_6782_, 0);
v_ref_6882_ = lean_ctor_get(v___y_6782_, 2);
v_suppressElabErrors_6883_ = lean_ctor_get_uint8(v___y_6782_, sizeof(void*)*3 + 1);
v_fileName_6884_ = lean_ctor_get(v_toCold_6881_, 0);
v_fileMap_6885_ = lean_ctor_get(v_toCold_6881_, 1);
v_options_6886_ = lean_ctor_get(v_toCold_6881_, 2);
v___x_6887_ = lean_box(v_suppressElabErrors_6883_);
v___x_6888_ = lean_box(v___y_6880_);
v___f_6889_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6889_, 0, v___x_6887_);
lean_closure_set(v___f_6889_, 1, v___x_6888_);
v___x_6890_ = 1;
v___x_6891_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6780_, v___x_6890_);
if (v___x_6891_ == 0)
{
v___y_6872_ = v_fileMap_6885_;
v___y_6873_ = v_fileName_6884_;
v___y_6874_ = v___f_6889_;
v___y_6875_ = v___y_6880_;
v___y_6876_ = v_suppressElabErrors_6883_;
v___y_6877_ = v_ref_6882_;
v___y_6878_ = v___x_6891_;
goto v___jp_6871_;
}
else
{
lean_object* v___x_6892_; uint8_t v___x_6893_; 
v___x_6892_ = l_Lean_warningAsError;
v___x_6893_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6886_, v___x_6892_);
v___y_6872_ = v_fileMap_6885_;
v___y_6873_ = v_fileName_6884_;
v___y_6874_ = v___f_6889_;
v___y_6875_ = v___y_6880_;
v___y_6876_ = v_suppressElabErrors_6883_;
v___y_6877_ = v_ref_6882_;
v___y_6878_ = v___x_6893_;
goto v___jp_6871_;
}
}
else
{
lean_object* v___x_6894_; lean_object* v___x_6895_; 
lean_dec_ref(v_msgData_6779_);
v___x_6894_ = lean_box(0);
v___x_6895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6895_, 0, v___x_6894_);
return v___x_6895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6898_, lean_object* v_msgData_6899_, lean_object* v_severity_6900_, lean_object* v_isSilent_6901_, lean_object* v___y_6902_, lean_object* v___y_6903_, lean_object* v___y_6904_){
_start:
{
uint8_t v_severity_boxed_6905_; uint8_t v_isSilent_boxed_6906_; lean_object* v_res_6907_; 
v_severity_boxed_6905_ = lean_unbox(v_severity_6900_);
v_isSilent_boxed_6906_ = lean_unbox(v_isSilent_6901_);
v_res_6907_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6898_, v_msgData_6899_, v_severity_boxed_6905_, v_isSilent_boxed_6906_, v___y_6902_, v___y_6903_);
lean_dec(v___y_6903_);
lean_dec_ref(v___y_6902_);
lean_dec(v_ref_6898_);
return v_res_6907_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6908_, uint8_t v_severity_6909_, uint8_t v_isSilent_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_){
_start:
{
lean_object* v_ref_6914_; lean_object* v___x_6915_; 
v_ref_6914_ = lean_ctor_get(v___y_6911_, 2);
v___x_6915_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6914_, v_msgData_6908_, v_severity_6909_, v_isSilent_6910_, v___y_6911_, v___y_6912_);
return v___x_6915_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6916_, lean_object* v_severity_6917_, lean_object* v_isSilent_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_){
_start:
{
uint8_t v_severity_boxed_6922_; uint8_t v_isSilent_boxed_6923_; lean_object* v_res_6924_; 
v_severity_boxed_6922_ = lean_unbox(v_severity_6917_);
v_isSilent_boxed_6923_ = lean_unbox(v_isSilent_6918_);
v_res_6924_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6916_, v_severity_boxed_6922_, v_isSilent_boxed_6923_, v___y_6919_, v___y_6920_);
lean_dec(v___y_6920_);
lean_dec_ref(v___y_6919_);
return v_res_6924_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6925_, lean_object* v___y_6926_, lean_object* v___y_6927_){
_start:
{
uint8_t v___x_6929_; uint8_t v___x_6930_; lean_object* v___x_6931_; 
v___x_6929_ = 2;
v___x_6930_ = 0;
v___x_6931_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6925_, v___x_6929_, v___x_6930_, v___y_6926_, v___y_6927_);
return v___x_6931_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_){
_start:
{
lean_object* v_res_6936_; 
v_res_6936_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6932_, v___y_6933_, v___y_6934_);
lean_dec(v___y_6934_);
lean_dec_ref(v___y_6933_);
return v_res_6936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6937_, lean_object* v___y_6938_, lean_object* v___y_6939_){
_start:
{
lean_object* v_module_6941_; lean_object* v_const_6942_; lean_object* v_exception_6943_; lean_object* v___x_6944_; lean_object* v___x_6945_; lean_object* v___x_6946_; lean_object* v___x_6947_; lean_object* v___x_6948_; lean_object* v___x_6949_; lean_object* v___x_6950_; lean_object* v___x_6951_; lean_object* v___x_6952_; lean_object* v___x_6953_; lean_object* v___x_6954_; lean_object* v___x_6955_; 
v_module_6941_ = lean_ctor_get(v_f_6937_, 0);
lean_inc(v_module_6941_);
v_const_6942_ = lean_ctor_get(v_f_6937_, 1);
lean_inc(v_const_6942_);
v_exception_6943_ = lean_ctor_get(v_f_6937_, 2);
lean_inc_ref(v_exception_6943_);
lean_dec_ref(v_f_6937_);
v___x_6944_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6945_ = l_Lean_MessageData_ofName(v_const_6942_);
v___x_6946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6946_, 0, v___x_6944_);
lean_ctor_set(v___x_6946_, 1, v___x_6945_);
v___x_6947_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6948_, 0, v___x_6946_);
lean_ctor_set(v___x_6948_, 1, v___x_6947_);
v___x_6949_ = l_Lean_MessageData_ofName(v_module_6941_);
v___x_6950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6950_, 0, v___x_6948_);
lean_ctor_set(v___x_6950_, 1, v___x_6949_);
v___x_6951_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6952_, 0, v___x_6950_);
lean_ctor_set(v___x_6952_, 1, v___x_6951_);
v___x_6953_ = l_Lean_Exception_toMessageData(v_exception_6943_);
v___x_6954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6954_, 0, v___x_6952_);
lean_ctor_set(v___x_6954_, 1, v___x_6953_);
v___x_6955_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6954_, v___y_6938_, v___y_6939_);
return v___x_6955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_, lean_object* v___y_6959_){
_start:
{
lean_object* v_res_6960_; 
v_res_6960_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6956_, v___y_6957_, v___y_6958_);
lean_dec(v___y_6958_);
lean_dec_ref(v___y_6957_);
return v_res_6960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_6961_, size_t v_i_6962_, size_t v_stop_6963_, lean_object* v_b_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_){
_start:
{
uint8_t v___x_6968_; 
v___x_6968_ = lean_usize_dec_eq(v_i_6962_, v_stop_6963_);
if (v___x_6968_ == 0)
{
lean_object* v___x_6969_; lean_object* v___x_6970_; 
v___x_6969_ = lean_array_uget_borrowed(v_as_6961_, v_i_6962_);
lean_inc(v___x_6969_);
v___x_6970_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_6969_, v___y_6965_, v___y_6966_);
if (lean_obj_tag(v___x_6970_) == 0)
{
lean_object* v_a_6971_; size_t v___x_6972_; size_t v___x_6973_; 
v_a_6971_ = lean_ctor_get(v___x_6970_, 0);
lean_inc(v_a_6971_);
lean_dec_ref_known(v___x_6970_, 1);
v___x_6972_ = ((size_t)1ULL);
v___x_6973_ = lean_usize_add(v_i_6962_, v___x_6972_);
v_i_6962_ = v___x_6973_;
v_b_6964_ = v_a_6971_;
goto _start;
}
else
{
return v___x_6970_;
}
}
else
{
lean_object* v___x_6975_; 
v___x_6975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6975_, 0, v_b_6964_);
return v___x_6975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_6976_, lean_object* v_i_6977_, lean_object* v_stop_6978_, lean_object* v_b_6979_, lean_object* v___y_6980_, lean_object* v___y_6981_, lean_object* v___y_6982_){
_start:
{
size_t v_i_boxed_6983_; size_t v_stop_boxed_6984_; lean_object* v_res_6985_; 
v_i_boxed_6983_ = lean_unbox_usize(v_i_6977_);
lean_dec(v_i_6977_);
v_stop_boxed_6984_ = lean_unbox_usize(v_stop_6978_);
lean_dec(v_stop_6978_);
v_res_6985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_6976_, v_i_boxed_6983_, v_stop_boxed_6984_, v_b_6979_, v___y_6980_, v___y_6981_);
lean_dec(v___y_6981_);
lean_dec_ref(v___y_6980_);
lean_dec_ref(v_as_6976_);
return v_res_6985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_6986_, lean_object* v_a_6987_, lean_object* v_a_6988_){
_start:
{
lean_object* v___x_6990_; lean_object* v___x_6991_; lean_object* v_a_6992_; lean_object* v___x_6994_; uint8_t v_isShared_6995_; uint8_t v_isSharedCheck_7026_; 
v___x_6990_ = lean_st_ref_get(v_a_6988_);
v___x_6991_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_6988_);
v_a_6992_ = lean_ctor_get(v___x_6991_, 0);
v_isSharedCheck_7026_ = !lean_is_exclusive(v___x_6991_);
if (v_isSharedCheck_7026_ == 0)
{
v___x_6994_ = v___x_6991_;
v_isShared_6995_ = v_isSharedCheck_7026_;
goto v_resetjp_6993_;
}
else
{
lean_inc(v_a_6992_);
lean_dec(v___x_6991_);
v___x_6994_ = lean_box(0);
v_isShared_6995_ = v_isSharedCheck_7026_;
goto v_resetjp_6993_;
}
v_resetjp_6993_:
{
lean_object* v___x_6996_; lean_object* v_env_6997_; lean_object* v___x_6998_; lean_object* v___y_7005_; lean_object* v___x_7014_; lean_object* v___x_7015_; lean_object* v___x_7016_; uint8_t v___x_7017_; 
v___x_6996_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_6997_ = lean_ctor_get(v___x_6990_, 0);
lean_inc_ref(v_env_6997_);
lean_dec(v___x_6990_);
lean_inc_ref(v_a_6987_);
v___x_6998_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_6987_, v_a_6992_, v_env_6997_, v___x_6996_, v_entriesForConst_6986_);
v___x_7014_ = lean_st_ref_get(v___x_6996_);
lean_dec(v___x_6996_);
v___x_7015_ = lean_unsigned_to_nat(0u);
v___x_7016_ = lean_array_get_size(v___x_7014_);
v___x_7017_ = lean_nat_dec_lt(v___x_7015_, v___x_7016_);
if (v___x_7017_ == 0)
{
lean_dec(v___x_7014_);
goto v___jp_6999_;
}
else
{
lean_object* v___x_7018_; uint8_t v___x_7019_; 
v___x_7018_ = lean_box(0);
v___x_7019_ = lean_nat_dec_le(v___x_7016_, v___x_7016_);
if (v___x_7019_ == 0)
{
if (v___x_7017_ == 0)
{
lean_dec(v___x_7014_);
goto v___jp_6999_;
}
else
{
size_t v___x_7020_; size_t v___x_7021_; lean_object* v___x_7022_; 
v___x_7020_ = ((size_t)0ULL);
v___x_7021_ = lean_usize_of_nat(v___x_7016_);
v___x_7022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7014_, v___x_7020_, v___x_7021_, v___x_7018_, v_a_6987_, v_a_6988_);
lean_dec(v___x_7014_);
v___y_7005_ = v___x_7022_;
goto v___jp_7004_;
}
}
else
{
size_t v___x_7023_; size_t v___x_7024_; lean_object* v___x_7025_; 
v___x_7023_ = ((size_t)0ULL);
v___x_7024_ = lean_usize_of_nat(v___x_7016_);
v___x_7025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7014_, v___x_7023_, v___x_7024_, v___x_7018_, v_a_6987_, v_a_6988_);
lean_dec(v___x_7014_);
v___y_7005_ = v___x_7025_;
goto v___jp_7004_;
}
}
v___jp_6999_:
{
lean_object* v___x_7000_; lean_object* v___x_7002_; 
v___x_7000_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_6998_);
if (v_isShared_6995_ == 0)
{
lean_ctor_set(v___x_6994_, 0, v___x_7000_);
v___x_7002_ = v___x_6994_;
goto v_reusejp_7001_;
}
else
{
lean_object* v_reuseFailAlloc_7003_; 
v_reuseFailAlloc_7003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7003_, 0, v___x_7000_);
v___x_7002_ = v_reuseFailAlloc_7003_;
goto v_reusejp_7001_;
}
v_reusejp_7001_:
{
return v___x_7002_;
}
}
v___jp_7004_:
{
if (lean_obj_tag(v___y_7005_) == 0)
{
lean_dec_ref_known(v___y_7005_, 1);
goto v___jp_6999_;
}
else
{
lean_object* v_a_7006_; lean_object* v___x_7008_; uint8_t v_isShared_7009_; uint8_t v_isSharedCheck_7013_; 
lean_dec_ref(v___x_6998_);
lean_del_object(v___x_6994_);
v_a_7006_ = lean_ctor_get(v___y_7005_, 0);
v_isSharedCheck_7013_ = !lean_is_exclusive(v___y_7005_);
if (v_isSharedCheck_7013_ == 0)
{
v___x_7008_ = v___y_7005_;
v_isShared_7009_ = v_isSharedCheck_7013_;
goto v_resetjp_7007_;
}
else
{
lean_inc(v_a_7006_);
lean_dec(v___y_7005_);
v___x_7008_ = lean_box(0);
v_isShared_7009_ = v_isSharedCheck_7013_;
goto v_resetjp_7007_;
}
v_resetjp_7007_:
{
lean_object* v___x_7011_; 
if (v_isShared_7009_ == 0)
{
v___x_7011_ = v___x_7008_;
goto v_reusejp_7010_;
}
else
{
lean_object* v_reuseFailAlloc_7012_; 
v_reuseFailAlloc_7012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7012_, 0, v_a_7006_);
v___x_7011_ = v_reuseFailAlloc_7012_;
goto v_reusejp_7010_;
}
v_reusejp_7010_:
{
return v___x_7011_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7027_, lean_object* v_a_7028_, lean_object* v_a_7029_, lean_object* v_a_7030_){
_start:
{
lean_object* v_res_7031_; 
v_res_7031_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7027_, v_a_7028_, v_a_7029_);
lean_dec(v_a_7029_);
lean_dec_ref(v_a_7028_);
return v_res_7031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7032_, lean_object* v_entriesForConst_7033_, lean_object* v_a_7034_, lean_object* v_a_7035_){
_start:
{
lean_object* v___x_7037_; 
v___x_7037_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7033_, v_a_7034_, v_a_7035_);
return v___x_7037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7038_, lean_object* v_entriesForConst_7039_, lean_object* v_a_7040_, lean_object* v_a_7041_, lean_object* v_a_7042_){
_start:
{
lean_object* v_res_7043_; 
v_res_7043_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7038_, v_entriesForConst_7039_, v_a_7040_, v_a_7041_);
lean_dec(v_a_7041_);
lean_dec_ref(v_a_7040_);
return v_res_7043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7044_, lean_object* v_droppedEntriesRef_7045_, lean_object* v_droppedKeys_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_){
_start:
{
lean_object* v_t_7053_; lean_object* v___x_7056_; 
v___x_7056_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7044_, v___y_7049_, v___y_7050_);
if (lean_obj_tag(v___x_7056_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7045_) == 1)
{
lean_object* v_a_7057_; lean_object* v_val_7058_; lean_object* v___x_7060_; uint8_t v_isShared_7061_; uint8_t v_isSharedCheck_7084_; 
v_a_7057_ = lean_ctor_get(v___x_7056_, 0);
lean_inc(v_a_7057_);
lean_dec_ref_known(v___x_7056_, 1);
v_val_7058_ = lean_ctor_get(v_droppedEntriesRef_7045_, 0);
v_isSharedCheck_7084_ = !lean_is_exclusive(v_droppedEntriesRef_7045_);
if (v_isSharedCheck_7084_ == 0)
{
v___x_7060_ = v_droppedEntriesRef_7045_;
v_isShared_7061_ = v_isSharedCheck_7084_;
goto v_resetjp_7059_;
}
else
{
lean_inc(v_val_7058_);
lean_dec(v_droppedEntriesRef_7045_);
v___x_7060_ = lean_box(0);
v_isShared_7061_ = v_isSharedCheck_7084_;
goto v_resetjp_7059_;
}
v_resetjp_7059_:
{
lean_object* v___x_7062_; 
v___x_7062_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7057_, v_droppedKeys_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_);
lean_dec(v_droppedKeys_7046_);
if (lean_obj_tag(v___x_7062_) == 0)
{
lean_object* v_a_7063_; lean_object* v_fst_7064_; lean_object* v_snd_7065_; lean_object* v___x_7066_; lean_object* v___y_7068_; 
v_a_7063_ = lean_ctor_get(v___x_7062_, 0);
lean_inc(v_a_7063_);
lean_dec_ref_known(v___x_7062_, 1);
v_fst_7064_ = lean_ctor_get(v_a_7063_, 0);
lean_inc(v_fst_7064_);
v_snd_7065_ = lean_ctor_get(v_a_7063_, 1);
lean_inc(v_snd_7065_);
lean_dec(v_a_7063_);
v___x_7066_ = lean_st_ref_get(v_val_7058_);
if (lean_obj_tag(v___x_7066_) == 0)
{
lean_object* v___x_7074_; 
v___x_7074_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7068_ = v___x_7074_;
goto v___jp_7067_;
}
else
{
lean_object* v_val_7075_; 
v_val_7075_ = lean_ctor_get(v___x_7066_, 0);
lean_inc(v_val_7075_);
lean_dec_ref_known(v___x_7066_, 1);
v___y_7068_ = v_val_7075_;
goto v___jp_7067_;
}
v___jp_7067_:
{
lean_object* v___x_7069_; lean_object* v___x_7071_; 
v___x_7069_ = l_Array_append___redArg(v___y_7068_, v_fst_7064_);
lean_dec(v_fst_7064_);
if (v_isShared_7061_ == 0)
{
lean_ctor_set(v___x_7060_, 0, v___x_7069_);
v___x_7071_ = v___x_7060_;
goto v_reusejp_7070_;
}
else
{
lean_object* v_reuseFailAlloc_7073_; 
v_reuseFailAlloc_7073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7073_, 0, v___x_7069_);
v___x_7071_ = v_reuseFailAlloc_7073_;
goto v_reusejp_7070_;
}
v_reusejp_7070_:
{
lean_object* v___x_7072_; 
v___x_7072_ = lean_st_ref_swap(v_val_7058_, v___x_7071_);
lean_dec(v_val_7058_);
lean_dec(v___x_7072_);
v_t_7053_ = v_snd_7065_;
goto v___jp_7052_;
}
}
}
else
{
lean_object* v_a_7076_; lean_object* v___x_7078_; uint8_t v_isShared_7079_; uint8_t v_isSharedCheck_7083_; 
lean_del_object(v___x_7060_);
lean_dec(v_val_7058_);
v_a_7076_ = lean_ctor_get(v___x_7062_, 0);
v_isSharedCheck_7083_ = !lean_is_exclusive(v___x_7062_);
if (v_isSharedCheck_7083_ == 0)
{
v___x_7078_ = v___x_7062_;
v_isShared_7079_ = v_isSharedCheck_7083_;
goto v_resetjp_7077_;
}
else
{
lean_inc(v_a_7076_);
lean_dec(v___x_7062_);
v___x_7078_ = lean_box(0);
v_isShared_7079_ = v_isSharedCheck_7083_;
goto v_resetjp_7077_;
}
v_resetjp_7077_:
{
lean_object* v___x_7081_; 
if (v_isShared_7079_ == 0)
{
v___x_7081_ = v___x_7078_;
goto v_reusejp_7080_;
}
else
{
lean_object* v_reuseFailAlloc_7082_; 
v_reuseFailAlloc_7082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_a_7076_);
v___x_7081_ = v_reuseFailAlloc_7082_;
goto v_reusejp_7080_;
}
v_reusejp_7080_:
{
return v___x_7081_;
}
}
}
}
}
else
{
lean_object* v_a_7085_; lean_object* v___x_7086_; 
lean_dec(v_droppedEntriesRef_7045_);
v_a_7085_ = lean_ctor_get(v___x_7056_, 0);
lean_inc(v_a_7085_);
lean_dec_ref_known(v___x_7056_, 1);
v___x_7086_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7085_, v_droppedKeys_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_);
if (lean_obj_tag(v___x_7086_) == 0)
{
lean_object* v_a_7087_; 
v_a_7087_ = lean_ctor_get(v___x_7086_, 0);
lean_inc(v_a_7087_);
lean_dec_ref_known(v___x_7086_, 1);
v_t_7053_ = v_a_7087_;
goto v___jp_7052_;
}
else
{
lean_object* v_a_7088_; lean_object* v___x_7090_; uint8_t v_isShared_7091_; uint8_t v_isSharedCheck_7095_; 
v_a_7088_ = lean_ctor_get(v___x_7086_, 0);
v_isSharedCheck_7095_ = !lean_is_exclusive(v___x_7086_);
if (v_isSharedCheck_7095_ == 0)
{
v___x_7090_ = v___x_7086_;
v_isShared_7091_ = v_isSharedCheck_7095_;
goto v_resetjp_7089_;
}
else
{
lean_inc(v_a_7088_);
lean_dec(v___x_7086_);
v___x_7090_ = lean_box(0);
v_isShared_7091_ = v_isSharedCheck_7095_;
goto v_resetjp_7089_;
}
v_resetjp_7089_:
{
lean_object* v___x_7093_; 
if (v_isShared_7091_ == 0)
{
v___x_7093_ = v___x_7090_;
goto v_reusejp_7092_;
}
else
{
lean_object* v_reuseFailAlloc_7094_; 
v_reuseFailAlloc_7094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7094_, 0, v_a_7088_);
v___x_7093_ = v_reuseFailAlloc_7094_;
goto v_reusejp_7092_;
}
v_reusejp_7092_:
{
return v___x_7093_;
}
}
}
}
}
else
{
lean_object* v_a_7096_; lean_object* v___x_7098_; uint8_t v_isShared_7099_; uint8_t v_isSharedCheck_7103_; 
lean_dec(v_droppedKeys_7046_);
lean_dec(v_droppedEntriesRef_7045_);
v_a_7096_ = lean_ctor_get(v___x_7056_, 0);
v_isSharedCheck_7103_ = !lean_is_exclusive(v___x_7056_);
if (v_isSharedCheck_7103_ == 0)
{
v___x_7098_ = v___x_7056_;
v_isShared_7099_ = v_isSharedCheck_7103_;
goto v_resetjp_7097_;
}
else
{
lean_inc(v_a_7096_);
lean_dec(v___x_7056_);
v___x_7098_ = lean_box(0);
v_isShared_7099_ = v_isSharedCheck_7103_;
goto v_resetjp_7097_;
}
v_resetjp_7097_:
{
lean_object* v___x_7101_; 
if (v_isShared_7099_ == 0)
{
v___x_7101_ = v___x_7098_;
goto v_reusejp_7100_;
}
else
{
lean_object* v_reuseFailAlloc_7102_; 
v_reuseFailAlloc_7102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7102_, 0, v_a_7096_);
v___x_7101_ = v_reuseFailAlloc_7102_;
goto v_reusejp_7100_;
}
v_reusejp_7100_:
{
return v___x_7101_;
}
}
}
v___jp_7052_:
{
lean_object* v___x_7054_; lean_object* v___x_7055_; 
v___x_7054_ = lean_st_mk_ref(v_t_7053_);
v___x_7055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7055_, 0, v___x_7054_);
return v___x_7055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7104_, lean_object* v_droppedEntriesRef_7105_, lean_object* v_droppedKeys_7106_, lean_object* v___y_7107_, lean_object* v___y_7108_, lean_object* v___y_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_){
_start:
{
lean_object* v_res_7112_; 
v_res_7112_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7104_, v_droppedEntriesRef_7105_, v_droppedKeys_7106_, v___y_7107_, v___y_7108_, v___y_7109_, v___y_7110_);
lean_dec(v___y_7110_);
lean_dec_ref(v___y_7109_);
lean_dec(v___y_7108_);
lean_dec_ref(v___y_7107_);
return v_res_7112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7114_, lean_object* v_droppedKeys_7115_, lean_object* v_droppedEntriesRef_7116_, lean_object* v_a_7117_, lean_object* v_a_7118_, lean_object* v_a_7119_, lean_object* v_a_7120_){
_start:
{
lean_object* v_toCold_7122_; lean_object* v_options_7123_; lean_object* v___f_7124_; lean_object* v___x_7125_; lean_object* v___x_7126_; lean_object* v___x_7127_; 
v_toCold_7122_ = lean_ctor_get(v_a_7119_, 0);
v_options_7123_ = lean_ctor_get(v_toCold_7122_, 2);
v___f_7124_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7124_, 0, v_entriesForConst_7114_);
lean_closure_set(v___f_7124_, 1, v_droppedEntriesRef_7116_);
lean_closure_set(v___f_7124_, 2, v_droppedKeys_7115_);
v___x_7125_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7126_ = lean_box(0);
v___x_7127_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7125_, v_options_7123_, v___f_7124_, v___x_7126_, v_a_7117_, v_a_7118_, v_a_7119_, v_a_7120_);
return v___x_7127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7128_, lean_object* v_droppedKeys_7129_, lean_object* v_droppedEntriesRef_7130_, lean_object* v_a_7131_, lean_object* v_a_7132_, lean_object* v_a_7133_, lean_object* v_a_7134_, lean_object* v_a_7135_){
_start:
{
lean_object* v_res_7136_; 
v_res_7136_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7128_, v_droppedKeys_7129_, v_droppedEntriesRef_7130_, v_a_7131_, v_a_7132_, v_a_7133_, v_a_7134_);
lean_dec(v_a_7134_);
lean_dec_ref(v_a_7133_);
lean_dec(v_a_7132_);
lean_dec_ref(v_a_7131_);
return v_res_7136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7137_, lean_object* v_entriesForConst_7138_, lean_object* v_droppedKeys_7139_, lean_object* v_droppedEntriesRef_7140_, lean_object* v_a_7141_, lean_object* v_a_7142_, lean_object* v_a_7143_, lean_object* v_a_7144_){
_start:
{
lean_object* v___x_7146_; 
v___x_7146_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7138_, v_droppedKeys_7139_, v_droppedEntriesRef_7140_, v_a_7141_, v_a_7142_, v_a_7143_, v_a_7144_);
return v___x_7146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7147_, lean_object* v_entriesForConst_7148_, lean_object* v_droppedKeys_7149_, lean_object* v_droppedEntriesRef_7150_, lean_object* v_a_7151_, lean_object* v_a_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_, lean_object* v_a_7155_){
_start:
{
lean_object* v_res_7156_; 
v_res_7156_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7147_, v_entriesForConst_7148_, v_droppedKeys_7149_, v_droppedEntriesRef_7150_, v_a_7151_, v_a_7152_, v_a_7153_, v_a_7154_);
lean_dec(v_a_7154_);
lean_dec_ref(v_a_7153_);
lean_dec(v_a_7152_);
lean_dec_ref(v_a_7151_);
return v_res_7156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7157_, lean_object* v_ty_7158_, lean_object* v___y_7159_, lean_object* v___y_7160_, lean_object* v___y_7161_, lean_object* v___y_7162_){
_start:
{
lean_object* v___x_7164_; lean_object* v___x_7165_; 
v___x_7164_ = lean_st_ref_get(v_moduleRef_7157_);
v___x_7165_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7164_, v_ty_7158_, v___y_7159_, v___y_7160_, v___y_7161_, v___y_7162_);
if (lean_obj_tag(v___x_7165_) == 0)
{
lean_object* v_a_7166_; lean_object* v___x_7168_; uint8_t v_isShared_7169_; uint8_t v_isSharedCheck_7176_; 
v_a_7166_ = lean_ctor_get(v___x_7165_, 0);
v_isSharedCheck_7176_ = !lean_is_exclusive(v___x_7165_);
if (v_isSharedCheck_7176_ == 0)
{
v___x_7168_ = v___x_7165_;
v_isShared_7169_ = v_isSharedCheck_7176_;
goto v_resetjp_7167_;
}
else
{
lean_inc(v_a_7166_);
lean_dec(v___x_7165_);
v___x_7168_ = lean_box(0);
v_isShared_7169_ = v_isSharedCheck_7176_;
goto v_resetjp_7167_;
}
v_resetjp_7167_:
{
lean_object* v_fst_7170_; lean_object* v_snd_7171_; lean_object* v___x_7172_; lean_object* v___x_7174_; 
v_fst_7170_ = lean_ctor_get(v_a_7166_, 0);
lean_inc(v_fst_7170_);
v_snd_7171_ = lean_ctor_get(v_a_7166_, 1);
lean_inc(v_snd_7171_);
lean_dec(v_a_7166_);
v___x_7172_ = lean_st_ref_swap(v_moduleRef_7157_, v_snd_7171_);
lean_dec(v___x_7172_);
if (v_isShared_7169_ == 0)
{
lean_ctor_set(v___x_7168_, 0, v_fst_7170_);
v___x_7174_ = v___x_7168_;
goto v_reusejp_7173_;
}
else
{
lean_object* v_reuseFailAlloc_7175_; 
v_reuseFailAlloc_7175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7175_, 0, v_fst_7170_);
v___x_7174_ = v_reuseFailAlloc_7175_;
goto v_reusejp_7173_;
}
v_reusejp_7173_:
{
return v___x_7174_;
}
}
}
else
{
lean_object* v_a_7177_; lean_object* v___x_7179_; uint8_t v_isShared_7180_; uint8_t v_isSharedCheck_7184_; 
v_a_7177_ = lean_ctor_get(v___x_7165_, 0);
v_isSharedCheck_7184_ = !lean_is_exclusive(v___x_7165_);
if (v_isSharedCheck_7184_ == 0)
{
v___x_7179_ = v___x_7165_;
v_isShared_7180_ = v_isSharedCheck_7184_;
goto v_resetjp_7178_;
}
else
{
lean_inc(v_a_7177_);
lean_dec(v___x_7165_);
v___x_7179_ = lean_box(0);
v_isShared_7180_ = v_isSharedCheck_7184_;
goto v_resetjp_7178_;
}
v_resetjp_7178_:
{
lean_object* v___x_7182_; 
if (v_isShared_7180_ == 0)
{
v___x_7182_ = v___x_7179_;
goto v_reusejp_7181_;
}
else
{
lean_object* v_reuseFailAlloc_7183_; 
v_reuseFailAlloc_7183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7183_, 0, v_a_7177_);
v___x_7182_ = v_reuseFailAlloc_7183_;
goto v_reusejp_7181_;
}
v_reusejp_7181_:
{
return v___x_7182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7185_, lean_object* v_ty_7186_, lean_object* v___y_7187_, lean_object* v___y_7188_, lean_object* v___y_7189_, lean_object* v___y_7190_, lean_object* v___y_7191_){
_start:
{
lean_object* v_res_7192_; 
v_res_7192_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7185_, v_ty_7186_, v___y_7187_, v___y_7188_, v___y_7189_, v___y_7190_);
lean_dec(v___y_7190_);
lean_dec_ref(v___y_7189_);
lean_dec(v___y_7188_);
lean_dec_ref(v___y_7187_);
lean_dec(v_moduleRef_7185_);
return v_res_7192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7194_, lean_object* v_ty_7195_, lean_object* v_a_7196_, lean_object* v_a_7197_, lean_object* v_a_7198_, lean_object* v_a_7199_){
_start:
{
lean_object* v_toCold_7201_; lean_object* v_options_7202_; lean_object* v___f_7203_; lean_object* v___x_7204_; lean_object* v___x_7205_; lean_object* v___x_7206_; 
v_toCold_7201_ = lean_ctor_get(v_a_7198_, 0);
v_options_7202_ = lean_ctor_get(v_toCold_7201_, 2);
v___f_7203_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7203_, 0, v_moduleRef_7194_);
lean_closure_set(v___f_7203_, 1, v_ty_7195_);
v___x_7204_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7205_ = lean_box(0);
v___x_7206_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7204_, v_options_7202_, v___f_7203_, v___x_7205_, v_a_7196_, v_a_7197_, v_a_7198_, v_a_7199_);
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
size_t v___x_7296_; size_t v___x_7297_; lean_object* v___x_7298_; 
v___x_7296_ = ((size_t)0ULL);
v___x_7297_ = lean_usize_of_nat(v___x_7293_);
lean_inc(v_adjustResult_7281_);
v___x_7298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7281_, v_j_7291_, v_b_7292_, v___x_7296_, v___x_7297_, v_a_7284_);
v_j_7283_ = v_n_7288_;
v_a_7284_ = v___x_7298_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7300_, lean_object* v_aa_7301_, lean_object* v_adjustResult_7302_, lean_object* v_n_7303_, lean_object* v_j_7304_, lean_object* v_a_7305_){
_start:
{
lean_object* v_res_7306_; 
v_res_7306_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7300_, v_aa_7301_, v_adjustResult_7302_, v_n_7303_, v_j_7304_, v_a_7305_);
lean_dec(v_n_7303_);
lean_dec_ref(v_aa_7301_);
lean_dec(v_n_7300_);
return v_res_7306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7307_, lean_object* v_adjustResult_7308_, lean_object* v_aa_7309_, lean_object* v_n_7310_, lean_object* v_j_7311_, lean_object* v_a_7312_){
_start:
{
lean_object* v_zero_7313_; uint8_t v_isZero_7314_; 
v_zero_7313_ = lean_unsigned_to_nat(0u);
v_isZero_7314_ = lean_nat_dec_eq(v_j_7311_, v_zero_7313_);
if (v_isZero_7314_ == 1)
{
lean_dec(v_adjustResult_7308_);
return v_a_7312_;
}
else
{
lean_object* v_one_7315_; lean_object* v_n_7316_; lean_object* v___x_7317_; lean_object* v___x_7318_; lean_object* v_j_7319_; lean_object* v_b_7320_; lean_object* v___x_7321_; uint8_t v___x_7322_; 
v_one_7315_ = lean_unsigned_to_nat(1u);
v_n_7316_ = lean_nat_sub(v_j_7311_, v_one_7315_);
v___x_7317_ = lean_nat_sub(v_n_7310_, v_j_7311_);
v___x_7318_ = lean_nat_sub(v_n_7307_, v_one_7315_);
v_j_7319_ = lean_nat_sub(v___x_7318_, v___x_7317_);
lean_dec(v___x_7317_);
lean_dec(v___x_7318_);
v_b_7320_ = lean_array_fget_borrowed(v_aa_7309_, v_j_7319_);
v___x_7321_ = lean_array_get_size(v_b_7320_);
v___x_7322_ = lean_nat_dec_lt(v_zero_7313_, v___x_7321_);
if (v___x_7322_ == 0)
{
lean_object* v___x_7323_; 
lean_dec(v_j_7319_);
v___x_7323_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7307_, v_aa_7309_, v_adjustResult_7308_, v_n_7310_, v_n_7316_, v_a_7312_);
return v___x_7323_;
}
else
{
size_t v___x_7324_; size_t v___x_7325_; lean_object* v___x_7326_; lean_object* v___x_7327_; 
v___x_7324_ = ((size_t)0ULL);
v___x_7325_ = lean_usize_of_nat(v___x_7321_);
lean_inc(v_adjustResult_7308_);
v___x_7326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7308_, v_j_7319_, v_b_7320_, v___x_7324_, v___x_7325_, v_a_7312_);
v___x_7327_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7307_, v_aa_7309_, v_adjustResult_7308_, v_n_7310_, v_n_7316_, v___x_7326_);
return v___x_7327_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7328_, lean_object* v_adjustResult_7329_, lean_object* v_aa_7330_, lean_object* v_n_7331_, lean_object* v_j_7332_, lean_object* v_a_7333_){
_start:
{
lean_object* v_res_7334_; 
v_res_7334_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7328_, v_adjustResult_7329_, v_aa_7330_, v_n_7331_, v_j_7332_, v_a_7333_);
lean_dec(v_j_7332_);
lean_dec(v_n_7331_);
lean_dec_ref(v_aa_7330_);
lean_dec(v_n_7328_);
return v_res_7334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7335_, lean_object* v_mr_7336_, lean_object* v_a_7337_){
_start:
{
lean_object* v_n_7338_; lean_object* v___x_7339_; 
v_n_7338_ = lean_array_get_size(v_mr_7336_);
v___x_7339_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7338_, v_adjustResult_7335_, v_mr_7336_, v_n_7338_, v_n_7338_, v_a_7337_);
return v___x_7339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7340_, lean_object* v_mr_7341_, lean_object* v_a_7342_){
_start:
{
lean_object* v_res_7343_; 
v_res_7343_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7340_, v_mr_7341_, v_a_7342_);
lean_dec_ref(v_mr_7341_);
return v_res_7343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7344_, lean_object* v_ref_7345_, lean_object* v_addEntry_7346_, lean_object* v_droppedKeys_7347_, lean_object* v_constantsPerTask_7348_, lean_object* v_droppedEntriesRef_7349_, lean_object* v_adjustResult_7350_, lean_object* v_ty_7351_, lean_object* v_a_7352_, lean_object* v_a_7353_, lean_object* v_a_7354_, lean_object* v_a_7355_){
_start:
{
lean_object* v___x_7357_; 
lean_inc_ref(v_ty_7351_);
v___x_7357_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7344_, v_ty_7351_, v_a_7352_, v_a_7353_, v_a_7354_, v_a_7355_);
if (lean_obj_tag(v___x_7357_) == 0)
{
lean_object* v_a_7358_; lean_object* v___x_7359_; 
v_a_7358_ = lean_ctor_get(v___x_7357_, 0);
lean_inc(v_a_7358_);
lean_dec_ref_known(v___x_7357_, 1);
v___x_7359_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7345_, v_addEntry_7346_, v_droppedKeys_7347_, v_constantsPerTask_7348_, v_droppedEntriesRef_7349_, v_ty_7351_, v_a_7352_, v_a_7353_, v_a_7354_, v_a_7355_);
if (lean_obj_tag(v___x_7359_) == 0)
{
lean_object* v_a_7360_; lean_object* v___x_7362_; uint8_t v_isShared_7363_; uint8_t v_isSharedCheck_7373_; 
v_a_7360_ = lean_ctor_get(v___x_7359_, 0);
v_isSharedCheck_7373_ = !lean_is_exclusive(v___x_7359_);
if (v_isSharedCheck_7373_ == 0)
{
v___x_7362_ = v___x_7359_;
v_isShared_7363_ = v_isSharedCheck_7373_;
goto v_resetjp_7361_;
}
else
{
lean_inc(v_a_7360_);
lean_dec(v___x_7359_);
v___x_7362_ = lean_box(0);
v_isShared_7363_ = v_isSharedCheck_7373_;
goto v_resetjp_7361_;
}
v_resetjp_7361_:
{
lean_object* v___x_7364_; lean_object* v___x_7365_; lean_object* v___x_7366_; lean_object* v___x_7367_; lean_object* v___x_7368_; lean_object* v___x_7369_; lean_object* v___x_7371_; 
v___x_7364_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7358_);
v___x_7365_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7360_);
v___x_7366_ = lean_nat_add(v___x_7364_, v___x_7365_);
lean_dec(v___x_7365_);
lean_dec(v___x_7364_);
v___x_7367_ = lean_mk_empty_array_with_capacity(v___x_7366_);
lean_dec(v___x_7366_);
lean_inc(v_adjustResult_7350_);
v___x_7368_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7350_, v_a_7358_, v___x_7367_);
lean_dec(v_a_7358_);
v___x_7369_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7350_, v_a_7360_, v___x_7368_);
lean_dec(v_a_7360_);
if (v_isShared_7363_ == 0)
{
lean_ctor_set(v___x_7362_, 0, v___x_7369_);
v___x_7371_ = v___x_7362_;
goto v_reusejp_7370_;
}
else
{
lean_object* v_reuseFailAlloc_7372_; 
v_reuseFailAlloc_7372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7372_, 0, v___x_7369_);
v___x_7371_ = v_reuseFailAlloc_7372_;
goto v_reusejp_7370_;
}
v_reusejp_7370_:
{
return v___x_7371_;
}
}
}
else
{
lean_object* v_a_7374_; lean_object* v___x_7376_; uint8_t v_isShared_7377_; uint8_t v_isSharedCheck_7381_; 
lean_dec(v_a_7358_);
lean_dec(v_adjustResult_7350_);
v_a_7374_ = lean_ctor_get(v___x_7359_, 0);
v_isSharedCheck_7381_ = !lean_is_exclusive(v___x_7359_);
if (v_isSharedCheck_7381_ == 0)
{
v___x_7376_ = v___x_7359_;
v_isShared_7377_ = v_isSharedCheck_7381_;
goto v_resetjp_7375_;
}
else
{
lean_inc(v_a_7374_);
lean_dec(v___x_7359_);
v___x_7376_ = lean_box(0);
v_isShared_7377_ = v_isSharedCheck_7381_;
goto v_resetjp_7375_;
}
v_resetjp_7375_:
{
lean_object* v___x_7379_; 
if (v_isShared_7377_ == 0)
{
v___x_7379_ = v___x_7376_;
goto v_reusejp_7378_;
}
else
{
lean_object* v_reuseFailAlloc_7380_; 
v_reuseFailAlloc_7380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7380_, 0, v_a_7374_);
v___x_7379_ = v_reuseFailAlloc_7380_;
goto v_reusejp_7378_;
}
v_reusejp_7378_:
{
return v___x_7379_;
}
}
}
}
else
{
lean_object* v_a_7382_; lean_object* v___x_7384_; uint8_t v_isShared_7385_; uint8_t v_isSharedCheck_7389_; 
lean_dec_ref(v_ty_7351_);
lean_dec(v_adjustResult_7350_);
lean_dec(v_droppedEntriesRef_7349_);
lean_dec(v_constantsPerTask_7348_);
lean_dec(v_droppedKeys_7347_);
lean_dec_ref(v_addEntry_7346_);
v_a_7382_ = lean_ctor_get(v___x_7357_, 0);
v_isSharedCheck_7389_ = !lean_is_exclusive(v___x_7357_);
if (v_isSharedCheck_7389_ == 0)
{
v___x_7384_ = v___x_7357_;
v_isShared_7385_ = v_isSharedCheck_7389_;
goto v_resetjp_7383_;
}
else
{
lean_inc(v_a_7382_);
lean_dec(v___x_7357_);
v___x_7384_ = lean_box(0);
v_isShared_7385_ = v_isSharedCheck_7389_;
goto v_resetjp_7383_;
}
v_resetjp_7383_:
{
lean_object* v___x_7387_; 
if (v_isShared_7385_ == 0)
{
v___x_7387_ = v___x_7384_;
goto v_reusejp_7386_;
}
else
{
lean_object* v_reuseFailAlloc_7388_; 
v_reuseFailAlloc_7388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7388_, 0, v_a_7382_);
v___x_7387_ = v_reuseFailAlloc_7388_;
goto v_reusejp_7386_;
}
v_reusejp_7386_:
{
return v___x_7387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7390_, lean_object* v_ref_7391_, lean_object* v_addEntry_7392_, lean_object* v_droppedKeys_7393_, lean_object* v_constantsPerTask_7394_, lean_object* v_droppedEntriesRef_7395_, lean_object* v_adjustResult_7396_, lean_object* v_ty_7397_, lean_object* v_a_7398_, lean_object* v_a_7399_, lean_object* v_a_7400_, lean_object* v_a_7401_, lean_object* v_a_7402_){
_start:
{
lean_object* v_res_7403_; 
v_res_7403_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7390_, v_ref_7391_, v_addEntry_7392_, v_droppedKeys_7393_, v_constantsPerTask_7394_, v_droppedEntriesRef_7395_, v_adjustResult_7396_, v_ty_7397_, v_a_7398_, v_a_7399_, v_a_7400_, v_a_7401_);
lean_dec(v_a_7401_);
lean_dec_ref(v_a_7400_);
lean_dec(v_a_7399_);
lean_dec_ref(v_a_7398_);
lean_dec(v_ref_7391_);
return v_res_7403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7404_, lean_object* v_00_u03b2_7405_, lean_object* v_moduleTreeRef_7406_, lean_object* v_ref_7407_, lean_object* v_addEntry_7408_, lean_object* v_droppedKeys_7409_, lean_object* v_constantsPerTask_7410_, lean_object* v_droppedEntriesRef_7411_, lean_object* v_adjustResult_7412_, lean_object* v_ty_7413_, lean_object* v_a_7414_, lean_object* v_a_7415_, lean_object* v_a_7416_, lean_object* v_a_7417_){
_start:
{
lean_object* v___x_7419_; 
v___x_7419_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7406_, v_ref_7407_, v_addEntry_7408_, v_droppedKeys_7409_, v_constantsPerTask_7410_, v_droppedEntriesRef_7411_, v_adjustResult_7412_, v_ty_7413_, v_a_7414_, v_a_7415_, v_a_7416_, v_a_7417_);
return v___x_7419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7420_, lean_object* v_00_u03b2_7421_, lean_object* v_moduleTreeRef_7422_, lean_object* v_ref_7423_, lean_object* v_addEntry_7424_, lean_object* v_droppedKeys_7425_, lean_object* v_constantsPerTask_7426_, lean_object* v_droppedEntriesRef_7427_, lean_object* v_adjustResult_7428_, lean_object* v_ty_7429_, lean_object* v_a_7430_, lean_object* v_a_7431_, lean_object* v_a_7432_, lean_object* v_a_7433_, lean_object* v_a_7434_){
_start:
{
lean_object* v_res_7435_; 
v_res_7435_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7420_, v_00_u03b2_7421_, v_moduleTreeRef_7422_, v_ref_7423_, v_addEntry_7424_, v_droppedKeys_7425_, v_constantsPerTask_7426_, v_droppedEntriesRef_7427_, v_adjustResult_7428_, v_ty_7429_, v_a_7430_, v_a_7431_, v_a_7432_, v_a_7433_);
lean_dec(v_a_7433_);
lean_dec_ref(v_a_7432_);
lean_dec(v_a_7431_);
lean_dec_ref(v_a_7430_);
lean_dec(v_ref_7423_);
return v_res_7435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7436_, lean_object* v_00_u03b2_7437_, lean_object* v_adjustResult_7438_, lean_object* v_mr_7439_, lean_object* v_a_7440_){
_start:
{
lean_object* v___x_7441_; 
v___x_7441_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7438_, v_mr_7439_, v_a_7440_);
return v___x_7441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7442_, lean_object* v_00_u03b2_7443_, lean_object* v_adjustResult_7444_, lean_object* v_mr_7445_, lean_object* v_a_7446_){
_start:
{
lean_object* v_res_7447_; 
v_res_7447_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7442_, v_00_u03b2_7443_, v_adjustResult_7444_, v_mr_7445_, v_a_7446_);
lean_dec_ref(v_mr_7445_);
return v_res_7447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7448_, lean_object* v_00_u03b2_7449_, lean_object* v_adjustResult_7450_, lean_object* v_j_7451_, size_t v_sz_7452_, size_t v_i_7453_, lean_object* v_bs_7454_){
_start:
{
lean_object* v___x_7455_; 
v___x_7455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7450_, v_j_7451_, v_sz_7452_, v_i_7453_, v_bs_7454_);
return v___x_7455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7456_, lean_object* v_00_u03b2_7457_, lean_object* v_adjustResult_7458_, lean_object* v_j_7459_, lean_object* v_sz_7460_, lean_object* v_i_7461_, lean_object* v_bs_7462_){
_start:
{
size_t v_sz_boxed_7463_; size_t v_i_boxed_7464_; lean_object* v_res_7465_; 
v_sz_boxed_7463_ = lean_unbox_usize(v_sz_7460_);
lean_dec(v_sz_7460_);
v_i_boxed_7464_ = lean_unbox_usize(v_i_7461_);
lean_dec(v_i_7461_);
v_res_7465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7456_, v_00_u03b2_7457_, v_adjustResult_7458_, v_j_7459_, v_sz_boxed_7463_, v_i_boxed_7464_, v_bs_7462_);
return v_res_7465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7466_, lean_object* v_00_u03b2_7467_, lean_object* v_adjustResult_7468_, lean_object* v_j_7469_, lean_object* v_as_7470_, size_t v_i_7471_, size_t v_stop_7472_, lean_object* v_b_7473_){
_start:
{
lean_object* v___x_7474_; 
v___x_7474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7468_, v_j_7469_, v_as_7470_, v_i_7471_, v_stop_7472_, v_b_7473_);
return v___x_7474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7475_, lean_object* v_00_u03b2_7476_, lean_object* v_adjustResult_7477_, lean_object* v_j_7478_, lean_object* v_as_7479_, lean_object* v_i_7480_, lean_object* v_stop_7481_, lean_object* v_b_7482_){
_start:
{
size_t v_i_boxed_7483_; size_t v_stop_boxed_7484_; lean_object* v_res_7485_; 
v_i_boxed_7483_ = lean_unbox_usize(v_i_7480_);
lean_dec(v_i_7480_);
v_stop_boxed_7484_ = lean_unbox_usize(v_stop_7481_);
lean_dec(v_stop_7481_);
v_res_7485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7475_, v_00_u03b2_7476_, v_adjustResult_7477_, v_j_7478_, v_as_7479_, v_i_boxed_7483_, v_stop_boxed_7484_, v_b_7482_);
lean_dec_ref(v_as_7479_);
return v_res_7485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7486_, lean_object* v_n_7487_, lean_object* v_00_u03b1_7488_, lean_object* v_adjustResult_7489_, lean_object* v_aa_7490_, lean_object* v_n_7491_, lean_object* v_j_7492_, lean_object* v_a_7493_, lean_object* v_a_7494_){
_start:
{
lean_object* v___x_7495_; 
v___x_7495_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7487_, v_adjustResult_7489_, v_aa_7490_, v_n_7491_, v_j_7492_, v_a_7494_);
return v___x_7495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7496_, lean_object* v_n_7497_, lean_object* v_00_u03b1_7498_, lean_object* v_adjustResult_7499_, lean_object* v_aa_7500_, lean_object* v_n_7501_, lean_object* v_j_7502_, lean_object* v_a_7503_, lean_object* v_a_7504_){
_start:
{
lean_object* v_res_7505_; 
v_res_7505_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7496_, v_n_7497_, v_00_u03b1_7498_, v_adjustResult_7499_, v_aa_7500_, v_n_7501_, v_j_7502_, v_a_7503_, v_a_7504_);
lean_dec(v_j_7502_);
lean_dec(v_n_7501_);
lean_dec_ref(v_aa_7500_);
lean_dec(v_n_7497_);
return v_res_7505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7506_, lean_object* v_n_7507_, lean_object* v_00_u03b1_7508_, lean_object* v_aa_7509_, lean_object* v_adjustResult_7510_, lean_object* v_n_7511_, lean_object* v_j_7512_, lean_object* v_a_7513_, lean_object* v_a_7514_){
_start:
{
lean_object* v___x_7515_; 
v___x_7515_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7507_, v_aa_7509_, v_adjustResult_7510_, v_n_7511_, v_j_7512_, v_a_7514_);
return v___x_7515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7516_, lean_object* v_n_7517_, lean_object* v_00_u03b1_7518_, lean_object* v_aa_7519_, lean_object* v_adjustResult_7520_, lean_object* v_n_7521_, lean_object* v_j_7522_, lean_object* v_a_7523_, lean_object* v_a_7524_){
_start:
{
lean_object* v_res_7525_; 
v_res_7525_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7516_, v_n_7517_, v_00_u03b1_7518_, v_aa_7519_, v_adjustResult_7520_, v_n_7521_, v_j_7522_, v_a_7523_, v_a_7524_);
lean_dec(v_n_7521_);
lean_dec_ref(v_aa_7519_);
lean_dec(v_n_7517_);
return v_res_7525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7526_, lean_object* v_v_7527_){
_start:
{
lean_inc(v_v_7527_);
return v_v_7527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7528_, lean_object* v_v_7529_){
_start:
{
lean_object* v_res_7530_; 
v_res_7530_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7528_, v_v_7529_);
lean_dec(v_v_7529_);
lean_dec(v_x_7528_);
return v_res_7530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7532_, lean_object* v_addEntry_7533_, lean_object* v_droppedKeys_7534_, lean_object* v_constantsPerTask_7535_, lean_object* v_droppedEntriesRef_7536_, lean_object* v_ty_7537_, lean_object* v_a_7538_, lean_object* v_a_7539_, lean_object* v_a_7540_, lean_object* v_a_7541_){
_start:
{
lean_object* v___x_7543_; 
lean_inc(v_droppedEntriesRef_7536_);
lean_inc(v_droppedKeys_7534_);
lean_inc_ref(v_addEntry_7533_);
v___x_7543_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7533_, v_droppedKeys_7534_, v_droppedEntriesRef_7536_, v_a_7538_, v_a_7539_, v_a_7540_, v_a_7541_);
if (lean_obj_tag(v___x_7543_) == 0)
{
lean_object* v_a_7544_; lean_object* v___f_7545_; lean_object* v___x_7546_; 
v_a_7544_ = lean_ctor_get(v___x_7543_, 0);
lean_inc(v_a_7544_);
lean_dec_ref_known(v___x_7543_, 1);
v___f_7545_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7546_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7544_, v_ref_7532_, v_addEntry_7533_, v_droppedKeys_7534_, v_constantsPerTask_7535_, v_droppedEntriesRef_7536_, v___f_7545_, v_ty_7537_, v_a_7538_, v_a_7539_, v_a_7540_, v_a_7541_);
return v___x_7546_;
}
else
{
lean_object* v_a_7547_; lean_object* v___x_7549_; uint8_t v_isShared_7550_; uint8_t v_isSharedCheck_7554_; 
lean_dec_ref(v_ty_7537_);
lean_dec(v_droppedEntriesRef_7536_);
lean_dec(v_constantsPerTask_7535_);
lean_dec(v_droppedKeys_7534_);
lean_dec_ref(v_addEntry_7533_);
v_a_7547_ = lean_ctor_get(v___x_7543_, 0);
v_isSharedCheck_7554_ = !lean_is_exclusive(v___x_7543_);
if (v_isSharedCheck_7554_ == 0)
{
v___x_7549_ = v___x_7543_;
v_isShared_7550_ = v_isSharedCheck_7554_;
goto v_resetjp_7548_;
}
else
{
lean_inc(v_a_7547_);
lean_dec(v___x_7543_);
v___x_7549_ = lean_box(0);
v_isShared_7550_ = v_isSharedCheck_7554_;
goto v_resetjp_7548_;
}
v_resetjp_7548_:
{
lean_object* v___x_7552_; 
if (v_isShared_7550_ == 0)
{
v___x_7552_ = v___x_7549_;
goto v_reusejp_7551_;
}
else
{
lean_object* v_reuseFailAlloc_7553_; 
v_reuseFailAlloc_7553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7553_, 0, v_a_7547_);
v___x_7552_ = v_reuseFailAlloc_7553_;
goto v_reusejp_7551_;
}
v_reusejp_7551_:
{
return v___x_7552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7555_, lean_object* v_addEntry_7556_, lean_object* v_droppedKeys_7557_, lean_object* v_constantsPerTask_7558_, lean_object* v_droppedEntriesRef_7559_, lean_object* v_ty_7560_, lean_object* v_a_7561_, lean_object* v_a_7562_, lean_object* v_a_7563_, lean_object* v_a_7564_, lean_object* v_a_7565_){
_start:
{
lean_object* v_res_7566_; 
v_res_7566_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7555_, v_addEntry_7556_, v_droppedKeys_7557_, v_constantsPerTask_7558_, v_droppedEntriesRef_7559_, v_ty_7560_, v_a_7561_, v_a_7562_, v_a_7563_, v_a_7564_);
lean_dec(v_a_7564_);
lean_dec_ref(v_a_7563_);
lean_dec(v_a_7562_);
lean_dec_ref(v_a_7561_);
lean_dec(v_ref_7555_);
return v_res_7566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7567_, lean_object* v_ref_7568_, lean_object* v_addEntry_7569_, lean_object* v_droppedKeys_7570_, lean_object* v_constantsPerTask_7571_, lean_object* v_droppedEntriesRef_7572_, lean_object* v_ty_7573_, lean_object* v_a_7574_, lean_object* v_a_7575_, lean_object* v_a_7576_, lean_object* v_a_7577_){
_start:
{
lean_object* v___x_7579_; 
v___x_7579_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7568_, v_addEntry_7569_, v_droppedKeys_7570_, v_constantsPerTask_7571_, v_droppedEntriesRef_7572_, v_ty_7573_, v_a_7574_, v_a_7575_, v_a_7576_, v_a_7577_);
return v___x_7579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7580_, lean_object* v_ref_7581_, lean_object* v_addEntry_7582_, lean_object* v_droppedKeys_7583_, lean_object* v_constantsPerTask_7584_, lean_object* v_droppedEntriesRef_7585_, lean_object* v_ty_7586_, lean_object* v_a_7587_, lean_object* v_a_7588_, lean_object* v_a_7589_, lean_object* v_a_7590_, lean_object* v_a_7591_){
_start:
{
lean_object* v_res_7592_; 
v_res_7592_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7580_, v_ref_7581_, v_addEntry_7582_, v_droppedKeys_7583_, v_constantsPerTask_7584_, v_droppedEntriesRef_7585_, v_ty_7586_, v_a_7587_, v_a_7588_, v_a_7589_, v_a_7590_);
lean_dec(v_a_7590_);
lean_dec_ref(v_a_7589_);
lean_dec(v_a_7588_);
lean_dec_ref(v_a_7587_);
lean_dec(v_ref_7581_);
return v_res_7592_;
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
