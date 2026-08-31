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
lean_object* v___y_780_; uint8_t v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; uint8_t v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v_toCold_806_; lean_object* v_options_807_; lean_object* v_currRecDepth_808_; lean_object* v_maxRecDepth_809_; lean_object* v_ref_810_; lean_object* v_currNamespace_811_; lean_object* v_openDecls_812_; lean_object* v_initHeartbeats_813_; lean_object* v_maxHeartbeats_814_; lean_object* v_currMacroScope_815_; uint8_t v_diag_816_; uint8_t v_suppressElabErrors_817_; lean_object* v_cancelTk_x3f_823_; 
v_toCold_806_ = lean_ctor_get(v___y_776_, 0);
v_options_807_ = lean_ctor_get(v___y_776_, 1);
v_currRecDepth_808_ = lean_ctor_get(v___y_776_, 2);
v_maxRecDepth_809_ = lean_ctor_get(v___y_776_, 3);
v_ref_810_ = lean_ctor_get(v___y_776_, 4);
v_currNamespace_811_ = lean_ctor_get(v___y_776_, 5);
v_openDecls_812_ = lean_ctor_get(v___y_776_, 6);
v_initHeartbeats_813_ = lean_ctor_get(v___y_776_, 7);
v_maxHeartbeats_814_ = lean_ctor_get(v___y_776_, 8);
v_currMacroScope_815_ = lean_ctor_get(v___y_776_, 9);
v_diag_816_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*10);
v_suppressElabErrors_817_ = lean_ctor_get_uint8(v___y_776_, sizeof(void*)*10 + 1);
v_cancelTk_x3f_823_ = lean_ctor_get(v_toCold_806_, 3);
if (lean_obj_tag(v_cancelTk_x3f_823_) == 1)
{
lean_object* v_val_824_; uint8_t v___x_825_; 
v_val_824_ = lean_ctor_get(v_cancelTk_x3f_823_, 0);
v___x_825_ = l_IO_CancelToken_isSet(v_val_824_);
if (v___x_825_ == 0)
{
goto v___jp_818_;
}
else
{
lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v_x_774_);
v___x_826_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
goto v___jp_818_;
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
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_add(v___y_800_, v___x_802_);
lean_inc(v___y_791_);
lean_inc(v___y_793_);
lean_inc(v___y_794_);
lean_inc(v___y_801_);
lean_inc(v___y_792_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_796_);
lean_inc_ref(v___y_797_);
v___x_804_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_804_, 0, v___y_797_);
lean_ctor_set(v___x_804_, 1, v___y_796_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
lean_ctor_set(v___x_804_, 3, v___y_799_);
lean_ctor_set(v___x_804_, 4, v___y_798_);
lean_ctor_set(v___x_804_, 5, v___y_792_);
lean_ctor_set(v___x_804_, 6, v___y_801_);
lean_ctor_set(v___x_804_, 7, v___y_794_);
lean_ctor_set(v___x_804_, 8, v___y_793_);
lean_ctor_set(v___x_804_, 9, v___y_791_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*10, v___y_790_);
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*10 + 1, v___y_795_);
lean_inc(v___y_777_);
lean_inc(v___y_775_);
v___x_805_ = lean_apply_4(v_x_774_, v___y_775_, v___x_804_, v___y_777_, lean_box(0));
v___y_780_ = v___x_805_;
goto v___jp_779_;
}
v___jp_818_:
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = lean_nat_dec_eq(v_maxRecDepth_809_, v___x_819_);
if (v___x_820_ == 0)
{
uint8_t v___x_821_; 
v___x_821_ = lean_nat_dec_eq(v_currRecDepth_808_, v_maxRecDepth_809_);
if (v___x_821_ == 0)
{
lean_inc(v_ref_810_);
v___y_790_ = v_diag_816_;
v___y_791_ = v_currMacroScope_815_;
v___y_792_ = v_currNamespace_811_;
v___y_793_ = v_maxHeartbeats_814_;
v___y_794_ = v_initHeartbeats_813_;
v___y_795_ = v_suppressElabErrors_817_;
v___y_796_ = v_options_807_;
v___y_797_ = v_toCold_806_;
v___y_798_ = v_ref_810_;
v___y_799_ = v_maxRecDepth_809_;
v___y_800_ = v_currRecDepth_808_;
v___y_801_ = v_openDecls_812_;
goto v___jp_789_;
}
else
{
lean_object* v___x_822_; 
lean_dec_ref(v_x_774_);
lean_inc(v_ref_810_);
v___x_822_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_810_);
v___y_780_ = v___x_822_;
goto v___jp_779_;
}
}
else
{
lean_inc(v_ref_810_);
v___y_790_ = v_diag_816_;
v___y_791_ = v_currMacroScope_815_;
v___y_792_ = v_currNamespace_811_;
v___y_793_ = v_maxHeartbeats_814_;
v___y_794_ = v_initHeartbeats_813_;
v___y_795_ = v_suppressElabErrors_817_;
v___y_796_ = v_options_807_;
v___y_797_ = v_toCold_806_;
v___y_798_ = v_ref_810_;
v___y_799_ = v_maxRecDepth_809_;
v___y_800_ = v_currRecDepth_808_;
v___y_801_ = v_openDecls_812_;
goto v___jp_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v___x_843_; 
v___x_843_ = lean_box(0);
return v___x_843_;
}
else
{
lean_object* v_key_844_; lean_object* v_value_845_; lean_object* v_tail_846_; uint8_t v___x_847_; 
v_key_844_ = lean_ctor_get(v_x_842_, 0);
v_value_845_ = lean_ctor_get(v_x_842_, 1);
v_tail_846_ = lean_ctor_get(v_x_842_, 2);
v___x_847_ = l_Lean_ExprStructEq_beq(v_key_844_, v_a_841_);
if (v___x_847_ == 0)
{
v_x_842_ = v_tail_846_;
goto _start;
}
else
{
lean_object* v___x_849_; 
lean_inc(v_value_845_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_value_845_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_850_, v_x_851_);
lean_dec(v_x_851_);
lean_dec_ref(v_a_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_buckets_855_; lean_object* v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v___x_859_; uint64_t v_fold_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_buckets_855_ = lean_ctor_get(v_m_853_, 1);
v___x_856_ = lean_array_get_size(v_buckets_855_);
v___x_857_ = l_Lean_ExprStructEq_hash(v_a_854_);
v___x_858_ = 32ULL;
v___x_859_ = lean_uint64_shift_right(v___x_857_, v___x_858_);
v_fold_860_ = lean_uint64_xor(v___x_857_, v___x_859_);
v___x_861_ = 16ULL;
v___x_862_ = lean_uint64_shift_right(v_fold_860_, v___x_861_);
v___x_863_ = lean_uint64_xor(v_fold_860_, v___x_862_);
v___x_864_ = lean_uint64_to_usize(v___x_863_);
v___x_865_ = lean_usize_of_nat(v___x_856_);
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_sub(v___x_865_, v___x_866_);
v___x_868_ = lean_usize_land(v___x_864_, v___x_867_);
v___x_869_ = lean_array_uget_borrowed(v_buckets_855_, v___x_868_);
v___x_870_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_854_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_871_, v_a_872_);
lean_dec_ref(v_a_872_);
lean_dec_ref(v_m_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_dec(v_b_875_);
lean_dec_ref(v_a_874_);
return v_x_876_;
}
else
{
lean_object* v_key_877_; lean_object* v_value_878_; lean_object* v_tail_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_key_877_ = lean_ctor_get(v_x_876_, 0);
v_value_878_ = lean_ctor_get(v_x_876_, 1);
v_tail_879_ = lean_ctor_get(v_x_876_, 2);
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v_x_876_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tail_879_);
lean_inc(v_value_878_);
lean_inc(v_key_877_);
lean_dec(v_x_876_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v___x_883_; 
v___x_883_ = l_Lean_ExprStructEq_beq(v_key_877_, v_a_874_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_874_, v_b_875_, v_tail_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 2, v___x_884_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_key_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_value_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v_value_878_);
lean_dec(v_key_877_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_b_875_);
lean_ctor_set(v___x_881_, 0, v_a_874_);
v___x_889_ = v___x_881_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_874_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_b_875_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_tail_879_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
return v_x_892_;
}
else
{
lean_object* v_key_894_; lean_object* v_value_895_; lean_object* v_tail_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_919_; 
v_key_894_ = lean_ctor_get(v_x_893_, 0);
v_value_895_ = lean_ctor_get(v_x_893_, 1);
v_tail_896_ = lean_ctor_get(v_x_893_, 2);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_919_ == 0)
{
v___x_898_ = v_x_893_;
v_isShared_899_ = v_isSharedCheck_919_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_tail_896_);
lean_inc(v_value_895_);
lean_inc(v_key_894_);
lean_dec(v_x_893_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_919_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v_fold_904_; uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_900_ = lean_array_get_size(v_x_892_);
v___x_901_ = l_Lean_ExprStructEq_hash(v_key_894_);
v___x_902_ = 32ULL;
v___x_903_ = lean_uint64_shift_right(v___x_901_, v___x_902_);
v_fold_904_ = lean_uint64_xor(v___x_901_, v___x_903_);
v___x_905_ = 16ULL;
v___x_906_ = lean_uint64_shift_right(v_fold_904_, v___x_905_);
v___x_907_ = lean_uint64_xor(v_fold_904_, v___x_906_);
v___x_908_ = lean_uint64_to_usize(v___x_907_);
v___x_909_ = lean_usize_of_nat(v___x_900_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = lean_usize_sub(v___x_909_, v___x_910_);
v___x_912_ = lean_usize_land(v___x_908_, v___x_911_);
v___x_913_ = lean_array_uget_borrowed(v_x_892_, v___x_912_);
lean_inc(v___x_913_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 2, v___x_913_);
v___x_915_ = v___x_898_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_key_894_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_value_895_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v___x_913_);
v___x_915_ = v_reuseFailAlloc_918_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_array_uset(v_x_892_, v___x_912_, v___x_915_);
v_x_892_ = v___x_916_;
v_x_893_ = v_tail_896_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_920_, lean_object* v_source_921_, lean_object* v_target_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_get_size(v_source_921_);
v___x_924_ = lean_nat_dec_lt(v_i_920_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec_ref(v_source_921_);
lean_dec(v_i_920_);
return v_target_922_;
}
else
{
lean_object* v_es_925_; lean_object* v___x_926_; lean_object* v_source_927_; lean_object* v_target_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_es_925_ = lean_array_fget(v_source_921_, v_i_920_);
v___x_926_ = lean_box(0);
v_source_927_ = lean_array_fset(v_source_921_, v_i_920_, v___x_926_);
v_target_928_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_922_, v_es_925_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_i_920_, v___x_929_);
lean_dec(v_i_920_);
v_i_920_ = v___x_930_;
v_source_921_ = v_source_927_;
v_target_922_ = v_target_928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_932_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_nbuckets_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_933_ = lean_array_get_size(v_data_932_);
v___x_934_ = lean_unsigned_to_nat(2u);
v_nbuckets_935_ = lean_nat_mul(v___x_933_, v___x_934_);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_box(0);
v___x_938_ = lean_mk_array(v_nbuckets_935_, v___x_937_);
v___x_939_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_936_, v_data_932_, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_940_, lean_object* v_x_941_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
uint8_t v___x_942_; 
v___x_942_ = 0;
return v___x_942_;
}
else
{
lean_object* v_key_943_; lean_object* v_tail_944_; uint8_t v___x_945_; 
v_key_943_ = lean_ctor_get(v_x_941_, 0);
v_tail_944_ = lean_ctor_get(v_x_941_, 2);
v___x_945_ = l_Lean_ExprStructEq_beq(v_key_943_, v_a_940_);
if (v___x_945_ == 0)
{
v_x_941_ = v_tail_944_;
goto _start;
}
else
{
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_947_, lean_object* v_x_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_947_, v_x_948_);
lean_dec(v_x_948_);
lean_dec_ref(v_a_947_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_951_, lean_object* v_a_952_, lean_object* v_b_953_){
_start:
{
lean_object* v_size_954_; lean_object* v_buckets_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_998_; 
v_size_954_ = lean_ctor_get(v_m_951_, 0);
v_buckets_955_ = lean_ctor_get(v_m_951_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_m_951_);
if (v_isSharedCheck_998_ == 0)
{
v___x_957_ = v_m_951_;
v_isShared_958_ = v_isSharedCheck_998_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_buckets_955_);
lean_inc(v_size_954_);
lean_dec(v_m_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_998_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v_fold_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v___x_971_; lean_object* v_bkt_972_; uint8_t v___x_973_; 
v___x_959_ = lean_array_get_size(v_buckets_955_);
v___x_960_ = l_Lean_ExprStructEq_hash(v_a_952_);
v___x_961_ = 32ULL;
v___x_962_ = lean_uint64_shift_right(v___x_960_, v___x_961_);
v_fold_963_ = lean_uint64_xor(v___x_960_, v___x_962_);
v___x_964_ = 16ULL;
v___x_965_ = lean_uint64_shift_right(v_fold_963_, v___x_964_);
v___x_966_ = lean_uint64_xor(v_fold_963_, v___x_965_);
v___x_967_ = lean_uint64_to_usize(v___x_966_);
v___x_968_ = lean_usize_of_nat(v___x_959_);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_sub(v___x_968_, v___x_969_);
v___x_971_ = lean_usize_land(v___x_967_, v___x_970_);
v_bkt_972_ = lean_array_uget_borrowed(v_buckets_955_, v___x_971_);
v___x_973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_952_, v_bkt_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v_size_x27_975_; lean_object* v___x_976_; lean_object* v_buckets_x27_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_974_ = lean_unsigned_to_nat(1u);
v_size_x27_975_ = lean_nat_add(v_size_954_, v___x_974_);
lean_dec(v_size_954_);
lean_inc(v_bkt_972_);
v___x_976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_976_, 0, v_a_952_);
lean_ctor_set(v___x_976_, 1, v_b_953_);
lean_ctor_set(v___x_976_, 2, v_bkt_972_);
v_buckets_x27_977_ = lean_array_uset(v_buckets_955_, v___x_971_, v___x_976_);
v___x_978_ = lean_unsigned_to_nat(4u);
v___x_979_ = lean_nat_mul(v_size_x27_975_, v___x_978_);
v___x_980_ = lean_unsigned_to_nat(3u);
v___x_981_ = lean_nat_div(v___x_979_, v___x_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_array_get_size(v_buckets_x27_977_);
v___x_983_ = lean_nat_dec_le(v___x_981_, v___x_982_);
lean_dec(v___x_981_);
if (v___x_983_ == 0)
{
lean_object* v_val_984_; lean_object* v___x_986_; 
v_val_984_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_977_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_val_984_);
lean_ctor_set(v___x_957_, 0, v_size_x27_975_);
v___x_986_ = v___x_957_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_size_x27_975_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_val_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v___x_989_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_buckets_x27_977_);
lean_ctor_set(v___x_957_, 0, v_size_x27_975_);
v___x_989_ = v___x_957_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_size_x27_975_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_buckets_x27_977_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v___x_991_; lean_object* v_buckets_x27_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
lean_inc(v_bkt_972_);
v___x_991_ = lean_box(0);
v_buckets_x27_992_ = lean_array_uset(v_buckets_955_, v___x_971_, v___x_991_);
v___x_993_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_952_, v_b_953_, v_bkt_972_);
v___x_994_ = lean_array_uset(v_buckets_x27_992_, v___x_971_, v___x_993_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_994_);
v___x_996_ = v___x_957_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_size_954_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_999_, lean_object* v_e_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = lean_st_ref_take(v_a_999_);
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_1003_, v_e_1000_, v_a_1001_);
v___x_1005_ = lean_st_ref_put(v_a_999_, v___x_1004_);
v___x_1006_ = lean_box(0);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_1007_, lean_object* v_e_1008_, lean_object* v_a_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_1007_, v_e_1008_, v_a_1009_);
lean_dec(v_a_1007_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_apply_1(v_x_1013_, lean_box(0));
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_1019_, v_x_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1026_; lean_object* v_dummy_1027_; 
v___x_1026_ = lean_box(0);
v_dummy_1027_ = l_Lean_Expr_sort___override(v___x_1026_);
return v_dummy_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1028_, lean_object* v_post_1029_, size_t v_sz_1030_, size_t v_i_1031_, lean_object* v_bs_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_usize_dec_lt(v_i_1031_, v_sz_1030_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_post_1029_);
lean_dec_ref(v_pre_1028_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_bs_1032_);
return v___x_1038_;
}
else
{
lean_object* v_v_1039_; lean_object* v___x_1040_; 
v_v_1039_ = lean_array_uget_borrowed(v_bs_1032_, v_i_1031_);
lean_inc(v_v_1039_);
lean_inc_ref(v_post_1029_);
lean_inc_ref(v_pre_1028_);
v___x_1040_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1028_, v_post_1029_, v_v_1039_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; lean_object* v_bs_x27_1043_; size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = lean_unsigned_to_nat(0u);
v_bs_x27_1043_ = lean_array_uset(v_bs_1032_, v_i_1031_, v___x_1042_);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_add(v_i_1031_, v___x_1044_);
v___x_1046_ = lean_array_uset(v_bs_x27_1043_, v_i_1031_, v_a_1041_);
v_i_1031_ = v___x_1045_;
v_bs_1032_ = v___x_1046_;
goto _start;
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v_bs_1032_);
lean_dec_ref(v_post_1029_);
lean_dec_ref(v_pre_1028_);
v_a_1048_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1040_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1040_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1056_, lean_object* v_post_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
if (lean_obj_tag(v_x_1058_) == 5)
{
lean_object* v_fn_1065_; lean_object* v_arg_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_fn_1065_ = lean_ctor_get(v_x_1058_, 0);
lean_inc_ref(v_fn_1065_);
v_arg_1066_ = lean_ctor_get(v_x_1058_, 1);
lean_inc_ref(v_arg_1066_);
lean_dec_ref_known(v_x_1058_, 2);
v___x_1067_ = lean_array_set(v_x_1059_, v_x_1060_, v_arg_1066_);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_sub(v_x_1060_, v___x_1068_);
lean_dec(v_x_1060_);
v_x_1058_ = v_fn_1065_;
v_x_1059_ = v___x_1067_;
v_x_1060_ = v___x_1069_;
goto _start;
}
else
{
lean_object* v___x_1071_; 
lean_dec(v_x_1060_);
lean_inc_ref(v_post_1057_);
lean_inc_ref(v_pre_1056_);
v___x_1071_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1056_, v_post_1057_, v_x_1058_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_1075_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_sz_1073_ = lean_array_size(v_x_1059_);
v___x_1074_ = ((size_t)0ULL);
lean_inc_ref(v_post_1057_);
lean_inc_ref(v_pre_1056_);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1056_, v_post_1057_, v_sz_1073_, v___x_1074_, v_x_1059_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = l_Lean_mkAppN(v_a_1072_, v_a_1076_);
lean_dec(v_a_1076_);
v___x_1078_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1056_, v_post_1057_, v___x_1077_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1078_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v_a_1072_);
lean_dec_ref(v_post_1057_);
lean_dec_ref(v_pre_1056_);
v_a_1079_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1075_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1075_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_dec_ref(v_x_1059_);
lean_dec_ref(v_post_1057_);
lean_dec_ref(v_pre_1056_);
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v___x_1087_, lean_object* v_pre_1088_, lean_object* v_e_1089_, lean_object* v_post_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Core_checkSystem(v___x_1087_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref_known(v___x_1095_, 1);
lean_inc_ref(v_pre_1088_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc_ref(v_e_1089_);
v___x_1096_ = lean_apply_4(v_pre_1088_, v_e_1089_, v___y_1092_, v___y_1093_, lean_box(0));
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1212_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1212_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1212_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___y_1102_; 
switch(lean_obj_tag(v_a_1097_))
{
case 0:
{
lean_object* v_e_1202_; lean_object* v___x_1204_; 
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_e_1089_);
lean_dec_ref(v_pre_1088_);
v_e_1202_ = lean_ctor_get(v_a_1097_, 0);
lean_inc_ref(v_e_1202_);
lean_dec_ref_known(v_a_1097_, 1);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_e_1202_);
v___x_1204_ = v___x_1099_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_e_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
case 1:
{
lean_object* v_e_1206_; lean_object* v___x_1207_; 
lean_del_object(v___x_1099_);
lean_dec_ref(v_e_1089_);
v_e_1206_ = lean_ctor_get(v_a_1097_, 0);
lean_inc_ref(v_e_1206_);
lean_dec_ref_known(v_a_1097_, 1);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1207_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_e_1206_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1209_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v_a_1208_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1209_;
}
else
{
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1207_;
}
}
default: 
{
lean_object* v_e_x3f_1210_; 
lean_del_object(v___x_1099_);
v_e_x3f_1210_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_e_x3f_1210_);
lean_dec_ref_known(v_a_1097_, 1);
if (lean_obj_tag(v_e_x3f_1210_) == 0)
{
v___y_1102_ = v_e_1089_;
goto v___jp_1101_;
}
else
{
lean_object* v_val_1211_; 
lean_dec_ref(v_e_1089_);
v_val_1211_ = lean_ctor_get(v_e_x3f_1210_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_e_x3f_1210_, 1);
v___y_1102_ = v_val_1211_;
goto v___jp_1101_;
}
}
}
v___jp_1101_:
{
switch(lean_obj_tag(v___y_1102_))
{
case 7:
{
lean_object* v_binderName_1103_; lean_object* v_binderType_1104_; lean_object* v_body_1105_; uint8_t v_binderInfo_1106_; lean_object* v___x_1107_; 
v_binderName_1103_ = lean_ctor_get(v___y_1102_, 0);
v_binderType_1104_ = lean_ctor_get(v___y_1102_, 1);
v_body_1105_ = lean_ctor_get(v___y_1102_, 2);
v_binderInfo_1106_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1104_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1107_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_binderType_1104_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1109_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
lean_inc_ref(v_body_1105_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1109_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_body_1105_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; size_t v___x_1111_; size_t v___x_1112_; uint8_t v___x_1113_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = lean_ptr_addr(v_binderType_1104_);
v___x_1112_ = lean_ptr_addr(v_a_1108_);
v___x_1113_ = lean_usize_dec_eq(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_inc(v_binderName_1103_);
lean_dec_ref_known(v___y_1102_, 3);
v___x_1114_ = l_Lean_Expr_forallE___override(v_binderName_1103_, v_a_1108_, v_a_1110_, v_binderInfo_1106_);
v___x_1115_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1114_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1115_;
}
else
{
size_t v___x_1116_; size_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_ptr_addr(v_body_1105_);
v___x_1117_ = lean_ptr_addr(v_a_1110_);
v___x_1118_ = lean_usize_dec_eq(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_inc(v_binderName_1103_);
lean_dec_ref_known(v___y_1102_, 3);
v___x_1119_ = l_Lean_Expr_forallE___override(v_binderName_1103_, v_a_1108_, v_a_1110_, v_binderInfo_1106_);
v___x_1120_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1119_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1120_;
}
else
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1106_, v_binderInfo_1106_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_inc(v_binderName_1103_);
lean_dec_ref_known(v___y_1102_, 3);
v___x_1122_ = l_Lean_Expr_forallE___override(v_binderName_1103_, v_a_1108_, v_a_1110_, v_binderInfo_1106_);
v___x_1123_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1122_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_a_1110_);
lean_dec(v_a_1108_);
v___x_1124_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___y_1102_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1124_;
}
}
}
}
else
{
lean_dec(v_a_1108_);
lean_dec_ref_known(v___y_1102_, 3);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1109_;
}
}
else
{
lean_dec_ref_known(v___y_1102_, 3);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1107_;
}
}
case 6:
{
lean_object* v_binderName_1125_; lean_object* v_binderType_1126_; lean_object* v_body_1127_; uint8_t v_binderInfo_1128_; lean_object* v___x_1129_; 
v_binderName_1125_ = lean_ctor_get(v___y_1102_, 0);
v_binderType_1126_ = lean_ctor_get(v___y_1102_, 1);
v_body_1127_ = lean_ctor_get(v___y_1102_, 2);
v_binderInfo_1128_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1126_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1129_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_binderType_1126_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
lean_inc_ref(v_body_1127_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1131_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_body_1127_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; size_t v___x_1133_; size_t v___x_1134_; uint8_t v___x_1135_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = lean_ptr_addr(v_binderType_1126_);
v___x_1134_ = lean_ptr_addr(v_a_1130_);
v___x_1135_ = lean_usize_dec_eq(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_inc(v_binderName_1125_);
lean_dec_ref_known(v___y_1102_, 3);
v___x_1136_ = l_Lean_Expr_lam___override(v_binderName_1125_, v_a_1130_, v_a_1132_, v_binderInfo_1128_);
v___x_1137_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1136_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1137_;
}
else
{
size_t v___x_1138_; size_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_ptr_addr(v_body_1127_);
v___x_1139_ = lean_ptr_addr(v_a_1132_);
v___x_1140_ = lean_usize_dec_eq(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc(v_binderName_1125_);
lean_dec_ref_known(v___y_1102_, 3);
v___x_1141_ = l_Lean_Expr_lam___override(v_binderName_1125_, v_a_1130_, v_a_1132_, v_binderInfo_1128_);
v___x_1142_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1141_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1142_;
}
else
{
uint8_t v___x_1143_; 
v___x_1143_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_1128_, v_binderInfo_1128_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_inc(v_binderName_1125_);
lean_dec_ref_known(v___y_1102_, 3);
v___x_1144_ = l_Lean_Expr_lam___override(v_binderName_1125_, v_a_1130_, v_a_1132_, v_binderInfo_1128_);
v___x_1145_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1144_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1145_;
}
else
{
lean_object* v___x_1146_; 
lean_dec(v_a_1132_);
lean_dec(v_a_1130_);
v___x_1146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___y_1102_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1146_;
}
}
}
}
else
{
lean_dec(v_a_1130_);
lean_dec_ref_known(v___y_1102_, 3);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1131_;
}
}
else
{
lean_dec_ref_known(v___y_1102_, 3);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1129_;
}
}
case 8:
{
lean_object* v_declName_1147_; lean_object* v_type_1148_; lean_object* v_value_1149_; lean_object* v_body_1150_; uint8_t v_nondep_1151_; lean_object* v___x_1152_; 
v_declName_1147_ = lean_ctor_get(v___y_1102_, 0);
v_type_1148_ = lean_ctor_get(v___y_1102_, 1);
v_value_1149_ = lean_ctor_get(v___y_1102_, 2);
v_body_1150_ = lean_ctor_get(v___y_1102_, 3);
v_nondep_1151_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1148_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1152_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_type_1148_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
lean_inc_ref(v_value_1149_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1154_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_value_1149_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
lean_inc_ref(v_body_1150_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1156_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_body_1150_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; size_t v___x_1158_; size_t v___x_1159_; uint8_t v___x_1160_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = lean_ptr_addr(v_type_1148_);
v___x_1159_ = lean_ptr_addr(v_a_1153_);
v___x_1160_ = lean_usize_dec_eq(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_inc(v_declName_1147_);
lean_dec_ref_known(v___y_1102_, 4);
v___x_1161_ = l_Lean_Expr_letE___override(v_declName_1147_, v_a_1153_, v_a_1155_, v_a_1157_, v_nondep_1151_);
v___x_1162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1161_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1162_;
}
else
{
size_t v___x_1163_; size_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_ptr_addr(v_value_1149_);
v___x_1164_ = lean_ptr_addr(v_a_1155_);
v___x_1165_ = lean_usize_dec_eq(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_inc(v_declName_1147_);
lean_dec_ref_known(v___y_1102_, 4);
v___x_1166_ = l_Lean_Expr_letE___override(v_declName_1147_, v_a_1153_, v_a_1155_, v_a_1157_, v_nondep_1151_);
v___x_1167_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1166_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1167_;
}
else
{
size_t v___x_1168_; size_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1168_ = lean_ptr_addr(v_body_1150_);
v___x_1169_ = lean_ptr_addr(v_a_1157_);
v___x_1170_ = lean_usize_dec_eq(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_inc(v_declName_1147_);
lean_dec_ref_known(v___y_1102_, 4);
v___x_1171_ = l_Lean_Expr_letE___override(v_declName_1147_, v_a_1153_, v_a_1155_, v_a_1157_, v_nondep_1151_);
v___x_1172_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1171_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec(v_a_1157_);
lean_dec(v_a_1155_);
lean_dec(v_a_1153_);
v___x_1173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___y_1102_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1173_;
}
}
}
}
else
{
lean_dec(v_a_1155_);
lean_dec(v_a_1153_);
lean_dec_ref_known(v___y_1102_, 4);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1156_;
}
}
else
{
lean_dec(v_a_1153_);
lean_dec_ref_known(v___y_1102_, 4);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1154_;
}
}
else
{
lean_dec_ref_known(v___y_1102_, 4);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1152_;
}
}
case 5:
{
lean_object* v_dummy_1174_; lean_object* v_nargs_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_dummy_1174_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1175_ = l_Lean_Expr_getAppNumArgs(v___y_1102_);
lean_inc(v_nargs_1175_);
v___x_1176_ = lean_mk_array(v_nargs_1175_, v_dummy_1174_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_sub(v_nargs_1175_, v___x_1177_);
lean_dec(v_nargs_1175_);
v___x_1179_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1088_, v_post_1090_, v___y_1102_, v___x_1176_, v___x_1178_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1179_;
}
case 10:
{
lean_object* v_data_1180_; lean_object* v_expr_1181_; lean_object* v___x_1182_; 
v_data_1180_ = lean_ctor_get(v___y_1102_, 0);
v_expr_1181_ = lean_ctor_get(v___y_1102_, 1);
lean_inc_ref(v_expr_1181_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1182_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_expr_1181_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; size_t v___x_1184_; size_t v___x_1185_; uint8_t v___x_1186_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
v___x_1184_ = lean_ptr_addr(v_expr_1181_);
v___x_1185_ = lean_ptr_addr(v_a_1183_);
v___x_1186_ = lean_usize_dec_eq(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_inc(v_data_1180_);
lean_dec_ref_known(v___y_1102_, 2);
v___x_1187_ = l_Lean_Expr_mdata___override(v_data_1180_, v_a_1183_);
v___x_1188_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1187_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; 
lean_dec(v_a_1183_);
v___x_1189_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___y_1102_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1189_;
}
}
else
{
lean_dec_ref_known(v___y_1102_, 2);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1182_;
}
}
case 11:
{
lean_object* v_typeName_1190_; lean_object* v_idx_1191_; lean_object* v_struct_1192_; lean_object* v___x_1193_; 
v_typeName_1190_ = lean_ctor_get(v___y_1102_, 0);
v_idx_1191_ = lean_ctor_get(v___y_1102_, 1);
v_struct_1192_ = lean_ctor_get(v___y_1102_, 2);
lean_inc_ref(v_struct_1192_);
lean_inc_ref(v_post_1090_);
lean_inc_ref(v_pre_1088_);
v___x_1193_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1088_, v_post_1090_, v_struct_1192_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; size_t v___x_1195_; size_t v___x_1196_; uint8_t v___x_1197_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = lean_ptr_addr(v_struct_1192_);
v___x_1196_ = lean_ptr_addr(v_a_1194_);
v___x_1197_ = lean_usize_dec_eq(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_inc(v_idx_1191_);
lean_inc(v_typeName_1190_);
lean_dec_ref_known(v___y_1102_, 3);
v___x_1198_ = l_Lean_Expr_proj___override(v_typeName_1190_, v_idx_1191_, v_a_1194_);
v___x_1199_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___x_1198_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1199_;
}
else
{
lean_object* v___x_1200_; 
lean_dec(v_a_1194_);
v___x_1200_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___y_1102_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1200_;
}
}
else
{
lean_dec_ref_known(v___y_1102_, 3);
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_pre_1088_);
return v___x_1193_;
}
}
default: 
{
lean_object* v___x_1201_; 
v___x_1201_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1088_, v_post_1090_, v___y_1102_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1201_;
}
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_e_1089_);
lean_dec_ref(v_pre_1088_);
v_a_1213_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1096_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1096_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_post_1090_);
lean_dec_ref(v_e_1089_);
lean_dec_ref(v_pre_1088_);
v_a_1221_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1095_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1095_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1229_, lean_object* v_pre_1230_, lean_object* v_e_1231_, lean_object* v_post_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1229_, v_pre_1230_, v_e_1231_, v_post_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1238_, lean_object* v_post_1239_, lean_object* v_e_1240_, lean_object* v_a_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_inc(v_a_1241_);
v___x_1245_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1245_, 0, lean_box(0));
lean_closure_set(v___x_1245_, 1, lean_box(0));
lean_closure_set(v___x_1245_, 2, v_a_1241_);
v___x_1246_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1245_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1278_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1278_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1278_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1247_, v_e_1240_);
lean_dec(v_a_1247_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; 
lean_del_object(v___x_1249_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1240_);
v___f_1253_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1253_, 0, v___x_1252_);
lean_closure_set(v___f_1253_, 1, v_pre_1238_);
lean_closure_set(v___f_1253_, 2, v_e_1240_);
lean_closure_set(v___f_1253_, 3, v_post_1239_);
v___x_1254_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1253_, v_a_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc_n(v_a_1255_, 2);
lean_dec_ref_known(v___x_1254_, 1);
lean_inc(v_a_1241_);
v___f_1256_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1256_, 0, v_a_1241_);
lean_closure_set(v___f_1256_, 1, v_e_1240_);
lean_closure_set(v___f_1256_, 2, v_a_1255_);
v___x_1257_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1256_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1265_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v_a_1255_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1255_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1255_);
v_a_1266_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1257_);
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
else
{
lean_dec_ref(v_e_1240_);
return v___x_1254_;
}
}
else
{
lean_object* v_val_1274_; lean_object* v___x_1276_; 
lean_dec_ref(v_e_1240_);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1238_);
v_val_1274_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v___x_1251_, 1);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_val_1274_);
v___x_1276_ = v___x_1249_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_val_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v_e_1240_);
lean_dec_ref(v_post_1239_);
lean_dec_ref(v_pre_1238_);
v_a_1279_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1246_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1246_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1287_, lean_object* v_post_1288_, lean_object* v_e_1289_, lean_object* v_a_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
lean_inc_ref(v_post_1288_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc_ref(v_e_1289_);
v___x_1294_ = lean_apply_4(v_post_1288_, v_e_1289_, v___y_1291_, v___y_1292_, lean_box(0));
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1313_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1313_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1313_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
switch(lean_obj_tag(v_a_1295_))
{
case 0:
{
lean_object* v_e_1299_; lean_object* v___x_1301_; 
lean_dec_ref(v_e_1289_);
lean_dec_ref(v_post_1288_);
lean_dec_ref(v_pre_1287_);
v_e_1299_ = lean_ctor_get(v_a_1295_, 0);
lean_inc_ref(v_e_1299_);
lean_dec_ref_known(v_a_1295_, 1);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v_e_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_e_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
case 1:
{
lean_object* v_e_1303_; lean_object* v___x_1304_; 
lean_del_object(v___x_1297_);
lean_dec_ref(v_e_1289_);
v_e_1303_ = lean_ctor_get(v_a_1295_, 0);
lean_inc_ref(v_e_1303_);
lean_dec_ref_known(v_a_1295_, 1);
v___x_1304_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1287_, v_post_1288_, v_e_1303_, v_a_1290_, v___y_1291_, v___y_1292_);
return v___x_1304_;
}
default: 
{
lean_object* v_e_x3f_1305_; 
lean_dec_ref(v_post_1288_);
lean_dec_ref(v_pre_1287_);
v_e_x3f_1305_ = lean_ctor_get(v_a_1295_, 0);
lean_inc(v_e_x3f_1305_);
lean_dec_ref_known(v_a_1295_, 1);
if (lean_obj_tag(v_e_x3f_1305_) == 0)
{
lean_object* v___x_1307_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v_e_1289_);
v___x_1307_ = v___x_1297_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_e_1289_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v_val_1309_; lean_object* v___x_1311_; 
lean_dec_ref(v_e_1289_);
v_val_1309_ = lean_ctor_get(v_e_x3f_1305_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v_e_x3f_1305_, 1);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v_val_1309_);
v___x_1311_ = v___x_1297_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_val_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v_e_1289_);
lean_dec_ref(v_post_1288_);
lean_dec_ref(v_pre_1287_);
v_a_1314_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1294_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1294_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1322_, lean_object* v_post_1323_, lean_object* v_e_1324_, lean_object* v_a_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1322_, v_post_1323_, v_e_1324_, v_a_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v_a_1325_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1330_, lean_object* v_post_1331_, lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_bs_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1330_, v_post_1331_, v_sz_boxed_1339_, v_i_boxed_1340_, v_bs_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1342_, lean_object* v_post_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1342_, v_post_1343_, v_x_1344_, v_x_1345_, v_x_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1352_, lean_object* v_post_1353_, lean_object* v_e_1354_, lean_object* v_a_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1352_, v_post_1353_, v_e_1354_, v_a_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v_a_1355_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_apply_1(v_x_1361_, lean_box(0));
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1367_, v_x_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1372_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_unsigned_to_nat(16u);
v___x_1375_ = lean_mk_array(v___x_1374_, v___x_1373_);
return v___x_1375_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v___x_1376_);
return v___x_1378_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1380_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1380_, 0, lean_box(0));
lean_closure_set(v___x_1380_, 1, lean_box(0));
lean_closure_set(v___x_1380_, 2, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1381_, lean_object* v_pre_1382_, lean_object* v_post_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___x_1390_; 
v___x_1387_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1388_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1387_, v___y_1384_, v___y_1385_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1382_, v_post_1383_, v_input_1381_, v_a_1389_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1392_, 0, lean_box(0));
lean_closure_set(v___x_1392_, 1, lean_box(0));
lean_closure_set(v___x_1392_, 2, v_a_1389_);
v___x_1393_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1392_, v___y_1384_, v___y_1385_);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1401_);
v___x_1395_ = v___x_1393_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_a_1391_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1391_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_dec(v_a_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1402_, lean_object* v_pre_1403_, lean_object* v_post_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1402_, v_pre_1403_, v_post_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___f_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; 
v___f_1415_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1416_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1417_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1411_, v___f_1415_, v___f_1416_, v_a_1412_, v_a_1413_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1418_, v_a_1419_, v_a_1420_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1423_, lean_object* v_m_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1424_, v_a_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1427_, v_m_1428_, v_a_1429_);
lean_dec_ref(v_a_1429_);
lean_dec_ref(v_m_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1431_, lean_object* v_ref_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1432_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_ref_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1437_, v_ref_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1460_, v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1468_, v_a_1469_, v_b_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1472_, lean_object* v_a_1473_, lean_object* v_x_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1473_, v_x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1476_, lean_object* v_a_1477_, lean_object* v_x_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1476_, v_a_1477_, v_x_1478_);
lean_dec(v_x_1478_);
lean_dec_ref(v_a_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1480_, lean_object* v_a_1481_, lean_object* v_x_1482_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_a_1481_, v_x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1484_, lean_object* v_a_1485_, lean_object* v_x_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_1484_, v_a_1485_, v_x_1486_);
lean_dec(v_x_1486_);
lean_dec_ref(v_a_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1489_, lean_object* v_data_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_data_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_1492_, lean_object* v_a_1493_, lean_object* v_b_1494_, lean_object* v_x_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__12___redArg(v_a_1493_, v_b_1494_, v_x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_1497_, lean_object* v_i_1498_, lean_object* v_source_1499_, lean_object* v_target_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_1498_, v_source_1499_, v_target_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_1503_, v_x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; lean_object* v_env_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1509_ = lean_st_ref_get(v___y_1507_);
v_env_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc_ref(v_env_1510_);
lean_dec(v___x_1509_);
v___x_1511_ = l_Lean_isRecCore(v_env_1510_, v_declName_1506_);
v___x_1512_ = lean_box(v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1514_, v___y_1515_);
lean_dec(v___y_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1518_, v___y_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_env_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1535_ = lean_st_ref_get(v___y_1533_);
v_env_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc_ref(v_env_1536_);
lean_dec(v___x_1535_);
v___x_1537_ = l_Lean_getReducibilityStatusCore(v_env_1536_, v_declName_1532_);
v___x_1538_ = lean_box(v___x_1537_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1540_, v___y_1541_);
lean_dec(v___y_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1566_; 
v___x_1550_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1544_, v___y_1548_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1566_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1566_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_unbox(v_a_1551_);
lean_dec(v_a_1551_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = 1;
v___x_1557_ = lean_box(v___x_1556_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1557_);
v___x_1559_ = v___x_1553_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1561_ = 0;
v___x_1562_ = lean_box(v___x_1561_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1562_);
v___x_1564_ = v___x_1553_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1574_, lean_object* v_b_1575_){
_start:
{
lean_object* v_array_1577_; lean_object* v_start_1578_; lean_object* v_stop_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1596_; 
v_array_1577_ = lean_ctor_get(v_a_1574_, 0);
v_start_1578_ = lean_ctor_get(v_a_1574_, 1);
v_stop_1579_ = lean_ctor_get(v_a_1574_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1574_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1581_ = v_a_1574_;
v_isShared_1582_ = v_isSharedCheck_1596_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_stop_1579_);
lean_inc(v_start_1578_);
lean_inc(v_array_1577_);
lean_dec(v_a_1574_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1596_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_lt(v_start_1578_, v_stop_1579_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_del_object(v___x_1581_);
lean_dec(v_stop_1579_);
lean_dec(v_start_1578_);
lean_dec_ref(v_array_1577_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_b_1575_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = lean_nat_add(v_start_1578_, v___x_1586_);
lean_inc_ref(v_array_1577_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1587_);
v___x_1589_ = v___x_1581_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_array_1577_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_stop_1579_);
v___x_1589_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = lean_array_fget(v_array_1577_, v_start_1578_);
lean_dec(v_start_1578_);
lean_dec_ref(v_array_1577_);
v___x_1591_ = l_Lean_Expr_hasExprMVar(v___x_1590_);
lean_dec(v___x_1590_);
if (v___x_1591_ == 0)
{
v_a_1574_ = v___x_1589_;
v_b_1575_ = v___x_1585_;
goto _start;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_dec_ref_known(v___x_1593_, 1);
v_a_1574_ = v___x_1589_;
v_b_1575_ = v___x_1585_;
goto _start;
}
else
{
lean_dec_ref(v___x_1589_);
return v___x_1593_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1597_, v_b_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1609_, uint8_t v_isMatch_1610_, uint8_t v_root_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___y_1618_; lean_object* v_b_1619_; lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1609_, v_root_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1793_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1793_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1793_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___y_1636_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; 
if (v_root_1611_ == 0)
{
lean_object* v___x_1781_; 
lean_inc(v_a_1631_);
v___x_1781_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1631_);
if (lean_obj_tag(v___x_1781_) == 1)
{
lean_object* v_val_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1792_; 
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1792_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_val_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1792_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 2);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_val_1782_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
}
}
else
{
lean_dec(v___x_1781_);
v___y_1646_ = v_a_1612_;
v___y_1647_ = v_a_1613_;
v___y_1648_ = v_a_1614_;
v___y_1649_ = v_a_1615_;
goto v___jp_1645_;
}
}
else
{
v___y_1646_ = v_a_1612_;
v___y_1647_ = v_a_1613_;
v___y_1648_ = v_a_1614_;
v___y_1649_ = v_a_1615_;
goto v___jp_1645_;
}
v___jp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1637_ = l_Lean_Expr_getAppNumArgs(v_a_1631_);
lean_inc(v___x_1637_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___y_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_mk_empty_array_with_capacity(v___x_1637_);
lean_dec(v___x_1637_);
v___x_1640_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1631_, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1638_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1641_);
v___x_1643_ = v___x_1633_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
v___jp_1645_:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Expr_getAppFn(v_a_1631_);
switch(lean_obj_tag(v___x_1650_))
{
case 1:
{
lean_object* v_fvarId_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_del_object(v___x_1633_);
v_fvarId_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_fvarId_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = l_Lean_Expr_getAppNumArgs(v_a_1631_);
lean_inc(v___x_1652_);
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v_fvarId_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_mk_empty_array_with_capacity(v___x_1652_);
lean_dec(v___x_1652_);
v___x_1655_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1631_, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1653_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
case 2:
{
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
if (v_isMatch_1610_ == 0)
{
lean_object* v_mvarId_1658_; lean_object* v___x_1659_; uint8_t v_isDefEqStuckEx_1660_; 
v_mvarId_1658_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_mvarId_1658_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1659_ = l_Lean_Meta_Context_config(v___y_1646_);
v_isDefEqStuckEx_1660_ = lean_ctor_get_uint8(v___x_1659_, 4);
lean_dec_ref(v___x_1659_);
if (v_isDefEqStuckEx_1660_ == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1658_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1675_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1675_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1675_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_unbox(v_a_1662_);
lean_dec(v_a_1662_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1667_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1671_);
v___x_1673_ = v___x_1664_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v_a_1676_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1661_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1661_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_dec(v_mvarId_1658_);
v___x_1684_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec_ref_known(v___x_1650_, 1);
v___x_1686_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
case 4:
{
lean_object* v_declName_1688_; lean_object* v___x_1689_; uint8_t v_isDefEqStuckEx_1690_; 
v_declName_1688_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_declName_1688_);
lean_dec_ref_known(v___x_1650_, 2);
v___x_1689_ = l_Lean_Meta_Context_config(v___y_1646_);
v_isDefEqStuckEx_1690_ = lean_ctor_get_uint8(v___x_1689_, 4);
lean_dec_ref(v___x_1689_);
if (v_isDefEqStuckEx_1690_ == 0)
{
v___y_1636_ = v_declName_1688_;
goto v___jp_1635_;
}
else
{
uint8_t v___x_1691_; 
v___x_1691_ = l_Lean_Expr_hasExprMVar(v_a_1631_);
if (v___x_1691_ == 0)
{
v___y_1636_ = v_declName_1688_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1692_; 
lean_inc(v_declName_1688_);
v___x_1692_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1688_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; uint8_t v___x_1694_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_unbox(v_a_1693_);
lean_dec(v_a_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v_env_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_st_ref_get(v___y_1649_);
v_env_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc_ref(v_env_1696_);
lean_dec(v___x_1695_);
v___x_1697_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1696_, v_a_1631_);
if (lean_obj_tag(v___x_1697_) == 1)
{
lean_object* v_val_1698_; lean_object* v_numDiscrs_1699_; lean_object* v_nargs_1700_; lean_object* v_dummy_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_val_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v_numDiscrs_1699_ = lean_ctor_get(v_val_1698_, 1);
lean_inc(v_numDiscrs_1699_);
v_nargs_1700_ = l_Lean_Expr_getAppNumArgs(v_a_1631_);
v_dummy_1701_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1700_);
v___x_1702_ = lean_mk_array(v_nargs_1700_, v_dummy_1701_);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_sub(v_nargs_1700_, v___x_1703_);
lean_dec(v_nargs_1700_);
lean_inc(v_a_1631_);
v___x_1705_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1631_, v___x_1702_, v___x_1704_);
v___x_1706_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1698_);
lean_dec(v_val_1698_);
v___x_1707_ = lean_nat_add(v___x_1706_, v_numDiscrs_1699_);
lean_dec(v_numDiscrs_1699_);
v___x_1708_ = l_Array_toSubarray___redArg(v___x_1705_, v___x_1706_, v___x_1707_);
v___x_1709_ = lean_box(0);
v___x_1710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1708_, v___x_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_dec_ref_known(v___x_1710_, 1);
v___y_1636_ = v_declName_1688_;
goto v___jp_1635_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_declName_1688_);
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v___x_1719_; lean_object* v_a_1720_; uint8_t v___x_1721_; 
lean_dec(v___x_1697_);
lean_inc(v_declName_1688_);
v___x_1719_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1688_, v___y_1649_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
if (v___x_1721_ == 0)
{
v___y_1636_ = v_declName_1688_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_dec_ref_known(v___x_1722_, 1);
v___y_1636_ = v_declName_1688_;
goto v___jp_1635_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_declName_1688_);
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_dec_ref_known(v___x_1731_, 1);
v___y_1636_ = v_declName_1688_;
goto v___jp_1635_;
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_declName_1688_);
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_declName_1688_);
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v_a_1740_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1692_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1692_);
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
}
case 7:
{
lean_object* v_binderType_1748_; lean_object* v_body_1749_; uint8_t v___x_1750_; 
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v_binderType_1748_ = lean_ctor_get(v___x_1650_, 1);
lean_inc_ref(v_binderType_1748_);
v_body_1749_ = lean_ctor_get(v___x_1650_, 2);
lean_inc_ref(v_body_1749_);
lean_dec_ref_known(v___x_1650_, 3);
v___x_1750_ = l_Lean_Expr_hasLooseBVars(v_body_1749_);
if (v___x_1750_ == 0)
{
v___y_1618_ = v_binderType_1748_;
v_b_1619_ = v_body_1749_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1749_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___y_1618_ = v_binderType_1748_;
v_b_1619_ = v_a_1752_;
goto v___jp_1617_;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_binderType_1748_);
v_a_1753_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1751_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1751_);
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
}
case 9:
{
lean_object* v_a_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v_a_1761_ = lean_ctor_get(v___x_1650_, 0);
lean_inc_ref(v_a_1761_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1762_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_a_1761_);
v___x_1763_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
case 11:
{
lean_object* v_typeName_1766_; lean_object* v_idx_1767_; lean_object* v_struct_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_del_object(v___x_1633_);
v_typeName_1766_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_typeName_1766_);
v_idx_1767_ = lean_ctor_get(v___x_1650_, 1);
lean_inc(v_idx_1767_);
v_struct_1768_ = lean_ctor_get(v___x_1650_, 2);
lean_inc_ref(v_struct_1768_);
lean_dec_ref_known(v___x_1650_, 3);
v___x_1769_ = l_Lean_Expr_getAppNumArgs(v_a_1631_);
lean_inc(v___x_1769_);
v___x_1770_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1770_, 0, v_typeName_1766_);
lean_ctor_set(v___x_1770_, 1, v_idx_1767_);
lean_ctor_set(v___x_1770_, 2, v___x_1769_);
v___x_1771_ = lean_unsigned_to_nat(1u);
v___x_1772_ = lean_mk_empty_array_with_capacity(v___x_1771_);
v___x_1773_ = lean_array_push(v___x_1772_, v_struct_1768_);
v___x_1774_ = lean_mk_empty_array_with_capacity(v___x_1769_);
lean_dec(v___x_1769_);
v___x_1775_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1631_, v___x_1774_);
v___x_1776_ = l_Array_append___redArg(v___x_1773_, v___x_1775_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1770_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
default: 
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec_ref(v___x_1650_);
lean_del_object(v___x_1633_);
lean_dec(v_a_1631_);
v___x_1779_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_a_1794_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1630_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1630_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
v___jp_1617_:
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lean_Expr_hasLooseBVars(v_b_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1621_ = lean_box(5);
v___x_1622_ = lean_unsigned_to_nat(2u);
v___x_1623_ = lean_mk_empty_array_with_capacity(v___x_1622_);
v___x_1624_ = lean_array_push(v___x_1623_, v___y_1618_);
v___x_1625_ = lean_array_push(v___x_1624_, v_b_1619_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1621_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec_ref(v_b_1619_);
lean_dec_ref(v___y_1618_);
v___x_1628_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1802_, lean_object* v_isMatch_1803_, lean_object* v_root_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
uint8_t v_isMatch_boxed_1810_; uint8_t v_root_boxed_1811_; lean_object* v_res_1812_; 
v_isMatch_boxed_1810_ = lean_unbox(v_isMatch_1803_);
v_root_boxed_1811_ = lean_unbox(v_root_1804_);
v_res_1812_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1802_, v_isMatch_boxed_1810_, v_root_boxed_1811_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1813_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1827_, lean_object* v_R_1828_, lean_object* v_a_1829_, lean_object* v_b_1830_, lean_object* v_c_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1829_, v_b_1830_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1838_, lean_object* v_R_1839_, lean_object* v_a_1840_, lean_object* v_b_1841_, lean_object* v_c_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1838_, v_R_1839_, v_a_1840_, v_b_1841_, v_c_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1849_, uint8_t v_root_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
uint8_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = 1;
v___x_1857_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1849_, v___x_1856_, v_root_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1858_, lean_object* v_root_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
uint8_t v_root_boxed_1865_; lean_object* v_res_1866_; 
v_root_boxed_1865_ = lean_unbox(v_root_1859_);
v_res_1866_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1858_, v_root_boxed_1865_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
return v_res_1866_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = lean_unsigned_to_nat(16u);
v___x_1871_ = lean_mk_array(v___x_1870_, v___x_1869_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v___x_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1877_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_1878_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1881_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1879_);
lean_ctor_set(v___x_1881_, 2, v___x_1878_);
lean_ctor_set(v___x_1881_, 3, v___x_1877_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_00_u03b1_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__4);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1886_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___x_1890_);
lean_ctor_set(v___x_1892_, 2, v___x_1889_);
lean_ctor_set(v___x_1892_, 3, v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v_values_1897_; lean_object* v_star_1898_; lean_object* v_children_1899_; lean_object* v_pending_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_values_1897_ = lean_ctor_get(v_x_1895_, 0);
v_star_1898_ = lean_ctor_get(v_x_1895_, 1);
v_children_1899_ = lean_ctor_get(v_x_1895_, 2);
v_pending_1900_ = lean_ctor_get(v_x_1895_, 3);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_x_1895_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v_x_1895_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_pending_1900_);
lean_inc(v_children_1899_);
lean_inc(v_star_1898_);
lean_inc(v_values_1897_);
lean_dec(v_x_1895_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_array_push(v_pending_1900_, v_x_1896_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 3, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_values_1897_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_star_1898_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_children_1899_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1910_, v_x_1911_);
return v___x_1912_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1913_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_mk_empty_array_with_capacity(v___x_1914_);
v___x_1916_ = lean_array_push(v___x_1915_, v___x_1913_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1918_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v_env_1929_; lean_object* v___x_1930_; lean_object* v_mctx_1931_; lean_object* v_lctx_1932_; lean_object* v_options_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1928_ = lean_st_ref_get(v___y_1926_);
v_env_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_ref(v_env_1929_);
lean_dec(v___x_1928_);
v___x_1930_ = lean_st_ref_get(v___y_1924_);
v_mctx_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_ref(v_mctx_1931_);
lean_dec(v___x_1930_);
v_lctx_1932_ = lean_ctor_get(v___y_1923_, 2);
v_options_1933_ = lean_ctor_get(v___y_1925_, 1);
lean_inc_ref(v_options_1933_);
lean_inc_ref(v_lctx_1932_);
v___x_1934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1934_, 0, v_env_1929_);
lean_ctor_set(v___x_1934_, 1, v_mctx_1931_);
lean_ctor_set(v___x_1934_, 2, v_lctx_1932_);
lean_ctor_set(v___x_1934_, 3, v_options_1933_);
v___x_1935_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_msgData_1922_);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_ref_1950_; lean_object* v___x_1951_; lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_ref_1950_ = lean_ctor_get(v___y_1947_, 4);
v___x_1951_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
lean_inc(v_ref_1950_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_ref_1950_);
lean_ctor_set(v___x_1956_, 1, v_a_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 1);
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
return v_res_1967_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1970_ = l_Lean_stringToMessageData(v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1971_, lean_object* v_todo_1972_, lean_object* v_e_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1973_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1973_, v_root_1971_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2120_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2120_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2120_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_v_1986_; lean_object* v___x_1992_; lean_object* v_k_1994_; lean_object* v_nargs_1995_; lean_object* v_todo_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; 
v___x_1992_ = l_Lean_Expr_getAppFn(v_a_1981_);
switch(lean_obj_tag(v___x_1992_))
{
case 9:
{
lean_object* v_a_2039_; 
lean_dec(v_a_1981_);
v_a_2039_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_ref(v_a_2039_);
lean_dec_ref_known(v___x_1992_, 1);
v_v_1986_ = v_a_2039_;
goto v___jp_1985_;
}
case 4:
{
lean_object* v_declName_2040_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; 
v_declName_2040_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_declName_2040_);
if (v_root_1971_ == 0)
{
lean_object* v___x_2048_; 
lean_inc(v_a_1981_);
v___x_2048_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1981_);
if (lean_obj_tag(v___x_2048_) == 1)
{
lean_object* v_val_2049_; 
lean_dec(v_declName_2040_);
lean_dec_ref_known(v___x_1992_, 2);
lean_dec(v_a_1981_);
v_val_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v_v_1986_ = v_val_2049_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2050_; 
lean_dec(v___x_2048_);
lean_del_object(v___x_1983_);
v___x_2050_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2040_, v_a_1981_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2061_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_unbox(v_a_2051_);
lean_dec(v_a_2051_);
if (v___x_2055_ == 0)
{
lean_del_object(v___x_2053_);
v___y_2042_ = v_a_1974_;
v___y_2043_ = v_a_1975_;
v___y_2044_ = v_a_1976_;
v___y_2045_ = v_a_1977_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_dec(v_declName_2040_);
lean_dec_ref_known(v___x_1992_, 2);
lean_dec(v_a_1981_);
v___x_2056_ = lean_box(3);
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
lean_ctor_set(v___x_2057_, 1, v_todo_1972_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2057_);
v___x_2059_ = v___x_2053_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref_known(v___x_1992_, 2);
lean_dec(v_declName_2040_);
lean_dec(v_a_1981_);
lean_dec_ref(v_todo_1972_);
v_a_2062_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2050_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2050_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
else
{
lean_del_object(v___x_1983_);
v___y_2042_ = v_a_1974_;
v___y_2043_ = v_a_1975_;
v___y_2044_ = v_a_1976_;
v___y_2045_ = v_a_1977_;
goto v___jp_2041_;
}
v___jp_2041_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = l_Lean_Expr_getAppNumArgs(v_a_1981_);
lean_inc(v___x_2046_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v_declName_2040_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v_k_1994_ = v___x_2047_;
v_nargs_1995_ = v___x_2046_;
v_todo_1996_ = v_todo_1972_;
v___y_1997_ = v___y_2042_;
v___y_1998_ = v___y_2043_;
v___y_1999_ = v___y_2044_;
v___y_2000_ = v___y_2045_;
goto v___jp_1993_;
}
}
case 11:
{
lean_object* v_typeName_2070_; lean_object* v_idx_2071_; lean_object* v_struct_2072_; lean_object* v___x_2073_; lean_object* v___y_2075_; lean_object* v_env_2079_; uint8_t v___x_2080_; 
lean_del_object(v___x_1983_);
v_typeName_2070_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_typeName_2070_);
v_idx_2071_ = lean_ctor_get(v___x_1992_, 1);
lean_inc(v_idx_2071_);
v_struct_2072_ = lean_ctor_get(v___x_1992_, 2);
lean_inc_ref(v_struct_2072_);
v___x_2073_ = lean_st_ref_get(v_a_1977_);
v_env_2079_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_ref(v_env_2079_);
lean_dec(v___x_2073_);
v___x_2080_ = l_Lean_isClass(v_env_2079_, v_typeName_2070_);
if (v___x_2080_ == 0)
{
v___y_2075_ = v_struct_2072_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2072_);
v___y_2075_ = v___x_2081_;
goto v___jp_2074_;
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = l_Lean_Expr_getAppNumArgs(v_a_1981_);
lean_inc(v___x_2076_);
v___x_2077_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2077_, 0, v_typeName_2070_);
lean_ctor_set(v___x_2077_, 1, v_idx_2071_);
lean_ctor_set(v___x_2077_, 2, v___x_2076_);
v___x_2078_ = lean_array_push(v_todo_1972_, v___y_2075_);
v_k_1994_ = v___x_2077_;
v_nargs_1995_ = v___x_2076_;
v_todo_1996_ = v___x_2078_;
v___y_1997_ = v_a_1974_;
v___y_1998_ = v_a_1975_;
v___y_1999_ = v_a_1976_;
v___y_2000_ = v_a_1977_;
goto v___jp_1993_;
}
}
case 1:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref_known(v___x_1992_, 1);
lean_del_object(v___x_1983_);
lean_dec(v_a_1981_);
v___x_2082_ = lean_box(3);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v_todo_1972_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
case 2:
{
lean_object* v_mvarId_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
lean_del_object(v___x_1983_);
lean_dec(v_a_1981_);
v_mvarId_2085_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_mvarId_2085_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_2086_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2087_ = l_Lean_instBEqMVarId_beq(v_mvarId_2085_, v___x_2086_);
lean_dec(v_mvarId_2085_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v_todo_1972_);
v___x_2088_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2089_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2088_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = lean_box(3);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v_todo_1972_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
case 7:
{
lean_object* v_binderType_2093_; lean_object* v_body_2094_; lean_object* v_b_2096_; uint8_t v___x_2106_; 
lean_del_object(v___x_1983_);
lean_dec(v_a_1981_);
v_binderType_2093_ = lean_ctor_get(v___x_1992_, 1);
lean_inc_ref(v_binderType_2093_);
v_body_2094_ = lean_ctor_get(v___x_1992_, 2);
lean_inc_ref(v_body_2094_);
lean_dec_ref_known(v___x_1992_, 3);
v___x_2106_ = l_Lean_Expr_hasLooseBVars(v_body_2094_);
if (v___x_2106_ == 0)
{
v_b_2096_ = v_body_2094_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2094_, v_a_1976_, v_a_1977_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v_b_2096_ = v_a_2108_;
goto v___jp_2095_;
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_binderType_2093_);
lean_dec_ref(v_todo_1972_);
v_a_2109_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2107_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2107_);
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
v___jp_2095_:
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Lean_Expr_hasLooseBVars(v_b_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2098_ = lean_box(5);
v___x_2099_ = lean_array_push(v_todo_1972_, v_binderType_2093_);
v___x_2100_ = lean_array_push(v___x_2099_, v_b_2096_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2098_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec_ref(v_b_2096_);
lean_dec_ref(v_binderType_2093_);
v___x_2103_ = lean_box(4);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_todo_1972_);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
}
default: 
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec_ref(v___x_1992_);
lean_del_object(v___x_1983_);
lean_dec(v_a_1981_);
v___x_2117_ = lean_box(4);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_todo_1972_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
v___jp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1987_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1987_, 0, v_v_1986_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v_todo_1972_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1988_);
v___x_1990_ = v___x_1983_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
v___jp_1993_:
{
lean_object* v___x_2001_; 
lean_inc(v_nargs_1995_);
v___x_2001_ = l_Lean_Meta_getFunInfoNArgs(v___x_1992_, v_nargs_1995_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v_paramInfo_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2029_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v_paramInfo_2003_ = lean_ctor_get(v_a_2002_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_a_2002_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_a_2002_, 1);
lean_dec(v_unused_2030_);
v___x_2005_ = v_a_2002_;
v_isShared_2006_ = v_isSharedCheck_2029_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_paramInfo_2003_);
lean_dec(v_a_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2029_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = lean_unsigned_to_nat(1u);
v___x_2008_ = lean_nat_sub(v_nargs_1995_, v___x_2007_);
lean_dec(v_nargs_1995_);
v___x_2009_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_2003_, v___x_2008_, v_a_1981_, v_todo_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec_ref(v_paramInfo_2003_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v_a_2010_);
lean_ctor_set(v___x_2005_, 0, v_k_1994_);
v___x_2015_ = v___x_2005_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_k_1994_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2017_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2015_);
v___x_2017_ = v___x_2012_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_del_object(v___x_2005_);
lean_dec(v_k_1994_);
v_a_2021_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2009_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2009_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_todo_1996_);
lean_dec(v_nargs_1995_);
lean_dec(v_k_1994_);
lean_dec(v_a_1981_);
v_a_2031_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2001_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2001_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_todo_1972_);
v_a_2121_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_1980_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_1980_);
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
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref(v_e_1973_);
v___x_2129_ = lean_box(3);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v_todo_1972_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2132_, lean_object* v_todo_2133_, lean_object* v_e_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
uint8_t v_root_boxed_2140_; lean_object* v_res_2141_; 
v_root_boxed_2140_ = lean_unbox(v_root_2132_);
v_res_2141_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2140_, v_todo_2133_, v_e_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2142_, lean_object* v_msg_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2150_, lean_object* v_msg_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2150_, v_msg_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2157_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_unsigned_to_nat(8u);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2165_ = 1;
v___x_2166_ = lean_unsigned_to_nat(8u);
v___x_2167_ = lean_mk_empty_array_with_capacity(v___x_2166_);
v___x_2168_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2165_, v___x_2167_, v_e_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2176_, uint8_t v_root_2177_, lean_object* v_todo_2178_, lean_object* v_keys_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2185_ = lean_array_get_size(v_todo_2178_);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = lean_nat_dec_eq(v___x_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v_e_2191_; lean_object* v_todo_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2188_ = l_Lean_instInhabitedExpr;
v___x_2189_ = lean_unsigned_to_nat(1u);
v___x_2190_ = lean_nat_sub(v___x_2185_, v___x_2189_);
v_e_2191_ = lean_array_get(v___x_2188_, v_todo_2178_, v___x_2190_);
lean_dec(v___x_2190_);
v_todo_2192_ = lean_array_pop(v_todo_2178_);
v___x_2193_ = lean_box(v_root_2177_);
lean_inc_ref(v_op_2176_);
lean_inc(v_a_2183_);
lean_inc_ref(v_a_2182_);
lean_inc(v_a_2181_);
lean_inc_ref(v_a_2180_);
v___x_2194_ = lean_apply_8(v_op_2176_, v___x_2193_, v_todo_2192_, v_e_2191_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, lean_box(0));
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v_fst_2196_; lean_object* v_snd_2197_; lean_object* v___x_2198_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v_fst_2196_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_fst_2196_);
v_snd_2197_ = lean_ctor_get(v_a_2195_, 1);
lean_inc(v_snd_2197_);
lean_dec(v_a_2195_);
v___x_2198_ = lean_array_push(v_keys_2179_, v_fst_2196_);
v_root_2177_ = v___x_2187_;
v_todo_2178_ = v_snd_2197_;
v_keys_2179_ = v___x_2198_;
goto _start;
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v_keys_2179_);
lean_dec_ref(v_op_2176_);
v_a_2200_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2194_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2194_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v_todo_2178_);
lean_dec_ref(v_op_2176_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_keys_2179_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2209_, lean_object* v_root_2210_, lean_object* v_todo_2211_, lean_object* v_keys_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
uint8_t v_root_boxed_2218_; lean_object* v_res_2219_; 
v_root_boxed_2218_ = lean_unbox(v_root_2210_);
v_res_2219_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2209_, v_root_boxed_2218_, v_todo_2211_, v_keys_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_op_2227_; lean_object* v___x_2228_; lean_object* v_todo_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_op_2227_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2228_ = lean_unsigned_to_nat(8u);
v_todo_2229_ = lean_mk_empty_array_with_capacity(v___x_2228_);
v___x_2230_ = 1;
lean_inc_ref(v_todo_2229_);
v___x_2231_ = lean_array_push(v_todo_2229_, v_e_2221_);
v___x_2232_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2227_, v___x_2230_, v___x_2231_, v_todo_2229_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2240_, lean_object* v_todo_2241_, lean_object* v_e_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
uint8_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = 1;
v___x_2249_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2242_, v___x_2248_, v_root_2240_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2267_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2267_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2267_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_fst_2254_; lean_object* v_snd_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2266_; 
v_fst_2254_ = lean_ctor_get(v_a_2250_, 0);
v_snd_2255_ = lean_ctor_get(v_a_2250_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_a_2250_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2257_ = v_a_2250_;
v_isShared_2258_ = v_isSharedCheck_2266_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_snd_2255_);
lean_inc(v_fst_2254_);
lean_dec(v_a_2250_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2266_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = l_Array_append___redArg(v_todo_2241_, v_snd_2255_);
lean_dec(v_snd_2255_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 1, v___x_2259_);
v___x_2261_ = v___x_2257_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_fst_2254_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2263_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2261_);
v___x_2263_ = v___x_2252_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2241_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2268_, lean_object* v_todo_2269_, lean_object* v_e_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
uint8_t v_root_boxed_2276_; lean_object* v_res_2277_; 
v_root_boxed_2276_ = lean_unbox(v_root_2268_);
v_res_2277_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2276_, v_todo_2269_, v_e_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_op_2285_; lean_object* v___x_2286_; lean_object* v_todo_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_op_2285_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2286_ = lean_unsigned_to_nat(8u);
v_todo_2287_ = lean_mk_empty_array_with_capacity(v___x_2286_);
v___x_2288_ = 1;
lean_inc_ref(v_todo_2287_);
v___x_2289_ = lean_array_push(v_todo_2287_, v_e_2279_);
v___x_2290_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2285_, v___x_2288_, v___x_2289_, v_todo_2287_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(lean_object* v_tries_2298_, lean_object* v_m_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = lean_st_mk_ref(v_tries_2298_);
lean_inc(v___x_2305_);
v___x_2306_ = lean_apply_6(v_m_2299_, v___x_2305_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, lean_box(0));
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2316_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = lean_st_ref_get(v___x_2305_);
lean_dec(v___x_2305_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v_a_2307_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2312_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v___x_2305_);
v_a_2317_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2306_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2306_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0___boxed(lean_object* v_tries_2325_, lean_object* v_m_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2325_, v_m_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2333_, lean_object* v_m_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_tries_2340_; lean_object* v_roots_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2394_; 
v_tries_2340_ = lean_ctor_get(v_d_2333_, 0);
v_roots_2341_ = lean_ctor_get(v_d_2333_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_d_2333_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2343_ = v_d_2333_;
v_isShared_2344_ = v_isSharedCheck_2394_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_roots_2341_);
lean_inc(v_tries_2340_);
lean_dec(v_d_2333_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2394_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___y_2346_; lean_object* v___x_2375_; uint8_t v_transparency_2376_; uint8_t v___x_2377_; uint8_t v___x_2378_; 
v___x_2375_ = l_Lean_Meta_Context_config(v_a_2335_);
v_transparency_2376_ = lean_ctor_get_uint8(v___x_2375_, 9);
lean_dec_ref(v___x_2375_);
v___x_2377_ = 2;
v___x_2378_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v_keyedConfig_2379_; uint8_t v_trackZetaDelta_2380_; lean_object* v_zetaDeltaSet_2381_; lean_object* v_lctx_2382_; lean_object* v_localInstances_2383_; lean_object* v_defEqCtx_x3f_2384_; lean_object* v_synthPendingDepth_2385_; lean_object* v_customCanUnfoldPredicate_x3f_2386_; uint8_t v_univApprox_2387_; uint8_t v_inTypeClassResolution_2388_; uint8_t v_cacheInferType_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_keyedConfig_2379_ = lean_ctor_get(v_a_2335_, 0);
v_trackZetaDelta_2380_ = lean_ctor_get_uint8(v_a_2335_, sizeof(void*)*7);
v_zetaDeltaSet_2381_ = lean_ctor_get(v_a_2335_, 1);
v_lctx_2382_ = lean_ctor_get(v_a_2335_, 2);
v_localInstances_2383_ = lean_ctor_get(v_a_2335_, 3);
v_defEqCtx_x3f_2384_ = lean_ctor_get(v_a_2335_, 4);
v_synthPendingDepth_2385_ = lean_ctor_get(v_a_2335_, 5);
v_customCanUnfoldPredicate_x3f_2386_ = lean_ctor_get(v_a_2335_, 6);
v_univApprox_2387_ = lean_ctor_get_uint8(v_a_2335_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2388_ = lean_ctor_get_uint8(v_a_2335_, sizeof(void*)*7 + 2);
v_cacheInferType_2389_ = lean_ctor_get_uint8(v_a_2335_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2379_);
v___x_2390_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2377_, v_keyedConfig_2379_);
lean_inc(v_customCanUnfoldPredicate_x3f_2386_);
lean_inc(v_synthPendingDepth_2385_);
lean_inc(v_defEqCtx_x3f_2384_);
lean_inc_ref(v_localInstances_2383_);
lean_inc_ref(v_lctx_2382_);
lean_inc(v_zetaDeltaSet_2381_);
v___x_2391_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v_zetaDeltaSet_2381_);
lean_ctor_set(v___x_2391_, 2, v_lctx_2382_);
lean_ctor_set(v___x_2391_, 3, v_localInstances_2383_);
lean_ctor_set(v___x_2391_, 4, v_defEqCtx_x3f_2384_);
lean_ctor_set(v___x_2391_, 5, v_synthPendingDepth_2385_);
lean_ctor_set(v___x_2391_, 6, v_customCanUnfoldPredicate_x3f_2386_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7, v_trackZetaDelta_2380_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7 + 1, v_univApprox_2387_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2388_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*7 + 3, v_cacheInferType_2389_);
lean_inc(v_a_2338_);
lean_inc_ref(v_a_2337_);
lean_inc(v_a_2336_);
v___x_2392_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2340_, v_m_2334_, v___x_2391_, v_a_2336_, v_a_2337_, v_a_2338_);
v___y_2346_ = v___x_2392_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2393_; 
lean_inc(v_a_2338_);
lean_inc_ref(v_a_2337_);
lean_inc(v_a_2336_);
lean_inc_ref(v_a_2335_);
v___x_2393_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg___lam__0(v_tries_2340_, v_m_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
v___y_2346_ = v___x_2393_;
goto v___jp_2345_;
}
v___jp_2345_:
{
if (lean_obj_tag(v___y_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2366_; 
v_a_2347_ = lean_ctor_get(v___y_2346_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___y_2346_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2349_ = v___y_2346_;
v_isShared_2350_ = v_isSharedCheck_2366_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___y_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2366_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_fst_2351_; lean_object* v_snd_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2365_; 
v_fst_2351_ = lean_ctor_get(v_a_2347_, 0);
v_snd_2352_ = lean_ctor_get(v_a_2347_, 1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_a_2347_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2354_ = v_a_2347_;
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_snd_2352_);
lean_inc(v_fst_2351_);
lean_dec(v_a_2347_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2365_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_snd_2352_);
v___x_2357_ = v___x_2343_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_snd_2352_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_roots_2341_);
v___x_2357_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_fst_2351_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2359_);
v___x_2361_ = v___x_2349_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_del_object(v___x_2343_);
lean_dec_ref(v_roots_2341_);
v_a_2367_ = lean_ctor_get(v___y_2346_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___y_2346_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___y_2346_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___y_2346_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2395_, lean_object* v_m_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2395_, v_m_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2403_, lean_object* v_00_u03b2_2404_, lean_object* v_d_2405_, lean_object* v_m_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2405_, v_m_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2413_, lean_object* v_00_u03b2_2414_, lean_object* v_d_2415_, lean_object* v_m_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2413_, v_00_u03b2_2414_, v_d_2415_, v_m_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2423_, lean_object* v_v_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2427_ = lean_st_ref_take(v_a_2425_);
v___x_2428_ = lean_array_set(v___x_2427_, v_i_2423_, v_v_2424_);
v___x_2429_ = lean_st_ref_put(v_a_2425_, v___x_2428_);
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2432_, lean_object* v_v_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2432_, v_v_2433_, v_a_2434_);
lean_dec(v_a_2434_);
lean_dec(v_i_2432_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2437_, lean_object* v_i_2438_, lean_object* v_v_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2438_, v_v_2439_, v_a_2440_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_i_2448_, lean_object* v_v_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2447_, v_i_2448_, v_v_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec(v_i_2448_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_sz_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_sz_2459_ = lean_array_get_size(v_a_2458_);
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2462_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_mk_empty_array_with_capacity(v___x_2463_);
v___x_2465_ = lean_array_push(v___x_2464_, v_e_2457_);
v___x_2466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2461_);
lean_ctor_set(v___x_2466_, 1, v___x_2460_);
lean_ctor_set(v___x_2466_, 2, v___x_2462_);
lean_ctor_set(v___x_2466_, 3, v___x_2465_);
v___x_2467_ = lean_array_push(v_a_2458_, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_sz_2459_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2469_, lean_object* v_e_2470_){
_start:
{
lean_object* v_modifyGet_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; 
v_modifyGet_2471_ = lean_ctor_get(v_inst_2469_, 2);
lean_inc(v_modifyGet_2471_);
lean_dec_ref(v_inst_2469_);
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2472_, 0, v_e_2470_);
v___x_2473_ = lean_apply_2(v_modifyGet_2471_, lean_box(0), v___f_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2474_, lean_object* v_00_u03b1_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_e_2478_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2477_, v_e_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2480_, lean_object* v_00_u03b1_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_e_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2480_, v_00_u03b1_2481_, v_inst_2482_, v_inst_2483_, v_e_2484_);
lean_dec_ref(v_inst_2482_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2486_, lean_object* v_e_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v___x_2490_; lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2490_ = lean_st_ref_take(v_a_2488_);
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_array_get_size(v___x_2490_);
v___x_2498_ = lean_nat_dec_lt(v_i_2486_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_dec_ref(v_e_2487_);
v_fst_2492_ = v___x_2496_;
v_snd_2493_ = v___x_2490_;
goto v___jp_2491_;
}
else
{
lean_object* v_v_2499_; lean_object* v_xs_x27_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v_v_2499_ = lean_array_fget(v___x_2490_, v_i_2486_);
v_xs_x27_2500_ = lean_array_fset(v___x_2490_, v_i_2486_, v___x_2496_);
v___x_2501_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2499_, v_e_2487_);
v___x_2502_ = lean_array_fset(v_xs_x27_2500_, v_i_2486_, v___x_2501_);
v_fst_2492_ = v___x_2496_;
v_snd_2493_ = v___x_2502_;
goto v___jp_2491_;
}
v___jp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_st_ref_put(v_a_2488_, v_snd_2493_);
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_fst_2492_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2503_, lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2503_, v_e_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec(v_i_2503_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2508_, lean_object* v_i_2509_, lean_object* v_e_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2509_, v_e_2510_, v_a_2511_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2518_, lean_object* v_i_2519_, lean_object* v_e_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2518_, v_i_2519_, v_e_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec(v_i_2519_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
lean_inc(v___y_2529_);
v___x_2535_ = lean_apply_6(v_x_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2537_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2544_, lean_object* v_localInsts_2545_, lean_object* v_x_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___f_2553_; lean_object* v___x_2554_; 
lean_inc(v___y_2547_);
v___f_2553_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2553_, 0, v_x_2546_);
lean_closure_set(v___f_2553_, 1, v___y_2547_);
v___x_2554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2544_, v_localInsts_2545_, v___f_2553_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2554_) == 0)
{
return v___x_2554_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2563_, lean_object* v_localInsts_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2563_, v_localInsts_2564_, v_x_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b1_2574_, lean_object* v_lctx_2575_, lean_object* v_localInsts_2576_, lean_object* v_x_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2575_, v_localInsts_2576_, v_x_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2585_, lean_object* v_00_u03b1_2586_, lean_object* v_lctx_2587_, lean_object* v_localInsts_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2585_, v_00_u03b1_2586_, v_lctx_2587_, v_localInsts_2588_, v_x_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v_sz_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2600_ = lean_st_ref_take(v___y_2598_);
v_sz_2601_ = lean_array_get_size(v___x_2600_);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2604_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2605_ = lean_unsigned_to_nat(1u);
v___x_2606_ = lean_mk_empty_array_with_capacity(v___x_2605_);
v___x_2607_ = lean_array_push(v___x_2606_, v_e_2597_);
v___x_2608_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2603_);
lean_ctor_set(v___x_2608_, 1, v___x_2602_);
lean_ctor_set(v___x_2608_, 2, v___x_2604_);
lean_ctor_set(v___x_2608_, 3, v___x_2607_);
v___x_2609_ = lean_array_push(v___x_2600_, v___x_2608_);
v___x_2610_ = lean_st_ref_put(v___y_2598_, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_sz_2601_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2612_, v___y_2613_);
lean_dec(v___y_2613_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2616_, lean_object* v_e_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2617_, v___y_2618_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2625_, lean_object* v_e_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2625_, v_e_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2634_, lean_object* v_todo_2635_, lean_object* v_e_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2634_, v_todo_2635_, v_e_2636_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2644_, lean_object* v_todo_2645_, lean_object* v_e_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v___x_3410__boxed_2653_; lean_object* v_res_2654_; 
v___x_3410__boxed_2653_ = lean_unbox(v___x_2644_);
v_res_2654_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_3410__boxed_2653_, v_todo_2645_, v_e_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2655_, lean_object* v_b_2656_, lean_object* v_x_2657_){
_start:
{
if (lean_obj_tag(v_x_2657_) == 0)
{
lean_dec(v_b_2656_);
lean_dec(v_a_2655_);
return v_x_2657_;
}
else
{
lean_object* v_key_2658_; lean_object* v_value_2659_; lean_object* v_tail_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2672_; 
v_key_2658_ = lean_ctor_get(v_x_2657_, 0);
v_value_2659_ = lean_ctor_get(v_x_2657_, 1);
v_tail_2660_ = lean_ctor_get(v_x_2657_, 2);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_x_2657_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2662_ = v_x_2657_;
v_isShared_2663_ = v_isSharedCheck_2672_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_tail_2660_);
lean_inc(v_value_2659_);
lean_inc(v_key_2658_);
lean_dec(v_x_2657_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2672_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint8_t v___x_2664_; 
v___x_2664_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2658_, v_a_2655_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2665_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2655_, v_b_2656_, v_tail_2660_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 2, v___x_2665_);
v___x_2667_ = v___x_2662_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_value_2659_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
else
{
lean_object* v___x_2670_; 
lean_dec(v_value_2659_);
lean_dec(v_key_2658_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v_b_2656_);
lean_ctor_set(v___x_2662_, 0, v_a_2655_);
v___x_2670_ = v___x_2662_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2655_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_b_2656_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_tail_2660_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2673_, lean_object* v_x_2674_){
_start:
{
if (lean_obj_tag(v_x_2674_) == 0)
{
uint8_t v___x_2675_; 
v___x_2675_ = 0;
return v___x_2675_;
}
else
{
lean_object* v_key_2676_; lean_object* v_tail_2677_; uint8_t v___x_2678_; 
v_key_2676_ = lean_ctor_get(v_x_2674_, 0);
v_tail_2677_ = lean_ctor_get(v_x_2674_, 2);
v___x_2678_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2676_, v_a_2673_);
if (v___x_2678_ == 0)
{
v_x_2674_ = v_tail_2677_;
goto _start;
}
else
{
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2680_, lean_object* v_x_2681_){
_start:
{
uint8_t v_res_2682_; lean_object* v_r_2683_; 
v_res_2682_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2680_, v_x_2681_);
lean_dec(v_x_2681_);
lean_dec(v_a_2680_);
v_r_2683_ = lean_box(v_res_2682_);
return v_r_2683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2684_, lean_object* v_x_2685_){
_start:
{
if (lean_obj_tag(v_x_2685_) == 0)
{
return v_x_2684_;
}
else
{
lean_object* v_key_2686_; lean_object* v_value_2687_; lean_object* v_tail_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2711_; 
v_key_2686_ = lean_ctor_get(v_x_2685_, 0);
v_value_2687_ = lean_ctor_get(v_x_2685_, 1);
v_tail_2688_ = lean_ctor_get(v_x_2685_, 2);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_x_2685_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2690_ = v_x_2685_;
v_isShared_2691_ = v_isSharedCheck_2711_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_tail_2688_);
lean_inc(v_value_2687_);
lean_inc(v_key_2686_);
lean_dec(v_x_2685_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2711_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; uint64_t v___x_2693_; uint64_t v___x_2694_; uint64_t v___x_2695_; uint64_t v_fold_2696_; uint64_t v___x_2697_; uint64_t v___x_2698_; uint64_t v___x_2699_; size_t v___x_2700_; size_t v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2692_ = lean_array_get_size(v_x_2684_);
v___x_2693_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2686_);
v___x_2694_ = 32ULL;
v___x_2695_ = lean_uint64_shift_right(v___x_2693_, v___x_2694_);
v_fold_2696_ = lean_uint64_xor(v___x_2693_, v___x_2695_);
v___x_2697_ = 16ULL;
v___x_2698_ = lean_uint64_shift_right(v_fold_2696_, v___x_2697_);
v___x_2699_ = lean_uint64_xor(v_fold_2696_, v___x_2698_);
v___x_2700_ = lean_uint64_to_usize(v___x_2699_);
v___x_2701_ = lean_usize_of_nat(v___x_2692_);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_sub(v___x_2701_, v___x_2702_);
v___x_2704_ = lean_usize_land(v___x_2700_, v___x_2703_);
v___x_2705_ = lean_array_uget_borrowed(v_x_2684_, v___x_2704_);
lean_inc(v___x_2705_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 2, v___x_2705_);
v___x_2707_ = v___x_2690_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_key_2686_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_value_2687_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_array_uset(v_x_2684_, v___x_2704_, v___x_2707_);
v_x_2684_ = v___x_2708_;
v_x_2685_ = v_tail_2688_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2712_, lean_object* v_source_2713_, lean_object* v_target_2714_){
_start:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = lean_array_get_size(v_source_2713_);
v___x_2716_ = lean_nat_dec_lt(v_i_2712_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_dec_ref(v_source_2713_);
lean_dec(v_i_2712_);
return v_target_2714_;
}
else
{
lean_object* v_es_2717_; lean_object* v___x_2718_; lean_object* v_source_2719_; lean_object* v_target_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_es_2717_ = lean_array_fget(v_source_2713_, v_i_2712_);
v___x_2718_ = lean_box(0);
v_source_2719_ = lean_array_fset(v_source_2713_, v_i_2712_, v___x_2718_);
v_target_2720_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2714_, v_es_2717_);
v___x_2721_ = lean_unsigned_to_nat(1u);
v___x_2722_ = lean_nat_add(v_i_2712_, v___x_2721_);
lean_dec(v_i_2712_);
v_i_2712_ = v___x_2722_;
v_source_2713_ = v_source_2719_;
v_target_2714_ = v_target_2720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2724_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v_nbuckets_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2725_ = lean_array_get_size(v_data_2724_);
v___x_2726_ = lean_unsigned_to_nat(2u);
v_nbuckets_2727_ = lean_nat_mul(v___x_2725_, v___x_2726_);
v___x_2728_ = lean_unsigned_to_nat(0u);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_mk_array(v_nbuckets_2727_, v___x_2729_);
v___x_2731_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2728_, v_data_2724_, v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2732_, lean_object* v_a_2733_, lean_object* v_b_2734_){
_start:
{
lean_object* v_size_2735_; lean_object* v_buckets_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2779_; 
v_size_2735_ = lean_ctor_get(v_m_2732_, 0);
v_buckets_2736_ = lean_ctor_get(v_m_2732_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_m_2732_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2738_ = v_m_2732_;
v_isShared_2739_ = v_isSharedCheck_2779_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_buckets_2736_);
lean_inc(v_size_2735_);
lean_dec(v_m_2732_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2779_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; uint64_t v___x_2741_; uint64_t v___x_2742_; uint64_t v___x_2743_; uint64_t v_fold_2744_; uint64_t v___x_2745_; uint64_t v___x_2746_; uint64_t v___x_2747_; size_t v___x_2748_; size_t v___x_2749_; size_t v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; lean_object* v_bkt_2753_; uint8_t v___x_2754_; 
v___x_2740_ = lean_array_get_size(v_buckets_2736_);
v___x_2741_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2733_);
v___x_2742_ = 32ULL;
v___x_2743_ = lean_uint64_shift_right(v___x_2741_, v___x_2742_);
v_fold_2744_ = lean_uint64_xor(v___x_2741_, v___x_2743_);
v___x_2745_ = 16ULL;
v___x_2746_ = lean_uint64_shift_right(v_fold_2744_, v___x_2745_);
v___x_2747_ = lean_uint64_xor(v_fold_2744_, v___x_2746_);
v___x_2748_ = lean_uint64_to_usize(v___x_2747_);
v___x_2749_ = lean_usize_of_nat(v___x_2740_);
v___x_2750_ = ((size_t)1ULL);
v___x_2751_ = lean_usize_sub(v___x_2749_, v___x_2750_);
v___x_2752_ = lean_usize_land(v___x_2748_, v___x_2751_);
v_bkt_2753_ = lean_array_uget_borrowed(v_buckets_2736_, v___x_2752_);
v___x_2754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2733_, v_bkt_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v_size_x27_2756_; lean_object* v___x_2757_; lean_object* v_buckets_x27_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2755_ = lean_unsigned_to_nat(1u);
v_size_x27_2756_ = lean_nat_add(v_size_2735_, v___x_2755_);
lean_dec(v_size_2735_);
lean_inc(v_bkt_2753_);
v___x_2757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2757_, 0, v_a_2733_);
lean_ctor_set(v___x_2757_, 1, v_b_2734_);
lean_ctor_set(v___x_2757_, 2, v_bkt_2753_);
v_buckets_x27_2758_ = lean_array_uset(v_buckets_2736_, v___x_2752_, v___x_2757_);
v___x_2759_ = lean_unsigned_to_nat(4u);
v___x_2760_ = lean_nat_mul(v_size_x27_2756_, v___x_2759_);
v___x_2761_ = lean_unsigned_to_nat(3u);
v___x_2762_ = lean_nat_div(v___x_2760_, v___x_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_array_get_size(v_buckets_x27_2758_);
v___x_2764_ = lean_nat_dec_le(v___x_2762_, v___x_2763_);
lean_dec(v___x_2762_);
if (v___x_2764_ == 0)
{
lean_object* v_val_2765_; lean_object* v___x_2767_; 
v_val_2765_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2758_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v_val_2765_);
lean_ctor_set(v___x_2738_, 0, v_size_x27_2756_);
v___x_2767_ = v___x_2738_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_size_x27_2756_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_val_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
else
{
lean_object* v___x_2770_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v_buckets_x27_2758_);
lean_ctor_set(v___x_2738_, 0, v_size_x27_2756_);
v___x_2770_ = v___x_2738_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_size_x27_2756_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_buckets_x27_2758_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
else
{
lean_object* v___x_2772_; lean_object* v_buckets_x27_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
lean_inc(v_bkt_2753_);
v___x_2772_ = lean_box(0);
v_buckets_x27_2773_ = lean_array_uset(v_buckets_2736_, v___x_2752_, v___x_2772_);
v___x_2774_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2733_, v_b_2734_, v_bkt_2753_);
v___x_2775_ = lean_array_uset(v_buckets_x27_2773_, v___x_2752_, v___x_2774_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v___x_2775_);
v___x_2777_ = v___x_2738_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_size_2735_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2780_, lean_object* v_x_2781_){
_start:
{
if (lean_obj_tag(v_x_2781_) == 0)
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_box(0);
return v___x_2782_;
}
else
{
lean_object* v_key_2783_; lean_object* v_value_2784_; lean_object* v_tail_2785_; uint8_t v___x_2786_; 
v_key_2783_ = lean_ctor_get(v_x_2781_, 0);
v_value_2784_ = lean_ctor_get(v_x_2781_, 1);
v_tail_2785_ = lean_ctor_get(v_x_2781_, 2);
v___x_2786_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2783_, v_a_2780_);
if (v___x_2786_ == 0)
{
v_x_2781_ = v_tail_2785_;
goto _start;
}
else
{
lean_object* v___x_2788_; 
lean_inc(v_value_2784_);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_value_2784_);
return v___x_2788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2789_, lean_object* v_x_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2789_, v_x_2790_);
lean_dec(v_x_2790_);
lean_dec(v_a_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_buckets_2794_; lean_object* v___x_2795_; uint64_t v___x_2796_; uint64_t v___x_2797_; uint64_t v___x_2798_; uint64_t v_fold_2799_; uint64_t v___x_2800_; uint64_t v___x_2801_; uint64_t v___x_2802_; size_t v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_buckets_2794_ = lean_ctor_get(v_m_2792_, 1);
v___x_2795_ = lean_array_get_size(v_buckets_2794_);
v___x_2796_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2793_);
v___x_2797_ = 32ULL;
v___x_2798_ = lean_uint64_shift_right(v___x_2796_, v___x_2797_);
v_fold_2799_ = lean_uint64_xor(v___x_2796_, v___x_2798_);
v___x_2800_ = 16ULL;
v___x_2801_ = lean_uint64_shift_right(v_fold_2799_, v___x_2800_);
v___x_2802_ = lean_uint64_xor(v_fold_2799_, v___x_2801_);
v___x_2803_ = lean_uint64_to_usize(v___x_2802_);
v___x_2804_ = lean_usize_of_nat(v___x_2795_);
v___x_2805_ = ((size_t)1ULL);
v___x_2806_ = lean_usize_sub(v___x_2804_, v___x_2805_);
v___x_2807_ = lean_usize_land(v___x_2803_, v___x_2806_);
v___x_2808_ = lean_array_uget_borrowed(v_buckets_2794_, v___x_2807_);
v___x_2809_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2793_, v___x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_m_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2813_, lean_object* v_entry_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_snd_2821_; lean_object* v_snd_2822_; lean_object* v_fst_2823_; lean_object* v_fst_2824_; lean_object* v_snd_2825_; lean_object* v_fst_2826_; lean_object* v_fst_2827_; lean_object* v_snd_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v_snd_2821_ = lean_ctor_get(v_p_2813_, 1);
v_snd_2822_ = lean_ctor_get(v_entry_2814_, 1);
lean_inc(v_snd_2822_);
v_fst_2823_ = lean_ctor_get(v_p_2813_, 0);
v_fst_2824_ = lean_ctor_get(v_snd_2821_, 0);
v_snd_2825_ = lean_ctor_get(v_snd_2821_, 1);
v_fst_2826_ = lean_ctor_get(v_entry_2814_, 0);
lean_inc(v_fst_2826_);
lean_dec_ref(v_entry_2814_);
v_fst_2827_ = lean_ctor_get(v_snd_2822_, 0);
lean_inc(v_fst_2827_);
v_snd_2828_ = lean_ctor_get(v_snd_2822_, 1);
v___x_2829_ = lean_array_get_size(v_fst_2826_);
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = lean_nat_dec_eq(v___x_2829_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v_fst_2832_; lean_object* v_snd_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2938_; 
v_fst_2832_ = lean_ctor_get(v_fst_2827_, 0);
v_snd_2833_ = lean_ctor_get(v_fst_2827_, 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_fst_2827_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2835_ = v_fst_2827_;
v_isShared_2836_ = v_isSharedCheck_2938_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_snd_2833_);
lean_inc(v_fst_2832_);
lean_dec(v_fst_2827_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2938_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v_e_2840_; lean_object* v_todo_2841_; lean_object* v___x_2842_; lean_object* v___f_2843_; lean_object* v___x_2844_; 
v___x_2837_ = l_Lean_instInhabitedExpr;
v___x_2838_ = lean_unsigned_to_nat(1u);
v___x_2839_ = lean_nat_sub(v___x_2829_, v___x_2838_);
v_e_2840_ = lean_array_get(v___x_2837_, v_fst_2826_, v___x_2839_);
lean_dec(v___x_2839_);
v_todo_2841_ = lean_array_pop(v_fst_2826_);
v___x_2842_ = lean_box(v___x_2831_);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2843_, 0, v___x_2842_);
lean_closure_set(v___f_2843_, 1, v_todo_2841_);
lean_closure_set(v___f_2843_, 2, v_e_2840_);
v___x_2844_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2832_, v_snd_2833_, v___f_2843_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v_fst_2846_; lean_object* v_snd_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2929_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v_fst_2846_ = lean_ctor_get(v_a_2845_, 0);
v_snd_2847_ = lean_ctor_get(v_a_2845_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_a_2845_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2849_ = v_a_2845_;
v_isShared_2850_ = v_isSharedCheck_2929_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_snd_2847_);
lean_inc(v_fst_2846_);
lean_dec(v_a_2845_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2929_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = lean_box(3);
v___x_2852_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2846_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2825_, v_fst_2846_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2855_; 
lean_inc(v_snd_2825_);
lean_inc(v_fst_2824_);
lean_inc(v_fst_2823_);
lean_dec_ref(v_p_2813_);
lean_inc(v_snd_2822_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v_snd_2822_);
lean_ctor_set(v___x_2849_, 0, v_snd_2847_);
v___x_2855_ = v___x_2849_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_snd_2847_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_snd_2822_);
v___x_2855_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2875_; 
v_isSharedCheck_2875_ = !lean_is_exclusive(v_snd_2822_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; lean_object* v_unused_2877_; 
v_unused_2876_ = lean_ctor_get(v_snd_2822_, 1);
lean_dec(v_unused_2876_);
v_unused_2877_ = lean_ctor_get(v_snd_2822_, 0);
lean_dec(v_unused_2877_);
v___x_2857_ = v_snd_2822_;
v_isShared_2858_ = v_isSharedCheck_2875_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v_snd_2822_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2875_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2874_; 
v___x_2859_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2855_, v_a_2815_);
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2874_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2874_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2825_, v_fst_2846_, v_a_2860_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v___x_2864_);
lean_ctor_set(v___x_2835_, 0, v_fst_2824_);
v___x_2866_ = v___x_2835_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_fst_2824_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2868_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v___x_2866_);
lean_ctor_set(v___x_2857_, 0, v_fst_2823_);
v___x_2868_ = v___x_2857_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_fst_2823_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2868_);
v___x_2870_ = v___x_2862_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2879_; lean_object* v___x_2881_; 
lean_dec(v_fst_2846_);
lean_del_object(v___x_2835_);
v_val_2879_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v___x_2853_, 1);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v_snd_2822_);
lean_ctor_set(v___x_2849_, 0, v_snd_2847_);
v___x_2881_ = v___x_2849_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_snd_2847_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_snd_2822_);
v___x_2881_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
v___x_2882_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2879_, v___x_2881_, v_a_2815_);
lean_dec(v_val_2879_);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; 
v_unused_2890_ = lean_ctor_get(v___x_2882_, 0);
lean_dec(v_unused_2890_);
v___x_2884_ = v___x_2882_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v___x_2882_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v_p_2813_);
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_p_2813_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
else
{
uint8_t v___x_2892_; 
lean_dec(v_fst_2846_);
v___x_2892_ = lean_nat_dec_eq(v_fst_2824_, v___x_2830_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2894_; 
lean_del_object(v___x_2835_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v_snd_2822_);
lean_ctor_set(v___x_2849_, 0, v_snd_2847_);
v___x_2894_ = v___x_2849_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_snd_2847_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_snd_2822_);
v___x_2894_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
v___x_2895_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2824_, v___x_2894_, v_a_2815_);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2902_ == 0)
{
lean_object* v_unused_2903_; 
v_unused_2903_ = lean_ctor_get(v___x_2895_, 0);
lean_dec(v_unused_2903_);
v___x_2897_ = v___x_2895_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_dec(v___x_2895_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v_p_2813_);
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_p_2813_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
else
{
lean_object* v___x_2906_; 
lean_inc(v_snd_2825_);
lean_inc(v_fst_2823_);
lean_dec_ref(v_p_2813_);
lean_inc(v_snd_2822_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v_snd_2822_);
lean_ctor_set(v___x_2849_, 0, v_snd_2847_);
v___x_2906_ = v___x_2849_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_snd_2847_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_snd_2822_);
v___x_2906_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2925_; 
v_isSharedCheck_2925_ = !lean_is_exclusive(v_snd_2822_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; lean_object* v_unused_2927_; 
v_unused_2926_ = lean_ctor_get(v_snd_2822_, 1);
lean_dec(v_unused_2926_);
v_unused_2927_ = lean_ctor_get(v_snd_2822_, 0);
lean_dec(v_unused_2927_);
v___x_2908_ = v_snd_2822_;
v_isShared_2909_ = v_isSharedCheck_2925_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v_snd_2822_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2925_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2924_; 
v___x_2910_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2906_, v_a_2815_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2924_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2924_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v_snd_2825_);
lean_ctor_set(v___x_2835_, 0, v_a_2911_);
v___x_2916_ = v___x_2835_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2911_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_snd_2825_);
v___x_2916_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 1, v___x_2916_);
lean_ctor_set(v___x_2908_, 0, v_fst_2823_);
v___x_2918_ = v___x_2908_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_fst_2823_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2920_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2918_);
v___x_2920_ = v___x_2913_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
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
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_del_object(v___x_2835_);
lean_dec(v_snd_2822_);
lean_dec_ref(v_p_2813_);
v_a_2930_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2844_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2844_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
else
{
lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2947_; 
lean_inc(v_snd_2828_);
lean_inc(v_fst_2823_);
lean_inc(v_snd_2821_);
lean_dec(v_fst_2827_);
lean_dec(v_fst_2826_);
lean_dec_ref(v_p_2813_);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_snd_2822_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; lean_object* v_unused_2949_; 
v_unused_2948_ = lean_ctor_get(v_snd_2822_, 1);
lean_dec(v_unused_2948_);
v_unused_2949_ = lean_ctor_get(v_snd_2822_, 0);
lean_dec(v_unused_2949_);
v___x_2940_ = v_snd_2822_;
v_isShared_2941_ = v_isSharedCheck_2947_;
goto v_resetjp_2939_;
}
else
{
lean_dec(v_snd_2822_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2947_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_values_2942_; lean_object* v___x_2944_; 
v_values_2942_ = lean_array_push(v_fst_2823_, v_snd_2828_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v_snd_2821_);
lean_ctor_set(v___x_2940_, 0, v_values_2942_);
v___x_2944_ = v___x_2940_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_values_2942_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_snd_2821_);
v___x_2944_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
return v___x_2945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2950_, lean_object* v_entry_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2950_, v_entry_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2959_, lean_object* v_p_2960_, lean_object* v_entry_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2960_, v_entry_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2969_, lean_object* v_p_2970_, lean_object* v_entry_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2969_, v_p_2970_, v_entry_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
lean_dec(v_a_2972_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2979_, lean_object* v_m_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2980_, v_a_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2983_, lean_object* v_m_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2983_, v_m_2984_, v_a_2985_);
lean_dec(v_a_2985_);
lean_dec_ref(v_m_2984_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2987_, lean_object* v_m_2988_, lean_object* v_a_2989_, lean_object* v_b_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2988_, v_a_2989_, v_b_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2992_, lean_object* v_a_2993_, lean_object* v_x_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2993_, v_x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2996_, lean_object* v_a_2997_, lean_object* v_x_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2996_, v_a_2997_, v_x_2998_);
lean_dec(v_x_2998_);
lean_dec(v_a_2997_);
return v_res_2999_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_3000_, lean_object* v_a_3001_, lean_object* v_x_3002_){
_start:
{
uint8_t v___x_3003_; 
v___x_3003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_3001_, v_x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3004_, lean_object* v_a_3005_, lean_object* v_x_3006_){
_start:
{
uint8_t v_res_3007_; lean_object* v_r_3008_; 
v_res_3007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_3004_, v_a_3005_, v_x_3006_);
lean_dec(v_x_3006_);
lean_dec(v_a_3005_);
v_r_3008_ = lean_box(v_res_3007_);
return v_r_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_3009_, lean_object* v_data_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_3012_, lean_object* v_a_3013_, lean_object* v_b_3014_, lean_object* v_x_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_3013_, v_b_3014_, v_x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_3017_, lean_object* v_i_3018_, lean_object* v_source_3019_, lean_object* v_target_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_3018_, v_source_3019_, v_target_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_3022_, lean_object* v_x_3023_, lean_object* v_x_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_3023_, v_x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3026_, size_t v_i_3027_, size_t v_stop_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_eq(v_i_3027_, v_stop_3028_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_array_uget_borrowed(v_as_3026_, v_i_3027_);
lean_inc(v___x_3037_);
v___x_3038_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3029_, v___x_3037_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; size_t v___x_3040_; size_t v___x_3041_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = ((size_t)1ULL);
v___x_3041_ = lean_usize_add(v_i_3027_, v___x_3040_);
v_i_3027_ = v___x_3041_;
v_b_3029_ = v_a_3039_;
goto _start;
}
else
{
return v___x_3038_;
}
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_b_3029_);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3044_, lean_object* v_i_3045_, lean_object* v_stop_3046_, lean_object* v_b_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
size_t v_i_boxed_3054_; size_t v_stop_boxed_3055_; lean_object* v_res_3056_; 
v_i_boxed_3054_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_stop_boxed_3055_ = lean_unbox_usize(v_stop_3046_);
lean_dec(v_stop_3046_);
v_res_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3044_, v_i_boxed_3054_, v_stop_boxed_3055_, v_b_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v_as_3044_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3057_, lean_object* v_starIdx_3058_, lean_object* v_children_3059_, lean_object* v_entries_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_starIdx_3058_);
lean_ctor_set(v___x_3067_, 1, v_children_3059_);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v_values_3057_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_array_get_size(v_entries_3060_);
v___x_3071_ = lean_nat_dec_lt(v___x_3069_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3068_);
return v___x_3072_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_nat_dec_le(v___x_3070_, v___x_3070_);
if (v___x_3073_ == 0)
{
if (v___x_3071_ == 0)
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3068_);
return v___x_3074_;
}
else
{
size_t v___x_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((size_t)0ULL);
v___x_3076_ = lean_usize_of_nat(v___x_3070_);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3060_, v___x_3075_, v___x_3076_, v___x_3068_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v___x_3077_;
}
}
else
{
size_t v___x_3078_; size_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((size_t)0ULL);
v___x_3079_ = lean_usize_of_nat(v___x_3070_);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3060_, v___x_3078_, v___x_3079_, v___x_3068_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v___x_3080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3081_, lean_object* v_starIdx_3082_, lean_object* v_children_3083_, lean_object* v_entries_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3081_, v_starIdx_3082_, v_children_3083_, v_entries_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_entries_3084_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3092_, lean_object* v_values_3093_, lean_object* v_starIdx_3094_, lean_object* v_children_3095_, lean_object* v_entries_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3093_, v_starIdx_3094_, v_children_3095_, v_entries_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_values_3105_, lean_object* v_starIdx_3106_, lean_object* v_children_3107_, lean_object* v_entries_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3104_, v_values_3105_, v_starIdx_3106_, v_children_3107_, v_entries_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
lean_dec_ref(v_entries_3108_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3116_, lean_object* v_as_3117_, size_t v_i_3118_, size_t v_stop_3119_, lean_object* v_b_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3117_, v_i_3118_, v_stop_3119_, v_b_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3128_, lean_object* v_as_3129_, lean_object* v_i_3130_, lean_object* v_stop_3131_, lean_object* v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
size_t v_i_boxed_3139_; size_t v_stop_boxed_3140_; lean_object* v_res_3141_; 
v_i_boxed_3139_ = lean_unbox_usize(v_i_3130_);
lean_dec(v_i_3130_);
v_stop_boxed_3140_ = lean_unbox_usize(v_stop_3131_);
lean_dec(v_stop_3131_);
v_res_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3128_, v_as_3129_, v_i_boxed_3139_, v_stop_boxed_3140_, v_b_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v_as_3129_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_values_3152_; lean_object* v_star_3153_; lean_object* v_children_3154_; lean_object* v_pending_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3185_; 
v___x_3149_ = lean_st_ref_get(v_a_3143_);
v___x_3150_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3151_ = lean_array_get(v___x_3150_, v___x_3149_, v_c_3142_);
lean_dec(v___x_3149_);
v_values_3152_ = lean_ctor_get(v___x_3151_, 0);
v_star_3153_ = lean_ctor_get(v___x_3151_, 1);
v_children_3154_ = lean_ctor_get(v___x_3151_, 2);
v_pending_3155_ = lean_ctor_get(v___x_3151_, 3);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3157_ = v___x_3151_;
v_isShared_3158_ = v_isSharedCheck_3185_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_pending_3155_);
lean_inc(v_children_3154_);
lean_inc(v_star_3153_);
lean_inc(v_values_3152_);
lean_dec(v___x_3151_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3185_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3159_ = lean_array_get_size(v_pending_3155_);
v___x_3160_ = lean_unsigned_to_nat(0u);
v___x_3161_ = lean_nat_dec_eq(v___x_3159_, v___x_3160_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3142_, v___x_3150_, v_a_3143_);
lean_dec_ref(v___x_3162_);
v___x_3163_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3152_, v_star_3153_, v_children_3154_, v_pending_3155_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
lean_dec_ref(v_pending_3155_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v_snd_3165_; lean_object* v_fst_3166_; lean_object* v_fst_3167_; lean_object* v_snd_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v_snd_3165_ = lean_ctor_get(v_a_3164_, 1);
v_fst_3166_ = lean_ctor_get(v_a_3164_, 0);
v_fst_3167_ = lean_ctor_get(v_snd_3165_, 0);
v_snd_3168_ = lean_ctor_get(v_snd_3165_, 1);
v___x_3169_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
lean_inc(v_snd_3168_);
lean_inc(v_fst_3167_);
lean_inc(v_fst_3166_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 3, v___x_3169_);
lean_ctor_set(v___x_3157_, 2, v_snd_3168_);
lean_ctor_set(v___x_3157_, 1, v_fst_3167_);
lean_ctor_set(v___x_3157_, 0, v_fst_3166_);
v___x_3171_ = v___x_3157_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_fst_3166_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_fst_3167_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_snd_3168_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
v___x_3172_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3142_, v___x_3171_, v_a_3143_);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; 
v_unused_3180_ = lean_ctor_get(v___x_3172_, 0);
lean_dec(v_unused_3180_);
v___x_3174_ = v___x_3172_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_dec(v___x_3172_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v_a_3164_);
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3164_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_del_object(v___x_3157_);
return v___x_3163_;
}
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_del_object(v___x_3157_);
lean_dec_ref(v_pending_3155_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_star_3153_);
lean_ctor_set(v___x_3182_, 1, v_children_3154_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_values_3152_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
return v___x_3184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec(v_c_3186_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3194_, lean_object* v_c_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3203_, lean_object* v_c_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3203_, v_c_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec(v_c_3204_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3212_, lean_object* v_fallback_3213_, lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3214_) == 0)
{
lean_inc(v_fallback_3213_);
return v_fallback_3213_;
}
else
{
lean_object* v_key_3215_; lean_object* v_value_3216_; lean_object* v_tail_3217_; uint8_t v___x_3218_; 
v_key_3215_ = lean_ctor_get(v_x_3214_, 0);
v_value_3216_ = lean_ctor_get(v_x_3214_, 1);
v_tail_3217_ = lean_ctor_get(v_x_3214_, 2);
v___x_3218_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3215_, v_a_3212_);
if (v___x_3218_ == 0)
{
v_x_3214_ = v_tail_3217_;
goto _start;
}
else
{
lean_inc(v_value_3216_);
return v_value_3216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3220_, lean_object* v_fallback_3221_, lean_object* v_x_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3220_, v_fallback_3221_, v_x_3222_);
lean_dec(v_x_3222_);
lean_dec(v_fallback_3221_);
lean_dec(v_a_3220_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3224_, lean_object* v_a_3225_, lean_object* v_fallback_3226_){
_start:
{
lean_object* v_buckets_3227_; lean_object* v___x_3228_; uint64_t v___x_3229_; uint64_t v___x_3230_; uint64_t v___x_3231_; uint64_t v_fold_3232_; uint64_t v___x_3233_; uint64_t v___x_3234_; uint64_t v___x_3235_; size_t v___x_3236_; size_t v___x_3237_; size_t v___x_3238_; size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_buckets_3227_ = lean_ctor_get(v_m_3224_, 1);
v___x_3228_ = lean_array_get_size(v_buckets_3227_);
v___x_3229_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3225_);
v___x_3230_ = 32ULL;
v___x_3231_ = lean_uint64_shift_right(v___x_3229_, v___x_3230_);
v_fold_3232_ = lean_uint64_xor(v___x_3229_, v___x_3231_);
v___x_3233_ = 16ULL;
v___x_3234_ = lean_uint64_shift_right(v_fold_3232_, v___x_3233_);
v___x_3235_ = lean_uint64_xor(v_fold_3232_, v___x_3234_);
v___x_3236_ = lean_uint64_to_usize(v___x_3235_);
v___x_3237_ = lean_usize_of_nat(v___x_3228_);
v___x_3238_ = ((size_t)1ULL);
v___x_3239_ = lean_usize_sub(v___x_3237_, v___x_3238_);
v___x_3240_ = lean_usize_land(v___x_3236_, v___x_3239_);
v___x_3241_ = lean_array_uget_borrowed(v_buckets_3227_, v___x_3240_);
v___x_3242_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3225_, v_fallback_3226_, v___x_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3243_, lean_object* v_a_3244_, lean_object* v_fallback_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3243_, v_a_3244_, v_fallback_3245_);
lean_dec(v_fallback_3245_);
lean_dec(v_a_3244_);
lean_dec_ref(v_m_3243_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3247_, lean_object* v_rest_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = lean_unsigned_to_nat(0u);
v___x_3256_ = lean_nat_dec_eq(v_next_3247_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3247_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3283_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3283_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3283_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_snd_3262_; 
v_snd_3262_ = lean_ctor_get(v_a_3258_, 1);
lean_inc(v_snd_3262_);
lean_dec(v_a_3258_);
if (lean_obj_tag(v_rest_3248_) == 0)
{
lean_object* v_fst_3263_; lean_object* v_snd_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v_fst_3263_ = lean_ctor_get(v_snd_3262_, 0);
lean_inc(v_fst_3263_);
v_snd_3264_ = lean_ctor_get(v_snd_3262_, 1);
lean_inc(v_snd_3264_);
lean_dec(v_snd_3262_);
v___x_3265_ = lean_st_ref_take(v_a_3249_);
v___x_3266_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v_fst_3263_);
lean_ctor_set(v___x_3267_, 2, v_snd_3264_);
lean_ctor_set(v___x_3267_, 3, v___x_3266_);
v___x_3268_ = lean_array_set(v___x_3265_, v_next_3247_, v___x_3267_);
lean_dec(v_next_3247_);
v___x_3269_ = lean_st_ref_put(v_a_3249_, v___x_3268_);
v___x_3270_ = lean_box(0);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3270_);
v___x_3272_ = v___x_3260_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
else
{
lean_object* v_fst_3274_; lean_object* v_snd_3275_; lean_object* v_head_3276_; lean_object* v_tail_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
lean_del_object(v___x_3260_);
lean_dec(v_next_3247_);
v_fst_3274_ = lean_ctor_get(v_snd_3262_, 0);
lean_inc(v_fst_3274_);
v_snd_3275_ = lean_ctor_get(v_snd_3262_, 1);
lean_inc(v_snd_3275_);
lean_dec(v_snd_3262_);
v_head_3276_ = lean_ctor_get(v_rest_3248_, 0);
v_tail_3277_ = lean_ctor_get(v_rest_3248_, 1);
v___x_3278_ = lean_box(3);
v___x_3279_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3276_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
lean_dec(v_fst_3274_);
v___x_3280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3275_, v_head_3276_, v___x_3255_);
lean_dec(v_snd_3275_);
v_next_3247_ = v___x_3280_;
v_rest_3248_ = v_tail_3277_;
goto _start;
}
else
{
lean_dec(v_snd_3275_);
v_next_3247_ = v_fst_3274_;
v_rest_3248_ = v_tail_3277_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_next_3247_);
v_a_3284_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3257_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3257_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec(v_next_3247_);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3294_, lean_object* v_rest_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3294_, v_rest_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec(v_rest_3295_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3303_, lean_object* v_next_3304_, lean_object* v_rest_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3304_, v_rest_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3313_, lean_object* v_next_3314_, lean_object* v_rest_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3313_, v_next_3314_, v_rest_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec(v_rest_3315_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3323_, lean_object* v_m_3324_, lean_object* v_a_3325_, lean_object* v_fallback_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3324_, v_a_3325_, v_fallback_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_m_3329_, lean_object* v_a_3330_, lean_object* v_fallback_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3328_, v_m_3329_, v_a_3330_, v_fallback_3331_);
lean_dec(v_fallback_3331_);
lean_dec(v_a_3330_);
lean_dec_ref(v_m_3329_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3333_, lean_object* v_a_3334_, lean_object* v_fallback_3335_, lean_object* v_x_3336_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3334_, v_fallback_3335_, v_x_3336_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3338_, lean_object* v_a_3339_, lean_object* v_fallback_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3338_, v_a_3339_, v_fallback_3340_, v_x_3341_);
lean_dec(v_x_3341_);
lean_dec(v_fallback_3340_);
lean_dec(v_a_3339_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3343_, lean_object* v_path_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
if (lean_obj_tag(v_path_3344_) == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_t_3343_);
return v___x_3350_;
}
else
{
lean_object* v_head_3351_; lean_object* v_tail_3352_; lean_object* v_roots_3353_; lean_object* v___x_3354_; lean_object* v_idx_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_head_3351_ = lean_ctor_get(v_path_3344_, 0);
lean_inc(v_head_3351_);
v_tail_3352_ = lean_ctor_get(v_path_3344_, 1);
lean_inc(v_tail_3352_);
lean_dec_ref_known(v_path_3344_, 2);
v_roots_3353_ = lean_ctor_get(v_t_3343_, 1);
v___x_3354_ = lean_unsigned_to_nat(0u);
v_idx_3355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3353_, v_head_3351_, v___x_3354_);
lean_dec(v_head_3351_);
v___x_3356_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3356_, 0, lean_box(0));
lean_closure_set(v___x_3356_, 1, v_idx_3355_);
lean_closure_set(v___x_3356_, 2, v_tail_3352_);
v___x_3357_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3343_, v___x_3356_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3366_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_snd_3362_; lean_object* v___x_3364_; 
v_snd_3362_ = lean_ctor_get(v_a_3358_, 1);
lean_inc(v_snd_3362_);
lean_dec(v_a_3358_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v_snd_3362_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_snd_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3357_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3357_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3375_, lean_object* v_path_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3375_, v_path_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3383_, lean_object* v_t_3384_, lean_object* v_path_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3384_, v_path_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3392_, lean_object* v_t_3393_, lean_object* v_path_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3392_, v_t_3393_, v_path_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3403_, lean_object* v_e_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = lean_array_get_size(v_a_3405_);
v___x_3407_ = lean_nat_dec_lt(v___x_3406_, v_score_3403_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_mk_empty_array_with_capacity(v___x_3408_);
v___x_3410_ = lean_array_push(v___x_3409_, v_e_3404_);
v___x_3411_ = lean_array_push(v_a_3405_, v___x_3410_);
return v___x_3411_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3413_ = lean_array_push(v_a_3405_, v___x_3412_);
v_a_3405_ = v___x_3413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3415_, lean_object* v_e_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3415_, v_e_3416_, v_a_3417_);
lean_dec(v_score_3415_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3419_, lean_object* v_score_3420_, lean_object* v_e_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3420_, v_e_3421_, v_a_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3424_, lean_object* v_score_3425_, lean_object* v_e_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3424_, v_score_3425_, v_e_3426_, v_a_3427_);
lean_dec(v_score_3425_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3429_, lean_object* v_score_3430_, lean_object* v_e_3431_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3432_ = lean_array_get_size(v_e_3431_);
v___x_3433_ = lean_unsigned_to_nat(0u);
v___x_3434_ = lean_nat_dec_eq(v___x_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3435_ = lean_array_get_size(v_r_3429_);
v___x_3436_ = lean_nat_dec_lt(v_score_3430_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
v___x_3437_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3430_, v_e_3431_, v_r_3429_);
return v___x_3437_;
}
else
{
if (v___x_3436_ == 0)
{
lean_dec_ref(v_e_3431_);
return v_r_3429_;
}
else
{
lean_object* v_v_3438_; lean_object* v___x_3439_; lean_object* v_xs_x27_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_v_3438_ = lean_array_fget(v_r_3429_, v_score_3430_);
v___x_3439_ = lean_box(0);
v_xs_x27_3440_ = lean_array_fset(v_r_3429_, v_score_3430_, v___x_3439_);
v___x_3441_ = lean_array_push(v_v_3438_, v_e_3431_);
v___x_3442_ = lean_array_fset(v_xs_x27_3440_, v_score_3430_, v___x_3441_);
return v___x_3442_;
}
}
}
else
{
lean_dec_ref(v_e_3431_);
return v_r_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3443_, lean_object* v_score_3444_, lean_object* v_e_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3443_, v_score_3444_, v_e_3445_);
lean_dec(v_score_3444_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3447_, lean_object* v_r_3448_, lean_object* v_score_3449_, lean_object* v_e_3450_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3448_, v_score_3449_, v_e_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3452_, lean_object* v_r_3453_, lean_object* v_score_3454_, lean_object* v_e_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3452_, v_r_3453_, v_score_3454_, v_e_3455_);
lean_dec(v_score_3454_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3457_, size_t v_i_3458_, size_t v_stop_3459_, lean_object* v_b_3460_){
_start:
{
uint8_t v___x_3461_; 
v___x_3461_ = lean_usize_dec_eq(v_i_3458_, v_stop_3459_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; size_t v___x_3465_; size_t v___x_3466_; 
v___x_3462_ = lean_array_uget_borrowed(v_as_3457_, v_i_3458_);
v___x_3463_ = lean_array_get_size(v___x_3462_);
v___x_3464_ = lean_nat_add(v_b_3460_, v___x_3463_);
lean_dec(v_b_3460_);
v___x_3465_ = ((size_t)1ULL);
v___x_3466_ = lean_usize_add(v_i_3458_, v___x_3465_);
v_i_3458_ = v___x_3466_;
v_b_3460_ = v___x_3464_;
goto _start;
}
else
{
return v_b_3460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3468_, lean_object* v_i_3469_, lean_object* v_stop_3470_, lean_object* v_b_3471_){
_start:
{
size_t v_i_boxed_3472_; size_t v_stop_boxed_3473_; lean_object* v_res_3474_; 
v_i_boxed_3472_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_stop_boxed_3473_ = lean_unbox_usize(v_stop_3470_);
lean_dec(v_stop_3470_);
v_res_3474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3468_, v_i_boxed_3472_, v_stop_boxed_3473_, v_b_3471_);
lean_dec_ref(v_as_3468_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3475_, size_t v_i_3476_, size_t v_stop_3477_, lean_object* v_b_3478_){
_start:
{
lean_object* v___y_3480_; uint8_t v___x_3484_; 
v___x_3484_ = lean_usize_dec_eq(v_i_3476_, v_stop_3477_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3485_ = lean_array_uget_borrowed(v_as_3475_, v_i_3476_);
v___x_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = lean_array_get_size(v___x_3485_);
v___x_3488_ = lean_nat_dec_lt(v___x_3486_, v___x_3487_);
if (v___x_3488_ == 0)
{
v___y_3480_ = v_b_3478_;
goto v___jp_3479_;
}
else
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_nat_dec_le(v___x_3487_, v___x_3487_);
if (v___x_3489_ == 0)
{
if (v___x_3488_ == 0)
{
v___y_3480_ = v_b_3478_;
goto v___jp_3479_;
}
else
{
size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = lean_usize_of_nat(v___x_3487_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3485_, v___x_3490_, v___x_3491_, v_b_3478_);
v___y_3480_ = v___x_3492_;
goto v___jp_3479_;
}
}
else
{
size_t v___x_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = ((size_t)0ULL);
v___x_3494_ = lean_usize_of_nat(v___x_3487_);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3485_, v___x_3493_, v___x_3494_, v_b_3478_);
v___y_3480_ = v___x_3495_;
goto v___jp_3479_;
}
}
}
else
{
return v_b_3478_;
}
v___jp_3479_:
{
size_t v___x_3481_; size_t v___x_3482_; 
v___x_3481_ = ((size_t)1ULL);
v___x_3482_ = lean_usize_add(v_i_3476_, v___x_3481_);
v_i_3476_ = v___x_3482_;
v_b_3478_ = v___y_3480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3496_, lean_object* v_i_3497_, lean_object* v_stop_3498_, lean_object* v_b_3499_){
_start:
{
size_t v_i_boxed_3500_; size_t v_stop_boxed_3501_; lean_object* v_res_3502_; 
v_i_boxed_3500_ = lean_unbox_usize(v_i_3497_);
lean_dec(v_i_3497_);
v_stop_boxed_3501_ = lean_unbox_usize(v_stop_3498_);
lean_dec(v_stop_3498_);
v_res_3502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3496_, v_i_boxed_3500_, v_stop_boxed_3501_, v_b_3499_);
lean_dec_ref(v_as_3496_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3503_){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3504_ = lean_unsigned_to_nat(0u);
v___x_3505_ = lean_array_get_size(v_mr_3503_);
v___x_3506_ = lean_nat_dec_lt(v___x_3504_, v___x_3505_);
if (v___x_3506_ == 0)
{
return v___x_3504_;
}
else
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_nat_dec_le(v___x_3505_, v___x_3505_);
if (v___x_3507_ == 0)
{
if (v___x_3506_ == 0)
{
return v___x_3504_;
}
else
{
size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v___x_3508_ = ((size_t)0ULL);
v___x_3509_ = lean_usize_of_nat(v___x_3505_);
v___x_3510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3503_, v___x_3508_, v___x_3509_, v___x_3504_);
return v___x_3510_;
}
}
else
{
size_t v___x_3511_; size_t v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = ((size_t)0ULL);
v___x_3512_ = lean_usize_of_nat(v___x_3505_);
v___x_3513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3503_, v___x_3511_, v___x_3512_, v___x_3504_);
return v___x_3513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3514_);
lean_dec_ref(v_mr_3514_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3516_, lean_object* v_mr_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3519_, lean_object* v_mr_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3519_, v_mr_3520_);
lean_dec_ref(v_mr_3520_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3522_, lean_object* v_as_3523_, size_t v_i_3524_, size_t v_stop_3525_, lean_object* v_b_3526_){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3523_, v_i_3524_, v_stop_3525_, v_b_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3528_, lean_object* v_as_3529_, lean_object* v_i_3530_, lean_object* v_stop_3531_, lean_object* v_b_3532_){
_start:
{
size_t v_i_boxed_3533_; size_t v_stop_boxed_3534_; lean_object* v_res_3535_; 
v_i_boxed_3533_ = lean_unbox_usize(v_i_3530_);
lean_dec(v_i_3530_);
v_stop_boxed_3534_ = lean_unbox_usize(v_stop_3531_);
lean_dec(v_stop_3531_);
v_res_3535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3528_, v_as_3529_, v_i_boxed_3533_, v_stop_boxed_3534_, v_b_3532_);
lean_dec_ref(v_as_3529_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3536_, lean_object* v_as_3537_, size_t v_i_3538_, size_t v_stop_3539_, lean_object* v_b_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3537_, v_i_3538_, v_stop_3539_, v_b_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_as_3543_, lean_object* v_i_3544_, lean_object* v_stop_3545_, lean_object* v_b_3546_){
_start:
{
size_t v_i_boxed_3547_; size_t v_stop_boxed_3548_; lean_object* v_res_3549_; 
v_i_boxed_3547_ = lean_unbox_usize(v_i_3544_);
lean_dec(v_i_3544_);
v_stop_boxed_3548_ = lean_unbox_usize(v_stop_3545_);
lean_dec(v_stop_3545_);
v_res_3549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3542_, v_as_3543_, v_i_boxed_3547_, v_stop_boxed_3548_, v_b_3546_);
lean_dec_ref(v_as_3543_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3550_, lean_object* v_j_3551_, lean_object* v_x_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_apply_2(v_f_3550_, v_j_3551_, v_x_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3573_, lean_object* v_x1_3574_, lean_object* v_x2_3575_){
_start:
{
lean_object* v___x_3576_; size_t v_sz_3577_; size_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3576_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3577_ = lean_array_size(v_x2_3575_);
v___x_3578_ = ((size_t)0ULL);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3576_, v___f_3573_, v_sz_3577_, v___x_3578_, v_x2_3575_);
v___x_3580_ = l_Array_append___redArg(v_x1_3574_, v___x_3579_);
lean_dec(v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3581_, lean_object* v_mr_3582_, lean_object* v_f_3583_, lean_object* v_i_3584_, lean_object* v_x_3585_, lean_object* v_r_3586_){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v_j_3589_; lean_object* v_b_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3587_ = lean_unsigned_to_nat(1u);
v___x_3588_ = lean_nat_sub(v_n_3581_, v___x_3587_);
v_j_3589_ = lean_nat_sub(v___x_3588_, v_i_3584_);
lean_dec(v___x_3588_);
v_b_3590_ = lean_array_fget_borrowed(v_mr_3582_, v_j_3589_);
v___x_3591_ = lean_unsigned_to_nat(0u);
v___x_3592_ = lean_array_get_size(v_b_3590_);
v___x_3593_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3594_ = lean_nat_dec_lt(v___x_3591_, v___x_3592_);
if (v___x_3594_ == 0)
{
lean_dec(v_j_3589_);
lean_dec(v_f_3583_);
return v_r_3586_;
}
else
{
lean_object* v___f_3595_; lean_object* v___f_3596_; uint8_t v___x_3597_; 
v___f_3595_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3595_, 0, v_f_3583_);
lean_closure_set(v___f_3595_, 1, v_j_3589_);
v___f_3596_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3596_, 0, v___f_3595_);
v___x_3597_ = lean_nat_dec_le(v___x_3592_, v___x_3592_);
if (v___x_3597_ == 0)
{
if (v___x_3594_ == 0)
{
lean_dec_ref(v___f_3596_);
return v_r_3586_;
}
else
{
size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = ((size_t)0ULL);
v___x_3599_ = lean_usize_of_nat(v___x_3592_);
lean_inc(v_b_3590_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3593_, v___f_3596_, v_b_3590_, v___x_3598_, v___x_3599_, v_r_3586_);
return v___x_3600_;
}
}
else
{
size_t v___x_3601_; size_t v___x_3602_; lean_object* v___x_3603_; 
v___x_3601_ = ((size_t)0ULL);
v___x_3602_ = lean_usize_of_nat(v___x_3592_);
lean_inc(v_b_3590_);
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3593_, v___f_3596_, v_b_3590_, v___x_3601_, v___x_3602_, v_r_3586_);
return v___x_3603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3604_, lean_object* v_mr_3605_, lean_object* v_f_3606_, lean_object* v_i_3607_, lean_object* v_x_3608_, lean_object* v_r_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3604_, v_mr_3605_, v_f_3606_, v_i_3607_, v_x_3608_, v_r_3609_);
lean_dec(v_i_3607_);
lean_dec_ref(v_mr_3605_);
lean_dec(v_n_3604_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3611_, lean_object* v_a_3612_, lean_object* v_f_3613_){
_start:
{
lean_object* v_n_3614_; lean_object* v___f_3615_; lean_object* v___x_3616_; 
v_n_3614_ = lean_array_get_size(v_mr_3611_);
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3615_, 0, v_n_3614_);
lean_closure_set(v___f_3615_, 1, v_mr_3611_);
lean_closure_set(v___f_3615_, 2, v_f_3613_);
v___x_3616_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3614_, v___f_3615_, v_n_3614_, lean_box(0), v_a_3612_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3617_, lean_object* v_00_u03b2_3618_, lean_object* v_mr_3619_, lean_object* v_a_3620_, lean_object* v_f_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3619_, v_a_3620_, v_f_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3623_, size_t v_i_3624_, lean_object* v_bs_3625_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_lt(v_i_3624_, v_sz_3623_);
if (v___x_3626_ == 0)
{
return v_bs_3625_;
}
else
{
lean_object* v_v_3627_; lean_object* v___x_3628_; lean_object* v_bs_x27_3629_; size_t v___x_3630_; size_t v___x_3631_; lean_object* v___x_3632_; 
v_v_3627_ = lean_array_uget(v_bs_3625_, v_i_3624_);
v___x_3628_ = lean_unsigned_to_nat(0u);
v_bs_x27_3629_ = lean_array_uset(v_bs_3625_, v_i_3624_, v___x_3628_);
v___x_3630_ = ((size_t)1ULL);
v___x_3631_ = lean_usize_add(v_i_3624_, v___x_3630_);
v___x_3632_ = lean_array_uset(v_bs_x27_3629_, v_i_3624_, v_v_3627_);
v_i_3624_ = v___x_3631_;
v_bs_3625_ = v___x_3632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3634_, lean_object* v_i_3635_, lean_object* v_bs_3636_){
_start:
{
size_t v_sz_boxed_3637_; size_t v_i_boxed_3638_; lean_object* v_res_3639_; 
v_sz_boxed_3637_ = lean_unbox_usize(v_sz_3634_);
lean_dec(v_sz_3634_);
v_i_boxed_3638_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3637_, v_i_boxed_3638_, v_bs_3636_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3640_, size_t v_i_3641_, size_t v_stop_3642_, lean_object* v_b_3643_){
_start:
{
uint8_t v___x_3644_; 
v___x_3644_ = lean_usize_dec_eq(v_i_3641_, v_stop_3642_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; size_t v_sz_3646_; size_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; size_t v___x_3650_; size_t v___x_3651_; 
v___x_3645_ = lean_array_uget_borrowed(v_as_3640_, v_i_3641_);
v_sz_3646_ = lean_array_size(v___x_3645_);
v___x_3647_ = ((size_t)0ULL);
lean_inc(v___x_3645_);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3646_, v___x_3647_, v___x_3645_);
v___x_3649_ = l_Array_append___redArg(v_b_3643_, v___x_3648_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = ((size_t)1ULL);
v___x_3651_ = lean_usize_add(v_i_3641_, v___x_3650_);
v_i_3641_ = v___x_3651_;
v_b_3643_ = v___x_3649_;
goto _start;
}
else
{
return v_b_3643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3653_, lean_object* v_i_3654_, lean_object* v_stop_3655_, lean_object* v_b_3656_){
_start:
{
size_t v_i_boxed_3657_; size_t v_stop_boxed_3658_; lean_object* v_res_3659_; 
v_i_boxed_3657_ = lean_unbox_usize(v_i_3654_);
lean_dec(v_i_3654_);
v_stop_boxed_3658_ = lean_unbox_usize(v_stop_3655_);
lean_dec(v_stop_3655_);
v_res_3659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3653_, v_i_boxed_3657_, v_stop_boxed_3658_, v_b_3656_);
lean_dec_ref(v_as_3653_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3660_, lean_object* v_aa_3661_, lean_object* v_n_3662_, lean_object* v_j_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v_zero_3665_; uint8_t v_isZero_3666_; 
v_zero_3665_ = lean_unsigned_to_nat(0u);
v_isZero_3666_ = lean_nat_dec_eq(v_j_3663_, v_zero_3665_);
if (v_isZero_3666_ == 1)
{
lean_dec(v_j_3663_);
return v_a_3664_;
}
else
{
lean_object* v_one_3667_; lean_object* v_n_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v_j_3671_; lean_object* v_b_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v_one_3667_ = lean_unsigned_to_nat(1u);
v_n_3668_ = lean_nat_sub(v_j_3663_, v_one_3667_);
v___x_3669_ = lean_nat_sub(v_n_3662_, v_j_3663_);
lean_dec(v_j_3663_);
v___x_3670_ = lean_nat_sub(v_n_3660_, v_one_3667_);
v_j_3671_ = lean_nat_sub(v___x_3670_, v___x_3669_);
lean_dec(v___x_3669_);
lean_dec(v___x_3670_);
v_b_3672_ = lean_array_fget_borrowed(v_aa_3661_, v_j_3671_);
lean_dec(v_j_3671_);
v___x_3673_ = lean_array_get_size(v_b_3672_);
v___x_3674_ = lean_nat_dec_lt(v_zero_3665_, v___x_3673_);
if (v___x_3674_ == 0)
{
v_j_3663_ = v_n_3668_;
goto _start;
}
else
{
size_t v___x_3676_; size_t v___x_3677_; lean_object* v___x_3678_; 
v___x_3676_ = ((size_t)0ULL);
v___x_3677_ = lean_usize_of_nat(v___x_3673_);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3672_, v___x_3676_, v___x_3677_, v_a_3664_);
v_j_3663_ = v_n_3668_;
v_a_3664_ = v___x_3678_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3680_, lean_object* v_aa_3681_, lean_object* v_n_3682_, lean_object* v_j_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3680_, v_aa_3681_, v_n_3682_, v_j_3683_, v_a_3684_);
lean_dec(v_n_3682_);
lean_dec_ref(v_aa_3681_);
lean_dec(v_n_3680_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_n_3688_; lean_object* v___x_3689_; 
v_n_3688_ = lean_array_get_size(v_mr_3686_);
v___x_3689_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3688_, v_mr_3686_, v_n_3688_, v_n_3688_, v_a_3687_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3690_, v_a_3691_);
lean_dec_ref(v_mr_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3693_, v_a_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3696_, v_a_3697_);
lean_dec_ref(v_mr_3696_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3699_, lean_object* v_mr_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3700_, v_a_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3703_, lean_object* v_mr_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3703_, v_mr_3704_, v_a_3705_);
lean_dec_ref(v_mr_3704_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3707_, lean_object* v_mr_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3708_, v_a_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3711_, lean_object* v_mr_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3711_, v_mr_3712_, v_a_3713_);
lean_dec_ref(v_mr_3712_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3715_, size_t v_sz_3716_, size_t v_i_3717_, lean_object* v_bs_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3716_, v_i_3717_, v_bs_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3720_, lean_object* v_sz_3721_, lean_object* v_i_3722_, lean_object* v_bs_3723_){
_start:
{
size_t v_sz_boxed_3724_; size_t v_i_boxed_3725_; lean_object* v_res_3726_; 
v_sz_boxed_3724_ = lean_unbox_usize(v_sz_3721_);
lean_dec(v_sz_3721_);
v_i_boxed_3725_ = lean_unbox_usize(v_i_3722_);
lean_dec(v_i_3722_);
v_res_3726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3720_, v_sz_boxed_3724_, v_i_boxed_3725_, v_bs_3723_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3727_, lean_object* v_as_3728_, size_t v_i_3729_, size_t v_stop_3730_, lean_object* v_b_3731_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3728_, v_i_3729_, v_stop_3730_, v_b_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_as_3734_, lean_object* v_i_3735_, lean_object* v_stop_3736_, lean_object* v_b_3737_){
_start:
{
size_t v_i_boxed_3738_; size_t v_stop_boxed_3739_; lean_object* v_res_3740_; 
v_i_boxed_3738_ = lean_unbox_usize(v_i_3735_);
lean_dec(v_i_3735_);
v_stop_boxed_3739_ = lean_unbox_usize(v_stop_3736_);
lean_dec(v_stop_3736_);
v_res_3740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3733_, v_as_3734_, v_i_boxed_3738_, v_stop_boxed_3739_, v_b_3737_);
lean_dec_ref(v_as_3734_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3741_, lean_object* v_n_3742_, lean_object* v_aa_3743_, lean_object* v_n_3744_, lean_object* v_j_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3742_, v_aa_3743_, v_n_3744_, v_j_3745_, v_a_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3749_, lean_object* v_n_3750_, lean_object* v_aa_3751_, lean_object* v_n_3752_, lean_object* v_j_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3749_, v_n_3750_, v_aa_3751_, v_n_3752_, v_j_3753_, v_a_3754_, v_a_3755_);
lean_dec(v_n_3752_);
lean_dec_ref(v_aa_3751_);
lean_dec(v_n_3750_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3764_, lean_object* v___x_3765_, lean_object* v_score_3766_, lean_object* v___x_3767_, lean_object* v_k_3768_, lean_object* v_args_3769_, lean_object* v_cases_3770_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3764_, v_k_3768_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_dec_ref(v___x_3765_);
return v_cases_3770_;
}
else
{
lean_object* v_val_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_val_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = l_Array_append___redArg(v___x_3765_, v_args_3769_);
v___x_3774_ = lean_nat_add(v_score_3766_, v___x_3767_);
v___x_3775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
lean_ctor_set(v___x_3775_, 2, v_val_3772_);
v___x_3776_ = lean_array_push(v_cases_3770_, v___x_3775_);
return v___x_3776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3777_, lean_object* v___x_3778_, lean_object* v_score_3779_, lean_object* v___x_3780_, lean_object* v_k_3781_, lean_object* v_args_3782_, lean_object* v_cases_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3777_, v___x_3778_, v_score_3779_, v___x_3780_, v_k_3781_, v_args_3782_, v_cases_3783_);
lean_dec_ref(v_args_3782_);
lean_dec(v_k_3781_);
lean_dec(v___x_3780_);
lean_dec(v_score_3779_);
lean_dec_ref(v_snd_3777_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3785_, lean_object* v_result_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3793_ = lean_array_get_size(v_cases_3785_);
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = lean_nat_dec_eq(v___x_3793_, v___x_3794_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v_ca_3799_; lean_object* v_todo_3800_; lean_object* v_score_3801_; lean_object* v_c_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3867_; 
v___x_3796_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3797_ = lean_unsigned_to_nat(1u);
v___x_3798_ = lean_nat_sub(v___x_3793_, v___x_3797_);
v_ca_3799_ = lean_array_get(v___x_3796_, v_cases_3785_, v___x_3798_);
lean_dec(v___x_3798_);
v_todo_3800_ = lean_ctor_get(v_ca_3799_, 0);
v_score_3801_ = lean_ctor_get(v_ca_3799_, 1);
v_c_3802_ = lean_ctor_get(v_ca_3799_, 2);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_ca_3799_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3804_ = v_ca_3799_;
v_isShared_3805_ = v_isSharedCheck_3867_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_c_3802_);
lean_inc(v_score_3801_);
lean_inc(v_todo_3800_);
lean_dec(v_ca_3799_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3867_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3802_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
lean_dec(v_c_3802_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; uint8_t v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v_snd_3835_; lean_object* v_fst_3836_; lean_object* v_fst_3837_; lean_object* v_snd_3838_; lean_object* v_cases_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v_snd_3835_ = lean_ctor_get(v_a_3807_, 1);
lean_inc(v_snd_3835_);
v_fst_3836_ = lean_ctor_get(v_a_3807_, 0);
lean_inc(v_fst_3836_);
lean_dec(v_a_3807_);
v_fst_3837_ = lean_ctor_get(v_snd_3835_, 0);
lean_inc(v_fst_3837_);
v_snd_3838_ = lean_ctor_get(v_snd_3835_, 1);
lean_inc(v_snd_3838_);
lean_dec(v_snd_3835_);
v_cases_3839_ = lean_array_pop(v_cases_3785_);
v___x_3840_ = lean_array_get_size(v_todo_3800_);
v___x_3841_ = lean_nat_dec_eq(v___x_3840_, v___x_3794_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; uint8_t v___x_3843_; uint8_t v___y_3845_; 
lean_dec(v_fst_3836_);
v___x_3842_ = l_Lean_instInhabitedExpr;
v___x_3843_ = lean_nat_dec_eq(v_fst_3837_, v___x_3794_);
if (v___x_3843_ == 0)
{
v___y_3845_ = v___x_3841_;
goto v___jp_3844_;
}
else
{
lean_object* v_size_3854_; uint8_t v___x_3855_; 
v_size_3854_ = lean_ctor_get(v_snd_3838_, 0);
v___x_3855_ = lean_nat_dec_eq(v_size_3854_, v___x_3794_);
if (v___x_3855_ == 0)
{
v___y_3845_ = v___x_3855_;
goto v___jp_3844_;
}
else
{
lean_dec(v_snd_3838_);
lean_dec(v_fst_3837_);
lean_del_object(v___x_3804_);
lean_dec(v_score_3801_);
lean_dec_ref(v_todo_3800_);
v_cases_3785_ = v_cases_3839_;
goto _start;
}
}
v___jp_3844_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___f_3849_; 
v___x_3846_ = lean_nat_sub(v___x_3840_, v___x_3797_);
v___x_3847_ = lean_array_get(v___x_3842_, v_todo_3800_, v___x_3846_);
lean_dec(v___x_3846_);
v___x_3848_ = lean_array_pop(v_todo_3800_);
lean_inc(v_score_3801_);
lean_inc_ref(v___x_3848_);
v___f_3849_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3849_, 0, v_snd_3838_);
lean_closure_set(v___f_3849_, 1, v___x_3848_);
lean_closure_set(v___f_3849_, 2, v_score_3801_);
lean_closure_set(v___f_3849_, 3, v___x_3797_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3851_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 2, v_fst_3837_);
lean_ctor_set(v___x_3804_, 0, v___x_3848_);
v___x_3851_ = v___x_3804_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_score_3801_);
lean_ctor_set(v_reuseFailAlloc_3853_, 2, v_fst_3837_);
v___x_3851_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_array_push(v_cases_3839_, v___x_3851_);
v___y_3809_ = v___y_3845_;
v___y_3810_ = v___f_3849_;
v___y_3811_ = v___x_3847_;
v___y_3812_ = v___x_3852_;
goto v___jp_3808_;
}
}
else
{
lean_dec_ref(v___x_3848_);
lean_dec(v_fst_3837_);
lean_del_object(v___x_3804_);
lean_dec(v_score_3801_);
v___y_3809_ = v___y_3845_;
v___y_3810_ = v___f_3849_;
v___y_3811_ = v___x_3847_;
v___y_3812_ = v_cases_3839_;
goto v___jp_3808_;
}
}
}
else
{
lean_object* v___x_3857_; 
lean_dec(v_snd_3838_);
lean_dec(v_fst_3837_);
lean_del_object(v___x_3804_);
lean_dec_ref(v_todo_3800_);
v___x_3857_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3786_, v_score_3801_, v_fst_3836_);
lean_dec(v_score_3801_);
v_cases_3785_ = v_cases_3839_;
v_result_3786_ = v___x_3857_;
goto _start;
}
v___jp_3808_:
{
uint8_t v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = 1;
v___x_3814_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3811_, v___x_3813_, v___y_3809_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v_fst_3816_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v_fst_3816_ = lean_ctor_get(v_a_3815_, 0);
lean_inc(v_fst_3816_);
switch(lean_obj_tag(v_fst_3816_))
{
case 3:
{
lean_dec(v_a_3815_);
lean_dec_ref(v___y_3810_);
v_cases_3785_ = v___y_3812_;
goto _start;
}
case 5:
{
lean_object* v_snd_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v_snd_3818_ = lean_ctor_get(v_a_3815_, 1);
lean_inc(v_snd_3818_);
lean_dec(v_a_3815_);
v___x_3819_ = lean_box(4);
v___x_3820_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3810_);
v___x_3821_ = lean_apply_3(v___y_3810_, v___x_3819_, v___x_3820_, v___y_3812_);
v___x_3822_ = lean_apply_3(v___y_3810_, v_fst_3816_, v_snd_3818_, v___x_3821_);
v_cases_3785_ = v___x_3822_;
goto _start;
}
default: 
{
lean_object* v_snd_3824_; lean_object* v___x_3825_; 
v_snd_3824_ = lean_ctor_get(v_a_3815_, 1);
lean_inc(v_snd_3824_);
lean_dec(v_a_3815_);
v___x_3825_ = lean_apply_3(v___y_3810_, v_fst_3816_, v_snd_3824_, v___y_3812_);
v_cases_3785_ = v___x_3825_;
goto _start;
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v___y_3812_);
lean_dec_ref(v___y_3810_);
lean_dec_ref(v_result_3786_);
v_a_3827_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3814_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3814_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_del_object(v___x_3804_);
lean_dec(v_score_3801_);
lean_dec_ref(v_todo_3800_);
lean_dec_ref(v_result_3786_);
lean_dec_ref(v_cases_3785_);
v_a_3859_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3806_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3806_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
else
{
lean_object* v___x_3868_; 
lean_dec_ref(v_cases_3785_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v_result_3786_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3869_, lean_object* v_result_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3869_, v_result_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3878_, lean_object* v_cases_3879_, lean_object* v_result_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3879_, v_result_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3888_, lean_object* v_cases_3889_, lean_object* v_result_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3888_, v_cases_3889_, v_result_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_box(3);
v___x_3908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3900_, v___x_3907_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
return v___x_3910_;
}
else
{
lean_object* v_val_3911_; lean_object* v___x_3912_; 
v_val_3911_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_val_3911_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3912_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3911_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
lean_dec(v_val_3911_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3924_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3912_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v_fst_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
v_fst_3917_ = lean_ctor_get(v_a_3913_, 0);
lean_inc(v_fst_3917_);
lean_dec(v_a_3913_);
v___x_3918_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3919_ = lean_unsigned_to_nat(1u);
v___x_3920_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3918_, v___x_3919_, v_fst_3917_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3920_);
v___x_3922_ = v___x_3915_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
v_a_3925_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3912_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3912_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_root_3933_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3941_, lean_object* v_root_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3950_, lean_object* v_root_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3950_, v_root_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec_ref(v_root_3951_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3959_, lean_object* v_k_3960_, lean_object* v_args_3961_, lean_object* v_cases_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3959_, v_k_3960_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_dec_ref(v_args_3961_);
return v_cases_3962_;
}
else
{
lean_object* v_val_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v_val_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_val_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3966_, 0, v_args_3961_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
lean_ctor_set(v___x_3966_, 2, v_val_3964_);
v___x_3967_ = lean_array_push(v_cases_3962_, v___x_3966_);
return v___x_3967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3968_, lean_object* v_k_3969_, lean_object* v_args_3970_, lean_object* v_cases_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3968_, v_k_3969_, v_args_3970_, v_cases_3971_);
lean_dec(v_k_3969_);
lean_dec_ref(v_r_3968_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3975_, lean_object* v_e_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3975_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; uint8_t v___x_3985_; lean_object* v___x_3986_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
v___x_3985_ = 1;
v___x_3986_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3976_, v___x_3985_, v___x_3985_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v_fst_3988_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref_known(v___x_3986_, 1);
v_fst_3988_ = lean_ctor_get(v_a_3987_, 0);
lean_inc(v_fst_3988_);
switch(lean_obj_tag(v_fst_3988_))
{
case 3:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
lean_dec(v_a_3987_);
v___x_3989_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3990_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3989_, v_a_3984_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_3990_;
}
case 5:
{
lean_object* v_snd_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_snd_3991_ = lean_ctor_get(v_a_3987_, 1);
lean_inc(v_snd_3991_);
lean_dec(v_a_3987_);
v___x_3992_ = lean_box(4);
v___x_3993_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3994_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3975_, v___x_3992_, v___x_3993_, v___x_3993_);
v___x_3995_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3975_, v_fst_3988_, v_snd_3991_, v___x_3994_);
v___x_3996_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3995_, v_a_3984_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_3996_;
}
default: 
{
lean_object* v_snd_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_snd_3997_ = lean_ctor_get(v_a_3987_, 1);
lean_inc(v_snd_3997_);
lean_dec(v_a_3987_);
v___x_3998_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3999_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3975_, v_fst_3988_, v_snd_3997_, v___x_3998_);
lean_dec(v_fst_3988_);
v___x_4000_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3999_, v_a_3984_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_4000_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec(v_a_3984_);
v_a_4001_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3986_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3986_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_dec_ref(v_e_3976_);
return v___x_3983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_4009_, lean_object* v_e_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4009_, v_e_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_a_4011_);
lean_dec_ref(v_root_4009_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4018_, lean_object* v_root_4019_, lean_object* v_e_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4019_, v_e_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4028_, lean_object* v_root_4029_, lean_object* v_e_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4028_, v_root_4029_, v_e_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_root_4029_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4038_, lean_object* v_e_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___y_4046_; lean_object* v_roots_4063_; lean_object* v___x_4064_; uint8_t v_transparency_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; uint8_t v___x_4068_; 
v_roots_4063_ = lean_ctor_get(v_d_4038_, 1);
v___x_4064_ = l_Lean_Meta_Context_config(v_a_4040_);
v_transparency_4065_ = lean_ctor_get_uint8(v___x_4064_, 9);
lean_dec_ref(v___x_4064_);
lean_inc_ref(v_roots_4063_);
v___x_4066_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4066_, 0, lean_box(0));
lean_closure_set(v___x_4066_, 1, v_roots_4063_);
lean_closure_set(v___x_4066_, 2, v_e_4039_);
v___x_4067_ = 2;
v___x_4068_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4065_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v_keyedConfig_4069_; uint8_t v_trackZetaDelta_4070_; lean_object* v_zetaDeltaSet_4071_; lean_object* v_lctx_4072_; lean_object* v_localInstances_4073_; lean_object* v_defEqCtx_x3f_4074_; lean_object* v_synthPendingDepth_4075_; lean_object* v_customCanUnfoldPredicate_x3f_4076_; uint8_t v_univApprox_4077_; uint8_t v_inTypeClassResolution_4078_; uint8_t v_cacheInferType_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v_keyedConfig_4069_ = lean_ctor_get(v_a_4040_, 0);
v_trackZetaDelta_4070_ = lean_ctor_get_uint8(v_a_4040_, sizeof(void*)*7);
v_zetaDeltaSet_4071_ = lean_ctor_get(v_a_4040_, 1);
v_lctx_4072_ = lean_ctor_get(v_a_4040_, 2);
v_localInstances_4073_ = lean_ctor_get(v_a_4040_, 3);
v_defEqCtx_x3f_4074_ = lean_ctor_get(v_a_4040_, 4);
v_synthPendingDepth_4075_ = lean_ctor_get(v_a_4040_, 5);
v_customCanUnfoldPredicate_x3f_4076_ = lean_ctor_get(v_a_4040_, 6);
v_univApprox_4077_ = lean_ctor_get_uint8(v_a_4040_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4078_ = lean_ctor_get_uint8(v_a_4040_, sizeof(void*)*7 + 2);
v_cacheInferType_4079_ = lean_ctor_get_uint8(v_a_4040_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4069_);
v___x_4080_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4067_, v_keyedConfig_4069_);
lean_inc(v_customCanUnfoldPredicate_x3f_4076_);
lean_inc(v_synthPendingDepth_4075_);
lean_inc(v_defEqCtx_x3f_4074_);
lean_inc_ref(v_localInstances_4073_);
lean_inc_ref(v_lctx_4072_);
lean_inc(v_zetaDeltaSet_4071_);
v___x_4081_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v_zetaDeltaSet_4071_);
lean_ctor_set(v___x_4081_, 2, v_lctx_4072_);
lean_ctor_set(v___x_4081_, 3, v_localInstances_4073_);
lean_ctor_set(v___x_4081_, 4, v_defEqCtx_x3f_4074_);
lean_ctor_set(v___x_4081_, 5, v_synthPendingDepth_4075_);
lean_ctor_set(v___x_4081_, 6, v_customCanUnfoldPredicate_x3f_4076_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*7, v_trackZetaDelta_4070_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*7 + 1, v_univApprox_4077_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4078_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*7 + 3, v_cacheInferType_4079_);
v___x_4082_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4038_, v___x_4066_, v___x_4081_, v_a_4041_, v_a_4042_, v_a_4043_);
lean_dec_ref_known(v___x_4081_, 7);
v___y_4046_ = v___x_4082_;
goto v___jp_4045_;
}
else
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4038_, v___x_4066_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
v___y_4046_ = v___x_4083_;
goto v___jp_4045_;
}
v___jp_4045_:
{
if (lean_obj_tag(v___y_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v_a_4047_ = lean_ctor_get(v___y_4046_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___y_4046_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___y_4046_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___y_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
v_a_4055_ = lean_ctor_get(v___y_4046_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___y_4046_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___y_4046_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___y_4046_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4084_, lean_object* v_e_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4084_, v_e_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4092_, lean_object* v_d_4093_, lean_object* v_e_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4093_, v_e_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4101_, lean_object* v_d_4102_, lean_object* v_e_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4101_, v_d_4102_, v_e_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
return v_res_4109_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4113_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
lean_ctor_set(v___x_4114_, 1, v___x_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_00_u03b1_4115_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4116_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4118_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4120_, lean_object* v_k_4121_, lean_object* v_f_4122_){
_start:
{
lean_object* v_roots_4123_; lean_object* v_tries_4124_; lean_object* v___x_4125_; 
v_roots_4123_ = lean_ctor_get(v_d_4120_, 0);
v_tries_4124_ = lean_ctor_get(v_d_4120_, 1);
v___x_4125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4123_, v_k_4121_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4137_; 
lean_inc_ref(v_tries_4124_);
lean_inc_ref(v_roots_4123_);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_d_4120_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; lean_object* v_unused_4139_; 
v_unused_4138_ = lean_ctor_get(v_d_4120_, 1);
lean_dec(v_unused_4138_);
v_unused_4139_ = lean_ctor_get(v_d_4120_, 0);
lean_dec(v_unused_4139_);
v___x_4127_ = v_d_4120_;
v_isShared_4128_ = v_isSharedCheck_4137_;
goto v_resetjp_4126_;
}
else
{
lean_dec(v_d_4120_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4137_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4129_; lean_object* v_roots_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4129_ = lean_array_get_size(v_tries_4124_);
v_roots_4130_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4123_, v_k_4121_, v___x_4129_);
v___x_4131_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3));
v___x_4132_ = lean_apply_1(v_f_4122_, v___x_4131_);
v___x_4133_ = lean_array_push(v_tries_4124_, v___x_4132_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 1, v___x_4133_);
lean_ctor_set(v___x_4127_, 0, v_roots_4130_);
v___x_4135_ = v___x_4127_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_roots_4130_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
else
{
lean_object* v_val_4140_; lean_object* v___x_4141_; uint8_t v___x_4142_; 
lean_dec(v_k_4121_);
v_val_4140_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_val_4140_);
lean_dec_ref_known(v___x_4125_, 1);
v___x_4141_ = lean_array_get_size(v_tries_4124_);
v___x_4142_ = lean_nat_dec_lt(v_val_4140_, v___x_4141_);
if (v___x_4142_ == 0)
{
lean_dec(v_val_4140_);
lean_dec_ref(v_f_4122_);
return v_d_4120_;
}
else
{
lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4154_; 
lean_inc_ref(v_tries_4124_);
lean_inc_ref(v_roots_4123_);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_d_4120_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; lean_object* v_unused_4156_; 
v_unused_4155_ = lean_ctor_get(v_d_4120_, 1);
lean_dec(v_unused_4155_);
v_unused_4156_ = lean_ctor_get(v_d_4120_, 0);
lean_dec(v_unused_4156_);
v___x_4144_ = v_d_4120_;
v_isShared_4145_ = v_isSharedCheck_4154_;
goto v_resetjp_4143_;
}
else
{
lean_dec(v_d_4120_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4154_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v_v_4146_; lean_object* v___x_4147_; lean_object* v_xs_x27_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
v_v_4146_ = lean_array_fget(v_tries_4124_, v_val_4140_);
v___x_4147_ = lean_box(0);
v_xs_x27_4148_ = lean_array_fset(v_tries_4124_, v_val_4140_, v___x_4147_);
v___x_4149_ = lean_apply_1(v_f_4122_, v_v_4146_);
v___x_4150_ = lean_array_fset(v_xs_x27_4148_, v_val_4140_, v___x_4149_);
lean_dec(v_val_4140_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 1, v___x_4150_);
v___x_4152_ = v___x_4144_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_roots_4123_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4157_, lean_object* v_d_4158_, lean_object* v_k_4159_, lean_object* v_f_4160_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4158_, v_k_4159_, v_f_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4162_, lean_object* v_x_4163_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_array_push(v_x_4163_, v_e_4162_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4165_, lean_object* v_k_4166_, lean_object* v_e_4167_){
_start:
{
lean_object* v___f_4168_; lean_object* v___x_4169_; 
v___f_4168_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4168_, 0, v_e_4167_);
v___x_4169_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4165_, v_k_4166_, v___f_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4170_, lean_object* v_d_4171_, lean_object* v_k_4172_, lean_object* v_e_4173_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4171_, v_k_4172_, v_e_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4175_, size_t v_i_4176_, lean_object* v_bs_4177_){
_start:
{
uint8_t v___x_4178_; 
v___x_4178_ = lean_usize_dec_lt(v_i_4176_, v_sz_4175_);
if (v___x_4178_ == 0)
{
return v_bs_4177_;
}
else
{
lean_object* v_v_4179_; lean_object* v___x_4180_; lean_object* v_bs_x27_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; size_t v___x_4185_; size_t v___x_4186_; lean_object* v___x_4187_; 
v_v_4179_ = lean_array_uget(v_bs_4177_, v_i_4176_);
v___x_4180_ = lean_unsigned_to_nat(0u);
v_bs_x27_4181_ = lean_array_uset(v_bs_4177_, v_i_4176_, v___x_4180_);
v___x_4182_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4183_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4182_);
lean_ctor_set(v___x_4184_, 1, v___x_4180_);
lean_ctor_set(v___x_4184_, 2, v___x_4183_);
lean_ctor_set(v___x_4184_, 3, v_v_4179_);
v___x_4185_ = ((size_t)1ULL);
v___x_4186_ = lean_usize_add(v_i_4176_, v___x_4185_);
v___x_4187_ = lean_array_uset(v_bs_x27_4181_, v_i_4176_, v___x_4184_);
v_i_4176_ = v___x_4186_;
v_bs_4177_ = v___x_4187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4189_, lean_object* v_i_4190_, lean_object* v_bs_4191_){
_start:
{
size_t v_sz_boxed_4192_; size_t v_i_boxed_4193_; lean_object* v_res_4194_; 
v_sz_boxed_4192_ = lean_unbox_usize(v_sz_4189_);
lean_dec(v_sz_4189_);
v_i_boxed_4193_ = lean_unbox_usize(v_i_4190_);
lean_dec(v_i_4190_);
v_res_4194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4192_, v_i_boxed_4193_, v_bs_4191_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4195_, lean_object* v_x_4196_){
_start:
{
if (lean_obj_tag(v_x_4196_) == 0)
{
return v_x_4195_;
}
else
{
lean_object* v_key_4197_; lean_object* v_value_4198_; lean_object* v_tail_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_key_4197_ = lean_ctor_get(v_x_4196_, 0);
lean_inc(v_key_4197_);
v_value_4198_ = lean_ctor_get(v_x_4196_, 1);
lean_inc(v_value_4198_);
v_tail_4199_ = lean_ctor_get(v_x_4196_, 2);
lean_inc(v_tail_4199_);
lean_dec_ref_known(v_x_4196_, 3);
v___x_4200_ = lean_unsigned_to_nat(1u);
v___x_4201_ = lean_nat_add(v_value_4198_, v___x_4200_);
lean_dec(v_value_4198_);
v___x_4202_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4195_, v_key_4197_, v___x_4201_);
v_x_4195_ = v___x_4202_;
v_x_4196_ = v_tail_4199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4204_, size_t v_i_4205_, size_t v_stop_4206_, lean_object* v_b_4207_){
_start:
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_usize_dec_eq(v_i_4205_, v_stop_4206_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4210_; size_t v___x_4211_; size_t v___x_4212_; 
v___x_4209_ = lean_array_uget_borrowed(v_as_4204_, v_i_4205_);
lean_inc(v___x_4209_);
v___x_4210_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4207_, v___x_4209_);
v___x_4211_ = ((size_t)1ULL);
v___x_4212_ = lean_usize_add(v_i_4205_, v___x_4211_);
v_i_4205_ = v___x_4212_;
v_b_4207_ = v___x_4210_;
goto _start;
}
else
{
return v_b_4207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4214_, lean_object* v_i_4215_, lean_object* v_stop_4216_, lean_object* v_b_4217_){
_start:
{
size_t v_i_boxed_4218_; size_t v_stop_boxed_4219_; lean_object* v_res_4220_; 
v_i_boxed_4218_ = lean_unbox_usize(v_i_4215_);
lean_dec(v_i_4215_);
v_stop_boxed_4219_ = lean_unbox_usize(v_stop_4216_);
lean_dec(v_stop_4216_);
v_res_4220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4214_, v_i_boxed_4218_, v_stop_boxed_4219_, v_b_4217_);
lean_dec_ref(v_as_4214_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4221_){
_start:
{
lean_object* v_roots_4222_; lean_object* v_tries_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4246_; 
v_roots_4222_ = lean_ctor_get(v_d_4221_, 0);
v_tries_4223_ = lean_ctor_get(v_d_4221_, 1);
v_isSharedCheck_4246_ = !lean_is_exclusive(v_d_4221_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4225_ = v_d_4221_;
v_isShared_4226_ = v_isSharedCheck_4246_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_tries_4223_);
lean_inc(v_roots_4222_);
lean_dec(v_d_4221_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4246_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___y_4228_; lean_object* v_buckets_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; 
v_buckets_4239_ = lean_ctor_get(v_roots_4222_, 1);
v___x_4240_ = lean_unsigned_to_nat(0u);
v___x_4241_ = lean_array_get_size(v_buckets_4239_);
v___x_4242_ = lean_nat_dec_lt(v___x_4240_, v___x_4241_);
if (v___x_4242_ == 0)
{
v___y_4228_ = v_roots_4222_;
goto v___jp_4227_;
}
else
{
size_t v___x_4243_; size_t v___x_4244_; lean_object* v___x_4245_; 
lean_inc_ref(v_buckets_4239_);
v___x_4243_ = ((size_t)0ULL);
v___x_4244_ = lean_usize_of_nat(v___x_4241_);
v___x_4245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4239_, v___x_4243_, v___x_4244_, v_roots_4222_);
lean_dec_ref(v_buckets_4239_);
v___y_4228_ = v___x_4245_;
goto v___jp_4227_;
}
v___jp_4227_:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; size_t v_sz_4232_; size_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4229_ = lean_unsigned_to_nat(1u);
v___x_4230_ = lean_mk_empty_array_with_capacity(v___x_4229_);
lean_dec_ref(v___x_4230_);
v___x_4231_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4232_ = lean_array_size(v_tries_4223_);
v___x_4233_ = ((size_t)0ULL);
v___x_4234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4232_, v___x_4233_, v_tries_4223_);
v___x_4235_ = l_Array_append___redArg(v___x_4231_, v___x_4234_);
lean_dec_ref(v___x_4234_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 1, v___y_4228_);
lean_ctor_set(v___x_4225_, 0, v___x_4235_);
v___x_4237_ = v___x_4225_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v___y_4228_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4247_, lean_object* v_d_4248_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4250_, size_t v_sz_4251_, size_t v_i_4252_, lean_object* v_bs_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4251_, v_i_4252_, v_bs_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4255_, lean_object* v_sz_4256_, lean_object* v_i_4257_, lean_object* v_bs_4258_){
_start:
{
size_t v_sz_boxed_4259_; size_t v_i_boxed_4260_; lean_object* v_res_4261_; 
v_sz_boxed_4259_ = lean_unbox_usize(v_sz_4256_);
lean_dec(v_sz_4256_);
v_i_boxed_4260_ = lean_unbox_usize(v_i_4257_);
lean_dec(v_i_4257_);
v_res_4261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4255_, v_sz_boxed_4259_, v_i_boxed_4260_, v_bs_4258_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4262_, lean_object* v_x_4263_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Array_append___redArg(v_x_4263_, v_y_4262_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4265_, lean_object* v_x_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4265_, v_x_4266_);
lean_dec_ref(v_y_4265_);
return v_res_4267_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Array_instInhabited(lean_box(0));
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4269_, lean_object* v_snd_4270_, lean_object* v_x_4271_, lean_object* v_x_4272_){
_start:
{
if (lean_obj_tag(v_x_4272_) == 0)
{
lean_dec_ref(v_snd_4270_);
return v_x_4271_;
}
else
{
lean_object* v_key_4273_; lean_object* v_value_4274_; lean_object* v_tail_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_key_4273_ = lean_ctor_get(v_x_4272_, 0);
lean_inc(v_key_4273_);
v_value_4274_ = lean_ctor_get(v_x_4272_, 1);
lean_inc(v_value_4274_);
v_tail_4275_ = lean_ctor_get(v_x_4272_, 2);
lean_inc(v_tail_4275_);
lean_dec_ref_known(v_x_4272_, 3);
v___x_4276_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4277_ = lean_array_get_borrowed(v___x_4276_, v_tries_4269_, v_value_4274_);
lean_dec(v_value_4274_);
lean_inc_ref(v_snd_4270_);
lean_inc(v___x_4277_);
v___x_4278_ = lean_apply_1(v_snd_4270_, v___x_4277_);
v___x_4279_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4271_, v_key_4273_, v___x_4278_);
v_x_4271_ = v___x_4279_;
v_x_4272_ = v_tail_4275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4281_, lean_object* v_snd_4282_, lean_object* v_x_4283_, lean_object* v_x_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4281_, v_snd_4282_, v_x_4283_, v_x_4284_);
lean_dec_ref(v_tries_4281_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4286_, lean_object* v_snd_4287_, lean_object* v_as_4288_, size_t v_i_4289_, size_t v_stop_4290_, lean_object* v_b_4291_){
_start:
{
uint8_t v___x_4292_; 
v___x_4292_ = lean_usize_dec_eq(v_i_4289_, v_stop_4290_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; lean_object* v___x_4294_; size_t v___x_4295_; size_t v___x_4296_; 
v___x_4293_ = lean_array_uget_borrowed(v_as_4288_, v_i_4289_);
lean_inc(v___x_4293_);
lean_inc_ref(v_snd_4287_);
v___x_4294_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4286_, v_snd_4287_, v_b_4291_, v___x_4293_);
v___x_4295_ = ((size_t)1ULL);
v___x_4296_ = lean_usize_add(v_i_4289_, v___x_4295_);
v_i_4289_ = v___x_4296_;
v_b_4291_ = v___x_4294_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4287_);
return v_b_4291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4298_, lean_object* v_snd_4299_, lean_object* v_as_4300_, lean_object* v_i_4301_, lean_object* v_stop_4302_, lean_object* v_b_4303_){
_start:
{
size_t v_i_boxed_4304_; size_t v_stop_boxed_4305_; lean_object* v_res_4306_; 
v_i_boxed_4304_ = lean_unbox_usize(v_i_4301_);
lean_dec(v_i_4301_);
v_stop_boxed_4305_ = lean_unbox_usize(v_stop_4302_);
lean_dec(v_stop_4302_);
v_res_4306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4298_, v_snd_4299_, v_as_4300_, v_i_boxed_4304_, v_stop_boxed_4305_, v_b_4303_);
lean_dec_ref(v_as_4300_);
lean_dec_ref(v_tries_4298_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4309_, lean_object* v_y_4310_){
_start:
{
lean_object* v_fst_4312_; lean_object* v_buckets_4313_; lean_object* v_tries_4314_; lean_object* v_snd_4315_; lean_object* v_roots_4322_; lean_object* v_roots_4323_; lean_object* v_tries_4324_; lean_object* v_size_4325_; lean_object* v_buckets_4326_; lean_object* v_tries_4327_; lean_object* v_size_4328_; lean_object* v_buckets_4329_; uint8_t v___x_4330_; 
v_roots_4322_ = lean_ctor_get(v_y_4310_, 0);
v_roots_4323_ = lean_ctor_get(v_x_4309_, 0);
v_tries_4324_ = lean_ctor_get(v_y_4310_, 1);
v_size_4325_ = lean_ctor_get(v_roots_4322_, 0);
v_buckets_4326_ = lean_ctor_get(v_roots_4322_, 1);
v_tries_4327_ = lean_ctor_get(v_x_4309_, 1);
v_size_4328_ = lean_ctor_get(v_roots_4323_, 0);
v_buckets_4329_ = lean_ctor_get(v_roots_4323_, 1);
v___x_4330_ = lean_nat_dec_le(v_size_4325_, v_size_4328_);
if (v___x_4330_ == 0)
{
lean_object* v___f_4331_; 
lean_inc_ref(v_buckets_4329_);
lean_inc_ref(v_tries_4327_);
lean_dec_ref(v_x_4309_);
v___f_4331_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4312_ = v_y_4310_;
v_buckets_4313_ = v_buckets_4329_;
v_tries_4314_ = v_tries_4327_;
v_snd_4315_ = v___f_4331_;
goto v___jp_4311_;
}
else
{
lean_object* v___f_4332_; 
lean_inc_ref(v_buckets_4326_);
lean_inc_ref(v_tries_4324_);
lean_dec_ref(v_y_4310_);
v___f_4332_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4312_ = v_x_4309_;
v_buckets_4313_ = v_buckets_4326_;
v_tries_4314_ = v_tries_4324_;
v_snd_4315_ = v___f_4332_;
goto v___jp_4311_;
}
v___jp_4311_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_array_get_size(v_buckets_4313_);
v___x_4318_ = lean_nat_dec_lt(v___x_4316_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_dec_ref(v_tries_4314_);
lean_dec_ref(v_buckets_4313_);
return v_fst_4312_;
}
else
{
size_t v___x_4319_; size_t v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = ((size_t)0ULL);
v___x_4320_ = lean_usize_of_nat(v___x_4317_);
lean_inc_ref(v_snd_4315_);
v___x_4321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4314_, v_snd_4315_, v_buckets_4313_, v___x_4319_, v___x_4320_, v_fst_4312_);
lean_dec_ref(v_buckets_4313_);
lean_dec_ref(v_tries_4314_);
return v___x_4321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4333_, lean_object* v_x_4334_, lean_object* v_y_4335_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4334_, v_y_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4337_, lean_object* v_tries_4338_, lean_object* v_snd_4339_, lean_object* v_x_4340_, lean_object* v_x_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4338_, v_snd_4339_, v_x_4340_, v_x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4343_, lean_object* v_tries_4344_, lean_object* v_snd_4345_, lean_object* v_x_4346_, lean_object* v_x_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4343_, v_tries_4344_, v_snd_4345_, v_x_4346_, v_x_4347_);
lean_dec_ref(v_tries_4344_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4349_, lean_object* v_tries_4350_, lean_object* v_snd_4351_, lean_object* v_as_4352_, size_t v_i_4353_, size_t v_stop_4354_, lean_object* v_b_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4350_, v_snd_4351_, v_as_4352_, v_i_4353_, v_stop_4354_, v_b_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4357_, lean_object* v_tries_4358_, lean_object* v_snd_4359_, lean_object* v_as_4360_, lean_object* v_i_4361_, lean_object* v_stop_4362_, lean_object* v_b_4363_){
_start:
{
size_t v_i_boxed_4364_; size_t v_stop_boxed_4365_; lean_object* v_res_4366_; 
v_i_boxed_4364_ = lean_unbox_usize(v_i_4361_);
lean_dec(v_i_4361_);
v_stop_boxed_4365_ = lean_unbox_usize(v_stop_4362_);
lean_dec(v_stop_4362_);
v_res_4366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4357_, v_tries_4358_, v_snd_4359_, v_as_4360_, v_i_boxed_4364_, v_stop_boxed_4365_, v_b_4363_);
lean_dec_ref(v_as_4360_);
lean_dec_ref(v_tries_4358_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4370_, lean_object* v_value_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4370_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4399_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4399_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4399_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v_fst_4382_; lean_object* v_snd_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4398_; 
v_fst_4382_ = lean_ctor_get(v_a_4378_, 0);
v_snd_4383_ = lean_ctor_get(v_a_4378_, 1);
v_isSharedCheck_4398_ = !lean_is_exclusive(v_a_4378_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4385_ = v_a_4378_;
v_isShared_4386_ = v_isSharedCheck_4398_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_snd_4383_);
lean_inc(v_fst_4382_);
lean_dec(v_a_4378_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4398_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v_lctx_4387_; lean_object* v_localInstances_4388_; lean_object* v___x_4390_; 
v_lctx_4387_ = lean_ctor_get(v_a_4372_, 2);
v_localInstances_4388_ = lean_ctor_get(v_a_4372_, 3);
lean_inc_ref(v_localInstances_4388_);
lean_inc_ref(v_lctx_4387_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 1, v_localInstances_4388_);
lean_ctor_set(v___x_4385_, 0, v_lctx_4387_);
v___x_4390_ = v___x_4385_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_lctx_4387_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_localInstances_4388_);
v___x_4390_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
lean_ctor_set(v___x_4391_, 1, v_value_4371_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_snd_4383_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_fst_4382_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4393_);
v___x_4395_ = v___x_4380_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_value_4371_);
v_a_4400_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4377_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4377_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4408_, lean_object* v_value_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4408_, v_value_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_a_4413_);
lean_dec_ref(v_a_4412_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4416_, lean_object* v_expr_4417_, lean_object* v_value_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4417_, v_value_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4425_, lean_object* v_expr_4426_, lean_object* v_value_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4425_, v_expr_4426_, v_value_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_);
lean_dec(v_a_4431_);
lean_dec_ref(v_a_4430_);
lean_dec(v_a_4429_);
lean_dec_ref(v_a_4428_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4434_, lean_object* v_idx_4435_, lean_object* v_value_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
lean_object* v_entry_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4488_; 
v_entry_4442_ = lean_ctor_get(v_e_4434_, 1);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_e_4434_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v_e_4434_, 0);
lean_dec(v_unused_4489_);
v___x_4444_ = v_e_4434_;
v_isShared_4445_ = v_isSharedCheck_4488_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_entry_4442_);
lean_dec(v_e_4434_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4488_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v_snd_4446_; lean_object* v_fst_4447_; lean_object* v_fst_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4486_; 
v_snd_4446_ = lean_ctor_get(v_entry_4442_, 1);
lean_inc(v_snd_4446_);
v_fst_4447_ = lean_ctor_get(v_entry_4442_, 0);
lean_inc(v_fst_4447_);
lean_dec_ref(v_entry_4442_);
v_fst_4448_ = lean_ctor_get(v_snd_4446_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_snd_4446_);
if (v_isSharedCheck_4486_ == 0)
{
lean_object* v_unused_4487_; 
v_unused_4487_ = lean_ctor_get(v_snd_4446_, 1);
lean_dec(v_unused_4487_);
v___x_4450_ = v_snd_4446_;
v_isShared_4451_ = v_isSharedCheck_4486_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_fst_4448_);
lean_dec(v_snd_4446_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4486_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = l_Lean_instInhabitedExpr;
v___x_4453_ = lean_array_get(v___x_4452_, v_fst_4447_, v_idx_4435_);
lean_dec(v_fst_4447_);
v___x_4454_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4453_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4477_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4457_ = v___x_4454_;
v_isShared_4458_ = v_isSharedCheck_4477_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4454_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4477_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v_fst_4459_; lean_object* v_snd_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4476_; 
v_fst_4459_ = lean_ctor_get(v_a_4455_, 0);
v_snd_4460_ = lean_ctor_get(v_a_4455_, 1);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_a_4455_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4462_ = v_a_4455_;
v_isShared_4463_ = v_isSharedCheck_4476_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_snd_4460_);
lean_inc(v_fst_4459_);
lean_dec(v_a_4455_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4476_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 1, v_value_4436_);
lean_ctor_set(v___x_4462_, 0, v_fst_4448_);
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_fst_4448_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_value_4436_);
v___x_4465_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4467_; 
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 1, v___x_4465_);
lean_ctor_set(v___x_4450_, 0, v_snd_4460_);
v___x_4467_ = v___x_4450_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_snd_4460_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4469_; 
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 1, v___x_4467_);
lean_ctor_set(v___x_4444_, 0, v_fst_4459_);
v___x_4469_ = v___x_4444_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_fst_4459_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4471_; 
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v___x_4469_);
v___x_4471_ = v___x_4457_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4469_);
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
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_del_object(v___x_4450_);
lean_dec(v_fst_4448_);
lean_del_object(v___x_4444_);
lean_dec(v_value_4436_);
v_a_4478_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4454_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4454_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4490_, lean_object* v_idx_4491_, lean_object* v_value_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4490_, v_idx_4491_, v_value_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec(v_a_4494_);
lean_dec_ref(v_a_4493_);
lean_dec(v_idx_4491_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4499_, lean_object* v_e_4500_, lean_object* v_idx_4501_, lean_object* v_value_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4500_, v_idx_4501_, v_value_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4509_, lean_object* v_e_4510_, lean_object* v_idx_4511_, lean_object* v_value_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4509_, v_e_4510_, v_idx_4511_, v_value_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_idx_4511_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4523_ = lean_st_mk_ref(v___x_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4525_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4526_; 
v___x_4526_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4526_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
return v___x_4528_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
return v___x_4530_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4532_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
lean_ctor_set(v___x_4532_, 1, v___x_4531_);
lean_ctor_set(v___x_4532_, 2, v___x_4531_);
lean_ctor_set(v___x_4532_, 3, v___x_4531_);
lean_ctor_set(v___x_4532_, 4, v___x_4531_);
lean_ctor_set(v___x_4532_, 5, v___x_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4533_){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4534_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4535_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4536_, 0, v_ngen_4533_);
lean_ctor_set(v___x_4536_, 1, v___x_4534_);
lean_ctor_set(v___x_4536_, 2, v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4537_, lean_object* v_declName_4538_){
_start:
{
uint8_t v___x_4539_; 
v___x_4539_ = l_Lean_isPrivateName(v_declName_4538_);
if (v___x_4539_ == 0)
{
return v___x_4539_;
}
else
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4537_, v_declName_4538_);
if (lean_obj_tag(v___x_4540_) == 0)
{
return v___x_4539_;
}
else
{
lean_object* v_val_4541_; lean_object* v___x_4542_; uint8_t v_isModule_4543_; lean_object* v_modules_4544_; uint8_t v___x_4545_; 
v_val_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_val_4541_);
lean_dec_ref_known(v___x_4540_, 1);
v___x_4542_ = l_Lean_Environment_header(v_env_4537_);
v_isModule_4543_ = lean_ctor_get_uint8(v___x_4542_, sizeof(void*)*7 + 4);
v_modules_4544_ = lean_ctor_get(v___x_4542_, 3);
lean_inc_ref(v_modules_4544_);
lean_dec_ref(v___x_4542_);
v___x_4545_ = 0;
if (v_isModule_4543_ == 0)
{
lean_dec_ref(v_modules_4544_);
lean_dec(v_val_4541_);
return v___x_4545_;
}
else
{
lean_object* v___x_4546_; uint8_t v___x_4547_; 
v___x_4546_ = lean_array_get_size(v_modules_4544_);
v___x_4547_ = lean_nat_dec_lt(v_val_4541_, v___x_4546_);
if (v___x_4547_ == 0)
{
lean_dec_ref(v_modules_4544_);
lean_dec(v_val_4541_);
return v___x_4545_;
}
else
{
lean_object* v___x_4548_; lean_object* v_toImport_4549_; uint8_t v_importAll_4550_; 
v___x_4548_ = lean_array_fget(v_modules_4544_, v_val_4541_);
lean_dec(v_val_4541_);
lean_dec_ref(v_modules_4544_);
v_toImport_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc_ref(v_toImport_4549_);
lean_dec(v___x_4548_);
v_importAll_4550_ = lean_ctor_get_uint8(v_toImport_4549_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4549_);
return v_importAll_4550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4551_, lean_object* v_declName_4552_){
_start:
{
uint8_t v_res_4553_; lean_object* v_r_4554_; 
v_res_4553_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4551_, v_declName_4552_);
lean_dec(v_declName_4552_);
lean_dec_ref(v_env_4551_);
v_r_4554_ = lean_box(v_res_4553_);
return v_r_4554_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4560_, lean_object* v_declName_4561_){
_start:
{
uint8_t v___x_4562_; 
lean_inc(v_declName_4561_);
lean_inc_ref(v_env_4560_);
v___x_4562_ = l_Lean_Meta_allowCompletion(v_env_4560_, v_declName_4561_);
if (v___x_4562_ == 0)
{
uint8_t v___x_4563_; 
lean_dec(v_declName_4561_);
lean_dec_ref(v_env_4560_);
v___x_4563_ = 1;
return v___x_4563_;
}
else
{
lean_object* v___x_4564_; uint8_t v___x_4565_; uint8_t v___y_4575_; 
v___x_4564_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4565_ = lean_name_eq(v_declName_4561_, v___x_4564_);
if (v___x_4565_ == 0)
{
uint8_t v___x_4576_; 
lean_inc(v_declName_4561_);
v___x_4576_ = l_Lean_Name_isInternalDetail(v_declName_4561_);
if (v___x_4576_ == 0)
{
lean_dec_ref(v_env_4560_);
v___y_4575_ = v___x_4576_;
goto v___jp_4574_;
}
else
{
uint8_t v___x_4577_; 
v___x_4577_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4560_, v_declName_4561_);
lean_dec_ref(v_env_4560_);
if (v___x_4577_ == 0)
{
v___y_4575_ = v___x_4576_;
goto v___jp_4574_;
}
else
{
goto v___jp_4570_;
}
}
}
else
{
lean_dec(v_declName_4561_);
lean_dec_ref(v_env_4560_);
return v___x_4565_;
}
v___jp_4566_:
{
if (lean_obj_tag(v_declName_4561_) == 1)
{
lean_object* v_str_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; 
v_str_4567_ = lean_ctor_get(v_declName_4561_, 1);
lean_inc_ref(v_str_4567_);
lean_dec_ref_known(v_declName_4561_, 2);
v___x_4568_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4569_ = lean_string_dec_eq(v_str_4567_, v___x_4568_);
lean_dec_ref(v_str_4567_);
return v___x_4569_;
}
else
{
lean_dec(v_declName_4561_);
return v___x_4565_;
}
}
v___jp_4570_:
{
if (lean_obj_tag(v_declName_4561_) == 1)
{
lean_object* v_str_4571_; lean_object* v___x_4572_; uint8_t v___x_4573_; 
v_str_4571_ = lean_ctor_get(v_declName_4561_, 1);
v___x_4572_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4573_ = lean_string_dec_eq(v_str_4571_, v___x_4572_);
if (v___x_4573_ == 0)
{
goto v___jp_4566_;
}
else
{
lean_dec_ref_known(v_declName_4561_, 2);
return v___x_4573_;
}
}
else
{
goto v___jp_4566_;
}
}
v___jp_4574_:
{
if (v___y_4575_ == 0)
{
goto v___jp_4570_;
}
else
{
lean_dec(v_declName_4561_);
return v___y_4575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4578_, lean_object* v_declName_4579_){
_start:
{
uint8_t v_res_4580_; lean_object* v_r_4581_; 
v_res_4580_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4578_, v_declName_4579_);
v_r_4581_ = lean_box(v_res_4580_);
return v_r_4581_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4582_, lean_object* v_opt_4583_){
_start:
{
lean_object* v_name_4584_; lean_object* v_defValue_4585_; lean_object* v_map_4586_; lean_object* v___x_4587_; 
v_name_4584_ = lean_ctor_get(v_opt_4583_, 0);
v_defValue_4585_ = lean_ctor_get(v_opt_4583_, 1);
v_map_4586_ = lean_ctor_get(v_opts_4582_, 0);
v___x_4587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4586_, v_name_4584_);
if (lean_obj_tag(v___x_4587_) == 0)
{
uint8_t v___x_4588_; 
v___x_4588_ = lean_unbox(v_defValue_4585_);
return v___x_4588_;
}
else
{
lean_object* v_val_4589_; 
v_val_4589_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_val_4589_);
lean_dec_ref_known(v___x_4587_, 1);
if (lean_obj_tag(v_val_4589_) == 1)
{
uint8_t v_v_4590_; 
v_v_4590_ = lean_ctor_get_uint8(v_val_4589_, 0);
lean_dec_ref_known(v_val_4589_, 0);
return v_v_4590_;
}
else
{
uint8_t v___x_4591_; 
lean_dec(v_val_4589_);
v___x_4591_ = lean_unbox(v_defValue_4585_);
return v___x_4591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4592_, lean_object* v_opt_4593_){
_start:
{
uint8_t v_res_4594_; lean_object* v_r_4595_; 
v_res_4594_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4592_, v_opt_4593_);
lean_dec_ref(v_opt_4593_);
lean_dec_ref(v_opts_4592_);
v_r_4595_ = lean_box(v_res_4594_);
return v_r_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4596_, lean_object* v_opt_4597_){
_start:
{
lean_object* v_name_4598_; lean_object* v_defValue_4599_; lean_object* v_map_4600_; lean_object* v___x_4601_; 
v_name_4598_ = lean_ctor_get(v_opt_4597_, 0);
v_defValue_4599_ = lean_ctor_get(v_opt_4597_, 1);
v_map_4600_ = lean_ctor_get(v_opts_4596_, 0);
v___x_4601_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4600_, v_name_4598_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_inc(v_defValue_4599_);
return v_defValue_4599_;
}
else
{
lean_object* v_val_4602_; 
v_val_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_val_4602_);
lean_dec_ref_known(v___x_4601_, 1);
if (lean_obj_tag(v_val_4602_) == 3)
{
lean_object* v_v_4603_; 
v_v_4603_ = lean_ctor_get(v_val_4602_, 0);
lean_inc(v_v_4603_);
lean_dec_ref_known(v_val_4602_, 1);
return v_v_4603_;
}
else
{
lean_dec(v_val_4602_);
lean_inc(v_defValue_4599_);
return v_defValue_4599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4604_, lean_object* v_opt_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4604_, v_opt_4605_);
lean_dec_ref(v_opt_4605_);
lean_dec_ref(v_opts_4604_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4607_, size_t v_i_4608_, size_t v_stop_4609_, lean_object* v_b_4610_){
_start:
{
uint8_t v___x_4611_; 
v___x_4611_ = lean_usize_dec_eq(v_i_4608_, v_stop_4609_);
if (v___x_4611_ == 0)
{
lean_object* v___x_4612_; lean_object* v_key_4613_; lean_object* v_entry_4614_; lean_object* v___x_4615_; size_t v___x_4616_; size_t v___x_4617_; 
v___x_4612_ = lean_array_uget_borrowed(v_as_4607_, v_i_4608_);
v_key_4613_ = lean_ctor_get(v___x_4612_, 0);
v_entry_4614_ = lean_ctor_get(v___x_4612_, 1);
lean_inc_ref(v_entry_4614_);
lean_inc(v_key_4613_);
v___x_4615_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4610_, v_key_4613_, v_entry_4614_);
v___x_4616_ = ((size_t)1ULL);
v___x_4617_ = lean_usize_add(v_i_4608_, v___x_4616_);
v_i_4608_ = v___x_4617_;
v_b_4610_ = v___x_4615_;
goto _start;
}
else
{
return v_b_4610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4619_, lean_object* v_i_4620_, lean_object* v_stop_4621_, lean_object* v_b_4622_){
_start:
{
size_t v_i_boxed_4623_; size_t v_stop_boxed_4624_; lean_object* v_res_4625_; 
v_i_boxed_4623_ = lean_unbox_usize(v_i_4620_);
lean_dec(v_i_4620_);
v_stop_boxed_4624_ = lean_unbox_usize(v_stop_4621_);
lean_dec(v_stop_4621_);
v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4619_, v_i_boxed_4623_, v_stop_boxed_4624_, v_b_4622_);
lean_dec_ref(v_as_4619_);
return v_res_4625_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4626_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
return v___x_4628_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4629_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4630_ = lean_unsigned_to_nat(0u);
v___x_4631_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
lean_ctor_set(v___x_4631_, 2, v___x_4630_);
lean_ctor_set(v___x_4631_, 3, v___x_4630_);
lean_ctor_set(v___x_4631_, 4, v___x_4629_);
lean_ctor_set(v___x_4631_, 5, v___x_4629_);
lean_ctor_set(v___x_4631_, 6, v___x_4629_);
lean_ctor_set(v___x_4631_, 7, v___x_4629_);
lean_ctor_set(v___x_4631_, 8, v___x_4629_);
lean_ctor_set(v___x_4631_, 9, v___x_4629_);
lean_ctor_set(v___x_4631_, 10, v___x_4629_);
return v___x_4631_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4632_ = lean_unsigned_to_nat(32u);
v___x_4633_ = lean_mk_empty_array_with_capacity(v___x_4632_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4633_);
return v___x_4634_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4635_ = ((size_t)5ULL);
v___x_4636_ = lean_unsigned_to_nat(0u);
v___x_4637_ = lean_unsigned_to_nat(32u);
v___x_4638_ = lean_mk_empty_array_with_capacity(v___x_4637_);
v___x_4639_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4640_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v___x_4638_);
lean_ctor_set(v___x_4640_, 2, v___x_4636_);
lean_ctor_set(v___x_4640_, 3, v___x_4636_);
lean_ctor_set_usize(v___x_4640_, 4, v___x_4635_);
return v___x_4640_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
lean_ctor_set(v___x_4642_, 2, v___x_4641_);
lean_ctor_set(v___x_4642_, 3, v___x_4641_);
lean_ctor_set(v___x_4642_, 4, v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4643_ = lean_box(1);
v___x_4644_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4645_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
lean_ctor_set(v___x_4646_, 1, v___x_4644_);
lean_ctor_set(v___x_4646_, 2, v___x_4643_);
return v___x_4646_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4649_ = lean_unsigned_to_nat(1u);
v___x_4650_ = l_Lean_firstFrontendMacroScope;
v___x_4651_ = lean_nat_add(v___x_4650_, v___x_4649_);
return v___x_4651_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4656_; uint64_t v___x_4657_; lean_object* v___x_4658_; 
v___x_4656_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4657_ = 0ULL;
v___x_4658_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4658_, 0, v___x_4656_);
lean_ctor_set_uint64(v___x_4658_, sizeof(void*)*1, v___x_4657_);
return v___x_4658_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4659_ = l_Lean_NameSet_empty;
v___x_4660_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4660_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
lean_ctor_set(v___x_4661_, 2, v___x_4659_);
return v___x_4661_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; lean_object* v___x_4665_; 
v___x_4662_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4663_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4664_ = 1;
v___x_4665_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4665_, 0, v___x_4663_);
lean_ctor_set(v___x_4665_, 1, v___x_4663_);
lean_ctor_set(v___x_4665_, 2, v___x_4662_);
lean_ctor_set_uint8(v___x_4665_, sizeof(void*)*3, v___x_4664_);
return v___x_4665_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
lean_ctor_set(v___x_4667_, 1, v___x_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4668_, lean_object* v_env_4669_, lean_object* v_modName_4670_, lean_object* v_d_4671_, lean_object* v_cacheRef_4672_, lean_object* v_tree_4673_, lean_object* v_act_4674_, lean_object* v_c_4675_){
_start:
{
uint8_t v___x_4677_; 
lean_inc_ref(v_c_4675_);
v___x_4677_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_4675_);
if (v___x_4677_ == 0)
{
lean_object* v_name_4678_; uint8_t v___x_4679_; 
v_name_4678_ = lean_ctor_get(v_c_4675_, 0);
lean_inc_n(v_name_4678_, 2);
lean_inc_ref(v_env_4669_);
v___x_4679_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4669_, v_name_4678_);
if (v___x_4679_ == 0)
{
lean_object* v___x_4680_; lean_object* v_ngen_4681_; lean_object* v_core_4682_; lean_object* v_meta_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4821_; 
v___x_4680_ = lean_st_ref_get(v_cacheRef_4672_);
v_ngen_4681_ = lean_ctor_get(v___x_4680_, 0);
v_core_4682_ = lean_ctor_get(v___x_4680_, 1);
v_meta_4683_ = lean_ctor_get(v___x_4680_, 2);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4685_ = v___x_4680_;
v_isShared_4686_ = v_isSharedCheck_4821_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_meta_4683_);
lean_inc(v_core_4682_);
lean_inc(v_ngen_4681_);
lean_dec(v___x_4680_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4821_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; uint8_t v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; uint8_t v___x_4697_; uint8_t v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v_toCold_4715_; lean_object* v_options_4716_; lean_object* v_currRecDepth_4717_; lean_object* v_maxRecDepth_4718_; lean_object* v_ref_4719_; lean_object* v_currNamespace_4720_; lean_object* v_openDecls_4721_; lean_object* v_initHeartbeats_4722_; lean_object* v_maxHeartbeats_4723_; lean_object* v_currMacroScope_4724_; uint8_t v_diag_4725_; uint8_t v_suppressElabErrors_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4820_; 
v___x_4687_ = lean_unsigned_to_nat(0u);
v___x_4688_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4689_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4690_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4681_);
v___x_4691_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4681_);
v___x_4692_ = lean_st_ref_swap(v_cacheRef_4672_, v___x_4691_);
lean_dec(v___x_4692_);
v___x_4693_ = lean_box(1);
v___x_4694_ = 1;
v___x_4695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4688_);
lean_ctor_set(v___x_4695_, 1, v_meta_4683_);
lean_ctor_set(v___x_4695_, 2, v___x_4693_);
lean_ctor_set(v___x_4695_, 3, v___x_4689_);
lean_ctor_set(v___x_4695_, 4, v___x_4690_);
v___x_4696_ = 2;
v___x_4697_ = 0;
v___x_4698_ = 2;
v___x_4699_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_4699_, 0, v___x_4679_);
lean_ctor_set_uint8(v___x_4699_, 1, v___x_4679_);
lean_ctor_set_uint8(v___x_4699_, 2, v___x_4679_);
lean_ctor_set_uint8(v___x_4699_, 3, v___x_4679_);
lean_ctor_set_uint8(v___x_4699_, 4, v___x_4679_);
lean_ctor_set_uint8(v___x_4699_, 5, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 6, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 7, v___x_4679_);
lean_ctor_set_uint8(v___x_4699_, 8, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 9, v___x_4696_);
lean_ctor_set_uint8(v___x_4699_, 10, v___x_4697_);
lean_ctor_set_uint8(v___x_4699_, 11, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 12, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 13, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 14, v___x_4698_);
lean_ctor_set_uint8(v___x_4699_, 15, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 16, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 17, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 18, v___x_4694_);
lean_ctor_set_uint8(v___x_4699_, 19, v___x_4679_);
v___x_4700_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4699_);
v___x_4701_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4702_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4703_ = lean_box(0);
v___x_4704_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4704_, 0, v___x_4700_);
lean_ctor_set(v___x_4704_, 1, v___x_4693_);
lean_ctor_set(v___x_4704_, 2, v___x_4701_);
lean_ctor_set(v___x_4704_, 3, v___x_4702_);
lean_ctor_set(v___x_4704_, 4, v___x_4703_);
lean_ctor_set(v___x_4704_, 5, v___x_4687_);
lean_ctor_set(v___x_4704_, 6, v___x_4703_);
lean_ctor_set_uint8(v___x_4704_, sizeof(void*)*7, v___x_4679_);
lean_ctor_set_uint8(v___x_4704_, sizeof(void*)*7 + 1, v___x_4679_);
lean_ctor_set_uint8(v___x_4704_, sizeof(void*)*7 + 2, v___x_4679_);
lean_ctor_set_uint8(v___x_4704_, sizeof(void*)*7 + 3, v___x_4694_);
v___x_4705_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4706_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4707_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4708_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4709_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4710_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4710_, 0, v_env_4669_);
lean_ctor_set(v___x_4710_, 1, v___x_4705_);
lean_ctor_set(v___x_4710_, 2, v_ngen_4681_);
lean_ctor_set(v___x_4710_, 3, v___x_4706_);
lean_ctor_set(v___x_4710_, 4, v___x_4707_);
lean_ctor_set(v___x_4710_, 5, v_core_4682_);
lean_ctor_set(v___x_4710_, 6, v___x_4708_);
lean_ctor_set(v___x_4710_, 7, v___x_4709_);
lean_ctor_set(v___x_4710_, 8, v___x_4702_);
v___x_4711_ = lean_st_mk_ref(v___x_4710_);
v___x_4712_ = l_Lean_inheritedTraceOptions;
v___x_4713_ = lean_st_ref_get(v___x_4712_);
v___x_4714_ = lean_st_ref_get(v___x_4711_);
v_toCold_4715_ = lean_ctor_get(v_cctx_4668_, 0);
v_options_4716_ = lean_ctor_get(v_cctx_4668_, 1);
v_currRecDepth_4717_ = lean_ctor_get(v_cctx_4668_, 2);
v_maxRecDepth_4718_ = lean_ctor_get(v_cctx_4668_, 3);
v_ref_4719_ = lean_ctor_get(v_cctx_4668_, 4);
v_currNamespace_4720_ = lean_ctor_get(v_cctx_4668_, 5);
v_openDecls_4721_ = lean_ctor_get(v_cctx_4668_, 6);
v_initHeartbeats_4722_ = lean_ctor_get(v_cctx_4668_, 7);
v_maxHeartbeats_4723_ = lean_ctor_get(v_cctx_4668_, 8);
v_currMacroScope_4724_ = lean_ctor_get(v_cctx_4668_, 9);
v_diag_4725_ = lean_ctor_get_uint8(v_cctx_4668_, sizeof(void*)*10);
v_suppressElabErrors_4726_ = lean_ctor_get_uint8(v_cctx_4668_, sizeof(void*)*10 + 1);
v_isSharedCheck_4820_ = !lean_is_exclusive(v_cctx_4668_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4728_ = v_cctx_4668_;
v_isShared_4729_ = v_isSharedCheck_4820_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_currMacroScope_4724_);
lean_inc(v_maxHeartbeats_4723_);
lean_inc(v_initHeartbeats_4722_);
lean_inc(v_openDecls_4721_);
lean_inc(v_currNamespace_4720_);
lean_inc(v_ref_4719_);
lean_inc(v_maxRecDepth_4718_);
lean_inc(v_currRecDepth_4717_);
lean_inc(v_options_4716_);
lean_inc(v_toCold_4715_);
lean_dec(v_cctx_4668_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4820_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v_fileName_4730_; lean_object* v_fileMap_4731_; lean_object* v_quotContext_4732_; lean_object* v_cancelTk_x3f_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4818_; 
v_fileName_4730_ = lean_ctor_get(v_toCold_4715_, 0);
v_fileMap_4731_ = lean_ctor_get(v_toCold_4715_, 1);
v_quotContext_4732_ = lean_ctor_get(v_toCold_4715_, 2);
v_cancelTk_x3f_4733_ = lean_ctor_get(v_toCold_4715_, 3);
v_isSharedCheck_4818_ = !lean_is_exclusive(v_toCold_4715_);
if (v_isSharedCheck_4818_ == 0)
{
lean_object* v_unused_4819_; 
v_unused_4819_ = lean_ctor_get(v_toCold_4715_, 4);
lean_dec(v_unused_4819_);
v___x_4735_ = v_toCold_4715_;
v_isShared_4736_ = v_isSharedCheck_4818_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_cancelTk_x3f_4733_);
lean_inc(v_quotContext_4732_);
lean_inc(v_fileMap_4731_);
lean_inc(v_fileName_4730_);
lean_dec(v_toCold_4715_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4818_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v_env_4737_; lean_object* v___x_4739_; 
v_env_4737_ = lean_ctor_get(v___x_4714_, 0);
lean_inc_ref(v_env_4737_);
lean_dec(v___x_4714_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 4, v___x_4713_);
v___x_4739_ = v___x_4735_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_fileName_4730_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_fileMap_4731_);
lean_ctor_set(v_reuseFailAlloc_4817_, 2, v_quotContext_4732_);
lean_ctor_set(v_reuseFailAlloc_4817_, 3, v_cancelTk_x3f_4733_);
lean_ctor_set(v_reuseFailAlloc_4817_, 4, v___x_4713_);
v___x_4739_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
lean_object* v___x_4741_; 
lean_inc_ref(v_options_4716_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v___x_4739_);
v___x_4741_ = v___x_4728_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4739_);
lean_ctor_set(v_reuseFailAlloc_4816_, 1, v_options_4716_);
lean_ctor_set(v_reuseFailAlloc_4816_, 2, v_currRecDepth_4717_);
lean_ctor_set(v_reuseFailAlloc_4816_, 3, v_maxRecDepth_4718_);
lean_ctor_set(v_reuseFailAlloc_4816_, 4, v_ref_4719_);
lean_ctor_set(v_reuseFailAlloc_4816_, 5, v_currNamespace_4720_);
lean_ctor_set(v_reuseFailAlloc_4816_, 6, v_openDecls_4721_);
lean_ctor_set(v_reuseFailAlloc_4816_, 7, v_initHeartbeats_4722_);
lean_ctor_set(v_reuseFailAlloc_4816_, 8, v_maxHeartbeats_4723_);
lean_ctor_set(v_reuseFailAlloc_4816_, 9, v_currMacroScope_4724_);
lean_ctor_set_uint8(v_reuseFailAlloc_4816_, sizeof(void*)*10, v_diag_4725_);
lean_ctor_set_uint8(v_reuseFailAlloc_4816_, sizeof(void*)*10 + 1, v_suppressElabErrors_4726_);
v___x_4741_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
lean_object* v___x_4742_; uint8_t v___x_4743_; lean_object* v___y_4745_; lean_object* v___y_4746_; uint8_t v___y_4794_; uint8_t v___x_4815_; 
v___x_4742_ = l_Lean_diagnostics;
v___x_4743_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4716_, v___x_4742_);
v___x_4815_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4737_);
lean_dec_ref(v_env_4737_);
if (v___x_4743_ == 0)
{
if (v___x_4815_ == 0)
{
lean_inc(v___x_4711_);
v___y_4745_ = v___x_4741_;
v___y_4746_ = v___x_4711_;
goto v___jp_4744_;
}
else
{
v___y_4794_ = v___x_4743_;
goto v___jp_4793_;
}
}
else
{
v___y_4794_ = v___x_4815_;
goto v___jp_4793_;
}
v___jp_4744_:
{
lean_object* v___x_4747_; lean_object* v_toCold_4748_; lean_object* v_currRecDepth_4749_; lean_object* v_ref_4750_; lean_object* v_currNamespace_4751_; lean_object* v_openDecls_4752_; lean_object* v_initHeartbeats_4753_; lean_object* v_maxHeartbeats_4754_; lean_object* v_currMacroScope_4755_; uint8_t v_suppressElabErrors_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4790_; 
v___x_4747_ = lean_st_mk_ref(v___x_4695_);
v_toCold_4748_ = lean_ctor_get(v___y_4745_, 0);
v_currRecDepth_4749_ = lean_ctor_get(v___y_4745_, 2);
v_ref_4750_ = lean_ctor_get(v___y_4745_, 4);
v_currNamespace_4751_ = lean_ctor_get(v___y_4745_, 5);
v_openDecls_4752_ = lean_ctor_get(v___y_4745_, 6);
v_initHeartbeats_4753_ = lean_ctor_get(v___y_4745_, 7);
v_maxHeartbeats_4754_ = lean_ctor_get(v___y_4745_, 8);
v_currMacroScope_4755_ = lean_ctor_get(v___y_4745_, 9);
v_suppressElabErrors_4756_ = lean_ctor_get_uint8(v___y_4745_, sizeof(void*)*10 + 1);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___y_4745_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; lean_object* v_unused_4792_; 
v_unused_4791_ = lean_ctor_get(v___y_4745_, 3);
lean_dec(v_unused_4791_);
v_unused_4792_ = lean_ctor_get(v___y_4745_, 1);
lean_dec(v_unused_4792_);
v___x_4758_ = v___y_4745_;
v_isShared_4759_ = v_isSharedCheck_4790_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_currMacroScope_4755_);
lean_inc(v_maxHeartbeats_4754_);
lean_inc(v_initHeartbeats_4753_);
lean_inc(v_openDecls_4752_);
lean_inc(v_currNamespace_4751_);
lean_inc(v_ref_4750_);
lean_inc(v_currRecDepth_4749_);
lean_inc(v_toCold_4748_);
lean_dec(v___y_4745_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4790_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4763_; 
v___x_4760_ = l_Lean_maxRecDepth;
v___x_4761_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4716_, v___x_4760_);
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 3, v___x_4761_);
lean_ctor_set(v___x_4758_, 1, v_options_4716_);
v___x_4763_ = v___x_4758_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_toCold_4748_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_options_4716_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_currRecDepth_4749_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v___x_4761_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_ref_4750_);
lean_ctor_set(v_reuseFailAlloc_4789_, 5, v_currNamespace_4751_);
lean_ctor_set(v_reuseFailAlloc_4789_, 6, v_openDecls_4752_);
lean_ctor_set(v_reuseFailAlloc_4789_, 7, v_initHeartbeats_4753_);
lean_ctor_set(v_reuseFailAlloc_4789_, 8, v_maxHeartbeats_4754_);
lean_ctor_set(v_reuseFailAlloc_4789_, 9, v_currMacroScope_4755_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*10 + 1, v_suppressElabErrors_4756_);
v___x_4763_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4764_; 
lean_ctor_set_uint8(v___x_4763_, sizeof(void*)*10, v___x_4743_);
lean_inc(v___x_4747_);
lean_inc(v_name_4678_);
v___x_4764_ = lean_apply_7(v_act_4674_, v_name_4678_, v_c_4675_, v___x_4704_, v___x_4747_, v___x_4763_, v___y_4746_, lean_box(0));
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v_ngen_4768_; lean_object* v_cache_4769_; lean_object* v_cache_4770_; lean_object* v___x_4772_; 
lean_dec(v_name_4678_);
lean_dec(v_modName_4670_);
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4766_ = lean_st_ref_get(v___x_4747_);
lean_dec(v___x_4747_);
v___x_4767_ = lean_st_ref_get(v___x_4711_);
lean_dec(v___x_4711_);
v_ngen_4768_ = lean_ctor_get(v___x_4767_, 2);
lean_inc_ref(v_ngen_4768_);
v_cache_4769_ = lean_ctor_get(v___x_4767_, 5);
lean_inc_ref(v_cache_4769_);
lean_dec(v___x_4767_);
v_cache_4770_ = lean_ctor_get(v___x_4766_, 1);
lean_inc_ref(v_cache_4770_);
lean_dec(v___x_4766_);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 2, v_cache_4770_);
lean_ctor_set(v___x_4685_, 1, v_cache_4769_);
lean_ctor_set(v___x_4685_, 0, v_ngen_4768_);
v___x_4772_ = v___x_4685_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_ngen_4768_);
lean_ctor_set(v_reuseFailAlloc_4783_, 1, v_cache_4769_);
lean_ctor_set(v_reuseFailAlloc_4783_, 2, v_cache_4770_);
v___x_4772_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; 
v___x_4773_ = lean_st_ref_swap(v_cacheRef_4672_, v___x_4772_);
lean_dec(v___x_4773_);
v___x_4774_ = lean_array_get_size(v_a_4765_);
v___x_4775_ = lean_nat_dec_lt(v___x_4687_, v___x_4774_);
if (v___x_4775_ == 0)
{
lean_dec(v_a_4765_);
return v_tree_4673_;
}
else
{
uint8_t v___x_4776_; 
v___x_4776_ = lean_nat_dec_le(v___x_4774_, v___x_4774_);
if (v___x_4776_ == 0)
{
if (v___x_4775_ == 0)
{
lean_dec(v_a_4765_);
return v_tree_4673_;
}
else
{
size_t v___x_4777_; size_t v___x_4778_; lean_object* v___x_4779_; 
v___x_4777_ = ((size_t)0ULL);
v___x_4778_ = lean_usize_of_nat(v___x_4774_);
v___x_4779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4765_, v___x_4777_, v___x_4778_, v_tree_4673_);
lean_dec(v_a_4765_);
return v___x_4779_;
}
}
else
{
size_t v___x_4780_; size_t v___x_4781_; lean_object* v___x_4782_; 
v___x_4780_ = ((size_t)0ULL);
v___x_4781_ = lean_usize_of_nat(v___x_4774_);
v___x_4782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4765_, v___x_4780_, v___x_4781_, v_tree_4673_);
lean_dec(v_a_4765_);
return v___x_4782_;
}
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
lean_dec(v___x_4747_);
lean_dec(v___x_4711_);
lean_del_object(v___x_4685_);
v_a_4784_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4785_ = lean_st_ref_take(v_d_4671_);
v___x_4786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4786_, 0, v_modName_4670_);
lean_ctor_set(v___x_4786_, 1, v_name_4678_);
lean_ctor_set(v___x_4786_, 2, v_a_4784_);
v___x_4787_ = lean_array_push(v___x_4785_, v___x_4786_);
v___x_4788_ = lean_st_ref_put(v_d_4671_, v___x_4787_);
return v_tree_4673_;
}
}
}
}
v___jp_4793_:
{
if (v___y_4794_ == 0)
{
lean_object* v___x_4795_; lean_object* v_env_4796_; lean_object* v_nextMacroScope_4797_; lean_object* v_ngen_4798_; lean_object* v_auxDeclNGen_4799_; lean_object* v_traceState_4800_; lean_object* v_messages_4801_; lean_object* v_infoState_4802_; lean_object* v_snapshotTasks_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4813_; 
v___x_4795_ = lean_st_ref_take(v___x_4711_);
v_env_4796_ = lean_ctor_get(v___x_4795_, 0);
v_nextMacroScope_4797_ = lean_ctor_get(v___x_4795_, 1);
v_ngen_4798_ = lean_ctor_get(v___x_4795_, 2);
v_auxDeclNGen_4799_ = lean_ctor_get(v___x_4795_, 3);
v_traceState_4800_ = lean_ctor_get(v___x_4795_, 4);
v_messages_4801_ = lean_ctor_get(v___x_4795_, 6);
v_infoState_4802_ = lean_ctor_get(v___x_4795_, 7);
v_snapshotTasks_4803_ = lean_ctor_get(v___x_4795_, 8);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4813_ == 0)
{
lean_object* v_unused_4814_; 
v_unused_4814_ = lean_ctor_get(v___x_4795_, 5);
lean_dec(v_unused_4814_);
v___x_4805_ = v___x_4795_;
v_isShared_4806_ = v_isSharedCheck_4813_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_snapshotTasks_4803_);
lean_inc(v_infoState_4802_);
lean_inc(v_messages_4801_);
lean_inc(v_traceState_4800_);
lean_inc(v_auxDeclNGen_4799_);
lean_inc(v_ngen_4798_);
lean_inc(v_nextMacroScope_4797_);
lean_inc(v_env_4796_);
lean_dec(v___x_4795_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4813_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4810_; 
v___x_4807_ = l_Lean_Kernel_enableDiag(v_env_4796_, v___x_4743_);
v___x_4808_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4806_ == 0)
{
lean_ctor_set(v___x_4805_, 5, v___x_4808_);
lean_ctor_set(v___x_4805_, 0, v___x_4807_);
v___x_4810_ = v___x_4805_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4807_);
lean_ctor_set(v_reuseFailAlloc_4812_, 1, v_nextMacroScope_4797_);
lean_ctor_set(v_reuseFailAlloc_4812_, 2, v_ngen_4798_);
lean_ctor_set(v_reuseFailAlloc_4812_, 3, v_auxDeclNGen_4799_);
lean_ctor_set(v_reuseFailAlloc_4812_, 4, v_traceState_4800_);
lean_ctor_set(v_reuseFailAlloc_4812_, 5, v___x_4808_);
lean_ctor_set(v_reuseFailAlloc_4812_, 6, v_messages_4801_);
lean_ctor_set(v_reuseFailAlloc_4812_, 7, v_infoState_4802_);
lean_ctor_set(v_reuseFailAlloc_4812_, 8, v_snapshotTasks_4803_);
v___x_4810_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
lean_object* v___x_4811_; 
v___x_4811_ = lean_st_ref_put(v___x_4711_, v___x_4810_);
lean_inc(v___x_4711_);
v___y_4745_ = v___x_4741_;
v___y_4746_ = v___x_4711_;
goto v___jp_4744_;
}
}
}
else
{
lean_inc(v___x_4711_);
v___y_4745_ = v___x_4741_;
v___y_4746_ = v___x_4711_;
goto v___jp_4744_;
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
lean_dec(v_name_4678_);
lean_dec_ref(v_c_4675_);
lean_dec_ref(v_act_4674_);
lean_dec(v_modName_4670_);
lean_dec_ref(v_env_4669_);
lean_dec_ref(v_cctx_4668_);
return v_tree_4673_;
}
}
else
{
lean_dec_ref(v_c_4675_);
lean_dec_ref(v_act_4674_);
lean_dec(v_modName_4670_);
lean_dec_ref(v_env_4669_);
lean_dec_ref(v_cctx_4668_);
return v_tree_4673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4822_, lean_object* v_env_4823_, lean_object* v_modName_4824_, lean_object* v_d_4825_, lean_object* v_cacheRef_4826_, lean_object* v_tree_4827_, lean_object* v_act_4828_, lean_object* v_c_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4822_, v_env_4823_, v_modName_4824_, v_d_4825_, v_cacheRef_4826_, v_tree_4827_, v_act_4828_, v_c_4829_);
lean_dec(v_cacheRef_4826_);
lean_dec(v_d_4825_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4832_, lean_object* v_cctx_4833_, lean_object* v_env_4834_, lean_object* v_modName_4835_, lean_object* v_d_4836_, lean_object* v_cacheRef_4837_, lean_object* v_tree_4838_, lean_object* v_act_4839_, lean_object* v_c_4840_){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4833_, v_env_4834_, v_modName_4835_, v_d_4836_, v_cacheRef_4837_, v_tree_4838_, v_act_4839_, v_c_4840_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4843_, lean_object* v_cctx_4844_, lean_object* v_env_4845_, lean_object* v_modName_4846_, lean_object* v_d_4847_, lean_object* v_cacheRef_4848_, lean_object* v_tree_4849_, lean_object* v_act_4850_, lean_object* v_c_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4843_, v_cctx_4844_, v_env_4845_, v_modName_4846_, v_d_4847_, v_cacheRef_4848_, v_tree_4849_, v_act_4850_, v_c_4851_);
lean_dec(v_cacheRef_4848_);
lean_dec(v_d_4847_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4854_, lean_object* v_as_4855_, size_t v_i_4856_, size_t v_stop_4857_, lean_object* v_b_4858_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4855_, v_i_4856_, v_stop_4857_, v_b_4858_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4860_, lean_object* v_as_4861_, lean_object* v_i_4862_, lean_object* v_stop_4863_, lean_object* v_b_4864_){
_start:
{
size_t v_i_boxed_4865_; size_t v_stop_boxed_4866_; lean_object* v_res_4867_; 
v_i_boxed_4865_ = lean_unbox_usize(v_i_4862_);
lean_dec(v_i_4862_);
v_stop_boxed_4866_ = lean_unbox_usize(v_stop_4863_);
lean_dec(v_stop_4863_);
v_res_4867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4860_, v_as_4861_, v_i_boxed_4865_, v_stop_boxed_4866_, v_b_4864_);
lean_dec_ref(v_as_4861_);
return v_res_4867_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0(void){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4868_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4869_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_4870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
lean_ctor_set(v___x_4870_, 1, v___x_4868_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4871_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4873_, lean_object* v_y_4874_){
_start:
{
lean_object* v_tree_4875_; lean_object* v_errors_4876_; lean_object* v_tree_4877_; lean_object* v_errors_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4887_; 
v_tree_4875_ = lean_ctor_get(v_x_4873_, 0);
lean_inc_ref(v_tree_4875_);
v_errors_4876_ = lean_ctor_get(v_x_4873_, 1);
lean_inc_ref(v_errors_4876_);
lean_dec_ref(v_x_4873_);
v_tree_4877_ = lean_ctor_get(v_y_4874_, 0);
v_errors_4878_ = lean_ctor_get(v_y_4874_, 1);
v_isSharedCheck_4887_ = !lean_is_exclusive(v_y_4874_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4880_ = v_y_4874_;
v_isShared_4881_ = v_isSharedCheck_4887_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_errors_4878_);
lean_inc(v_tree_4877_);
lean_dec(v_y_4874_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4887_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4882_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4875_, v_tree_4877_);
v___x_4883_ = l_Array_append___redArg(v_errors_4876_, v_errors_4878_);
lean_dec_ref(v_errors_4878_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 1, v___x_4883_);
lean_ctor_set(v___x_4880_, 0, v___x_4882_);
v___x_4885_ = v___x_4880_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4888_, lean_object* v_x_4889_, lean_object* v_y_4890_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4889_, v_y_4890_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4893_){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4895_, lean_object* v_tree_4896_){
_start:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4898_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4899_ = lean_st_ref_swap(v_d_4895_, v___x_4898_);
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v_tree_4896_);
lean_ctor_set(v___x_4900_, 1, v___x_4899_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4901_, lean_object* v_tree_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4901_, v_tree_4902_);
lean_dec(v_d_4901_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4905_, lean_object* v_d_4906_, lean_object* v_tree_4907_){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4906_, v_tree_4907_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4910_, lean_object* v_d_4911_, lean_object* v_tree_4912_, lean_object* v_a_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4910_, v_d_4911_, v_tree_4912_);
lean_dec(v_d_4911_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4915_, lean_object* v_env_4916_, lean_object* v_act_4917_, lean_object* v_d_4918_, lean_object* v_cacheRef_4919_, lean_object* v_tree_4920_, lean_object* v_mname_4921_, lean_object* v_mdata_4922_, lean_object* v_i_4923_){
_start:
{
lean_object* v_constants_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
v_constants_4925_ = lean_ctor_get(v_mdata_4922_, 2);
v___x_4926_ = lean_array_get_size(v_constants_4925_);
v___x_4927_ = lean_nat_dec_lt(v_i_4923_, v___x_4926_);
if (v___x_4927_ == 0)
{
lean_dec(v_i_4923_);
lean_dec(v_mname_4921_);
lean_dec_ref(v_act_4917_);
lean_dec_ref(v_env_4916_);
lean_dec_ref(v_cctx_4915_);
return v_tree_4920_;
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4928_ = lean_array_fget_borrowed(v_constants_4925_, v_i_4923_);
lean_inc(v___x_4928_);
v___x_4929_ = l_Lean_AsyncConstantInfo_ofConstantInfo(v___x_4928_);
lean_inc_ref(v_act_4917_);
lean_inc(v_mname_4921_);
lean_inc_ref(v_env_4916_);
lean_inc_ref(v_cctx_4915_);
v___x_4930_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4915_, v_env_4916_, v_mname_4921_, v_d_4918_, v_cacheRef_4919_, v_tree_4920_, v_act_4917_, v___x_4929_);
v___x_4931_ = lean_unsigned_to_nat(1u);
v___x_4932_ = lean_nat_add(v_i_4923_, v___x_4931_);
lean_dec(v_i_4923_);
v_tree_4920_ = v___x_4930_;
v_i_4923_ = v___x_4932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4934_, lean_object* v_env_4935_, lean_object* v_act_4936_, lean_object* v_d_4937_, lean_object* v_cacheRef_4938_, lean_object* v_tree_4939_, lean_object* v_mname_4940_, lean_object* v_mdata_4941_, lean_object* v_i_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4934_, v_env_4935_, v_act_4936_, v_d_4937_, v_cacheRef_4938_, v_tree_4939_, v_mname_4940_, v_mdata_4941_, v_i_4942_);
lean_dec_ref(v_mdata_4941_);
lean_dec(v_cacheRef_4938_);
lean_dec(v_d_4937_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4945_, lean_object* v_cctx_4946_, lean_object* v_env_4947_, lean_object* v_act_4948_, lean_object* v_d_4949_, lean_object* v_cacheRef_4950_, lean_object* v_tree_4951_, lean_object* v_mname_4952_, lean_object* v_mdata_4953_, lean_object* v_i_4954_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4946_, v_env_4947_, v_act_4948_, v_d_4949_, v_cacheRef_4950_, v_tree_4951_, v_mname_4952_, v_mdata_4953_, v_i_4954_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4957_, lean_object* v_cctx_4958_, lean_object* v_env_4959_, lean_object* v_act_4960_, lean_object* v_d_4961_, lean_object* v_cacheRef_4962_, lean_object* v_tree_4963_, lean_object* v_mname_4964_, lean_object* v_mdata_4965_, lean_object* v_i_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4957_, v_cctx_4958_, v_env_4959_, v_act_4960_, v_d_4961_, v_cacheRef_4962_, v_tree_4963_, v_mname_4964_, v_mdata_4965_, v_i_4966_);
lean_dec_ref(v_mdata_4965_);
lean_dec(v_cacheRef_4962_);
lean_dec(v_d_4961_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4969_, lean_object* v_env_4970_, lean_object* v_act_4971_, lean_object* v_d_4972_, lean_object* v_cacheRef_4973_, lean_object* v_tree_4974_, lean_object* v_start_4975_, lean_object* v_stop_4976_){
_start:
{
uint8_t v___x_4978_; 
v___x_4978_ = lean_nat_dec_lt(v_start_4975_, v_stop_4976_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; 
lean_dec(v_start_4975_);
lean_dec_ref(v_act_4971_);
lean_dec_ref(v_env_4970_);
lean_dec_ref(v_cctx_4969_);
v___x_4979_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4972_, v_tree_4974_);
return v___x_4979_;
}
else
{
lean_object* v___x_4980_; lean_object* v_moduleData_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v_mname_4985_; lean_object* v_mdata_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4980_ = l_Lean_Environment_header(v_env_4970_);
v_moduleData_4981_ = lean_ctor_get(v___x_4980_, 6);
lean_inc_ref(v_moduleData_4981_);
v___x_4982_ = lean_box(0);
v___x_4983_ = l_Lean_instInhabitedModuleData_default;
v___x_4984_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4980_);
v_mname_4985_ = lean_array_get(v___x_4982_, v___x_4984_, v_start_4975_);
lean_dec_ref(v___x_4984_);
v_mdata_4986_ = lean_array_get(v___x_4983_, v_moduleData_4981_, v_start_4975_);
lean_dec_ref(v_moduleData_4981_);
v___x_4987_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4971_);
lean_inc_ref(v_env_4970_);
lean_inc_ref(v_cctx_4969_);
v___x_4988_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4969_, v_env_4970_, v_act_4971_, v_d_4972_, v_cacheRef_4973_, v_tree_4974_, v_mname_4985_, v_mdata_4986_, v___x_4987_);
lean_dec(v_mdata_4986_);
v___x_4989_ = lean_unsigned_to_nat(1u);
v___x_4990_ = lean_nat_add(v_start_4975_, v___x_4989_);
lean_dec(v_start_4975_);
v_tree_4974_ = v___x_4988_;
v_start_4975_ = v___x_4990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4992_, lean_object* v_env_4993_, lean_object* v_act_4994_, lean_object* v_d_4995_, lean_object* v_cacheRef_4996_, lean_object* v_tree_4997_, lean_object* v_start_4998_, lean_object* v_stop_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4992_, v_env_4993_, v_act_4994_, v_d_4995_, v_cacheRef_4996_, v_tree_4997_, v_start_4998_, v_stop_4999_);
lean_dec(v_stop_4999_);
lean_dec(v_cacheRef_4996_);
lean_dec(v_d_4995_);
return v_res_5001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_5002_, lean_object* v_cctx_5003_, lean_object* v_env_5004_, lean_object* v_act_5005_, lean_object* v_d_5006_, lean_object* v_cacheRef_5007_, lean_object* v_tree_5008_, lean_object* v_start_5009_, lean_object* v_stop_5010_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5003_, v_env_5004_, v_act_5005_, v_d_5006_, v_cacheRef_5007_, v_tree_5008_, v_start_5009_, v_stop_5010_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5013_, lean_object* v_cctx_5014_, lean_object* v_env_5015_, lean_object* v_act_5016_, lean_object* v_d_5017_, lean_object* v_cacheRef_5018_, lean_object* v_tree_5019_, lean_object* v_start_5020_, lean_object* v_stop_5021_, lean_object* v_a_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5013_, v_cctx_5014_, v_env_5015_, v_act_5016_, v_d_5017_, v_cacheRef_5018_, v_tree_5019_, v_start_5020_, v_stop_5021_);
lean_dec(v_stop_5021_);
lean_dec(v_cacheRef_5018_);
lean_dec(v_d_5017_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5024_, lean_object* v_ngen_5025_, lean_object* v_env_5026_, lean_object* v_act_5027_, lean_object* v_start_5028_, lean_object* v_stop_5029_){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5031_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5025_);
v___x_5032_ = lean_st_mk_ref(v___x_5031_);
v___x_5033_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5034_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v___x_5035_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5024_, v_env_5026_, v_act_5027_, v___x_5033_, v___x_5032_, v___x_5034_, v_start_5028_, v_stop_5029_);
lean_dec(v___x_5032_);
lean_dec(v___x_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5036_, lean_object* v_ngen_5037_, lean_object* v_env_5038_, lean_object* v_act_5039_, lean_object* v_start_5040_, lean_object* v_stop_5041_, lean_object* v_a_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5036_, v_ngen_5037_, v_env_5038_, v_act_5039_, v_start_5040_, v_stop_5041_);
lean_dec(v_stop_5041_);
return v_res_5043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5044_, lean_object* v_cctx_5045_, lean_object* v_ngen_5046_, lean_object* v_env_5047_, lean_object* v_act_5048_, lean_object* v_start_5049_, lean_object* v_stop_5050_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5045_, v_ngen_5046_, v_env_5047_, v_act_5048_, v_start_5049_, v_stop_5050_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5053_, lean_object* v_cctx_5054_, lean_object* v_ngen_5055_, lean_object* v_env_5056_, lean_object* v_act_5057_, lean_object* v_start_5058_, lean_object* v_stop_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5053_, v_cctx_5054_, v_ngen_5055_, v_env_5056_, v_act_5057_, v_start_5058_, v_stop_5059_);
lean_dec(v_stop_5059_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5062_, lean_object* v_x1_5063_, lean_object* v_x2_5064_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = lean_task_get_own(v_x2_5064_);
v___x_5066_ = lean_apply_2(v_inst_5062_, v_x1_5063_, v___x_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5067_, lean_object* v_z_5068_, lean_object* v_tasks_5069_){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; uint8_t v___x_5073_; 
v___x_5070_ = lean_unsigned_to_nat(0u);
v___x_5071_ = lean_array_get_size(v_tasks_5069_);
v___x_5072_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5073_ = lean_nat_dec_lt(v___x_5070_, v___x_5071_);
if (v___x_5073_ == 0)
{
lean_dec_ref(v_tasks_5069_);
lean_dec(v_inst_5067_);
return v_z_5068_;
}
else
{
lean_object* v___f_5074_; uint8_t v___x_5075_; 
v___f_5074_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5074_, 0, v_inst_5067_);
v___x_5075_ = lean_nat_dec_le(v___x_5071_, v___x_5071_);
if (v___x_5075_ == 0)
{
if (v___x_5073_ == 0)
{
lean_dec_ref(v___f_5074_);
lean_dec_ref(v_tasks_5069_);
return v_z_5068_;
}
else
{
size_t v___x_5076_; size_t v___x_5077_; lean_object* v___x_5078_; 
v___x_5076_ = ((size_t)0ULL);
v___x_5077_ = lean_usize_of_nat(v___x_5071_);
v___x_5078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5072_, v___f_5074_, v_tasks_5069_, v___x_5076_, v___x_5077_, v_z_5068_);
return v___x_5078_;
}
}
else
{
size_t v___x_5079_; size_t v___x_5080_; lean_object* v___x_5081_; 
v___x_5079_ = ((size_t)0ULL);
v___x_5080_ = lean_usize_of_nat(v___x_5071_);
v___x_5081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5072_, v___f_5074_, v_tasks_5069_, v___x_5079_, v___x_5080_, v_z_5068_);
return v___x_5081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5082_, lean_object* v_inst_5083_, lean_object* v_z_5084_, lean_object* v_tasks_5085_){
_start:
{
lean_object* v___x_5086_; 
v___x_5086_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5083_, v_z_5084_, v_tasks_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5087_, lean_object* v___x_5088_, lean_object* v_____r_5089_){
_start:
{
lean_object* v___x_5090_; 
v___x_5090_ = lean_apply_2(v_toPure_5087_, lean_box(0), v___x_5088_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5091_, lean_object* v_setNGen_5092_, lean_object* v_toBind_5093_, lean_object* v_ngen_5094_){
_start:
{
lean_object* v_namePrefix_5095_; lean_object* v_idx_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5110_; 
v_namePrefix_5095_ = lean_ctor_get(v_ngen_5094_, 0);
v_idx_5096_ = lean_ctor_get(v_ngen_5094_, 1);
v_isSharedCheck_5110_ = !lean_is_exclusive(v_ngen_5094_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5098_ = v_ngen_5094_;
v_isShared_5099_ = v_isSharedCheck_5110_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_idx_5096_);
lean_inc(v_namePrefix_5095_);
lean_dec(v_ngen_5094_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5110_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5103_; 
lean_inc(v_idx_5096_);
lean_inc(v_namePrefix_5095_);
v___x_5100_ = l_Lean_Name_num___override(v_namePrefix_5095_, v_idx_5096_);
v___x_5101_ = lean_unsigned_to_nat(1u);
if (v_isShared_5099_ == 0)
{
lean_ctor_set(v___x_5098_, 1, v___x_5101_);
lean_ctor_set(v___x_5098_, 0, v___x_5100_);
v___x_5103_ = v___x_5098_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v___x_5101_);
v___x_5103_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___f_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___f_5104_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5104_, 0, v_toPure_5091_);
lean_closure_set(v___f_5104_, 1, v___x_5103_);
v___x_5105_ = lean_nat_add(v_idx_5096_, v___x_5101_);
lean_dec(v_idx_5096_);
v___x_5106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5106_, 0, v_namePrefix_5095_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
v___x_5107_ = lean_apply_1(v_setNGen_5092_, v___x_5106_);
v___x_5108_ = lean_apply_4(v_toBind_5093_, lean_box(0), lean_box(0), v___x_5107_, v___f_5104_);
return v___x_5108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5111_, lean_object* v_inst_5112_){
_start:
{
lean_object* v_toApplicative_5113_; lean_object* v_toBind_5114_; lean_object* v_getNGen_5115_; lean_object* v_setNGen_5116_; lean_object* v_toPure_5117_; lean_object* v___f_5118_; lean_object* v___x_5119_; 
v_toApplicative_5113_ = lean_ctor_get(v_inst_5111_, 0);
lean_inc_ref(v_toApplicative_5113_);
v_toBind_5114_ = lean_ctor_get(v_inst_5111_, 1);
lean_inc_n(v_toBind_5114_, 2);
lean_dec_ref(v_inst_5111_);
v_getNGen_5115_ = lean_ctor_get(v_inst_5112_, 0);
lean_inc(v_getNGen_5115_);
v_setNGen_5116_ = lean_ctor_get(v_inst_5112_, 1);
lean_inc(v_setNGen_5116_);
lean_dec_ref(v_inst_5112_);
v_toPure_5117_ = lean_ctor_get(v_toApplicative_5113_, 1);
lean_inc(v_toPure_5117_);
lean_dec_ref(v_toApplicative_5113_);
v___f_5118_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5118_, 0, v_toPure_5117_);
lean_closure_set(v___f_5118_, 1, v_setNGen_5116_);
lean_closure_set(v___f_5118_, 2, v_toBind_5114_);
v___x_5119_ = lean_apply_4(v_toBind_5114_, lean_box(0), lean_box(0), v_getNGen_5115_, v___f_5118_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5120_, lean_object* v_inst_5121_, lean_object* v_inst_5122_){
_start:
{
lean_object* v___x_5123_; 
v___x_5123_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5121_, v_inst_5122_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_cctx_5124_, lean_object* v_env_5125_, lean_object* v_modName_5126_, lean_object* v_d_5127_, lean_object* v_val_5128_, lean_object* v_act_5129_, lean_object* v_as_5130_, size_t v_sz_5131_, size_t v_i_5132_, lean_object* v_b_5133_){
_start:
{
uint8_t v___x_5135_; 
v___x_5135_ = lean_usize_dec_lt(v_i_5132_, v_sz_5131_);
if (v___x_5135_ == 0)
{
lean_dec_ref(v_act_5129_);
lean_dec(v_modName_5126_);
lean_dec_ref(v_env_5125_);
lean_dec_ref(v_cctx_5124_);
return v_b_5133_;
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5137_; size_t v___x_5138_; size_t v___x_5139_; 
v_a_5136_ = lean_array_uget_borrowed(v_as_5130_, v_i_5132_);
lean_inc(v_a_5136_);
lean_inc_ref(v_act_5129_);
lean_inc(v_modName_5126_);
lean_inc_ref(v_env_5125_);
lean_inc_ref(v_cctx_5124_);
v___x_5137_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5124_, v_env_5125_, v_modName_5126_, v_d_5127_, v_val_5128_, v_b_5133_, v_act_5129_, v_a_5136_);
v___x_5138_ = ((size_t)1ULL);
v___x_5139_ = lean_usize_add(v_i_5132_, v___x_5138_);
v_i_5132_ = v___x_5139_;
v_b_5133_ = v___x_5137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_cctx_5141_, lean_object* v_env_5142_, lean_object* v_modName_5143_, lean_object* v_d_5144_, lean_object* v_val_5145_, lean_object* v_act_5146_, lean_object* v_as_5147_, lean_object* v_sz_5148_, lean_object* v_i_5149_, lean_object* v_b_5150_, lean_object* v___y_5151_){
_start:
{
size_t v_sz_boxed_5152_; size_t v_i_boxed_5153_; lean_object* v_res_5154_; 
v_sz_boxed_5152_ = lean_unbox_usize(v_sz_5148_);
lean_dec(v_sz_5148_);
v_i_boxed_5153_ = lean_unbox_usize(v_i_5149_);
lean_dec(v_i_5149_);
v_res_5154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5141_, v_env_5142_, v_modName_5143_, v_d_5144_, v_val_5145_, v_act_5146_, v_as_5147_, v_sz_boxed_5152_, v_i_boxed_5153_, v_b_5150_);
lean_dec_ref(v_as_5147_);
lean_dec(v_val_5145_);
lean_dec(v_d_5144_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5155_, lean_object* v_ngen_5156_, lean_object* v_env_5157_, lean_object* v_d_5158_, lean_object* v_act_5159_){
_start:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v_mainModule_5166_; lean_object* v___x_5167_; size_t v_sz_5168_; size_t v___x_5169_; lean_object* v___x_5170_; 
v___x_5161_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5156_);
v___x_5162_ = lean_st_mk_ref(v___x_5161_);
v___x_5163_ = 1;
v___x_5164_ = l_Lean_Environment_getLocalConstantInfos(v_env_5157_, v___x_5163_);
v___x_5165_ = l_Lean_Environment_header(v_env_5157_);
v_mainModule_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_mainModule_5166_);
lean_dec_ref(v___x_5165_);
v___x_5167_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
v_sz_5168_ = lean_array_size(v___x_5164_);
v___x_5169_ = ((size_t)0ULL);
v___x_5170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5155_, v_env_5157_, v_mainModule_5166_, v_d_5158_, v___x_5162_, v_act_5159_, v___x_5164_, v_sz_5168_, v___x_5169_, v___x_5167_);
lean_dec_ref(v___x_5164_);
lean_dec(v___x_5162_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5171_, lean_object* v_ngen_5172_, lean_object* v_env_5173_, lean_object* v_d_5174_, lean_object* v_act_5175_, lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5171_, v_ngen_5172_, v_env_5173_, v_d_5174_, v_act_5175_);
lean_dec(v_d_5174_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5178_, lean_object* v_cctx_5179_, lean_object* v_ngen_5180_, lean_object* v_env_5181_, lean_object* v_d_5182_, lean_object* v_act_5183_){
_start:
{
lean_object* v___x_5185_; 
v___x_5185_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5179_, v_ngen_5180_, v_env_5181_, v_d_5182_, v_act_5183_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5186_, lean_object* v_cctx_5187_, lean_object* v_ngen_5188_, lean_object* v_env_5189_, lean_object* v_d_5190_, lean_object* v_act_5191_, lean_object* v_a_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5186_, v_cctx_5187_, v_ngen_5188_, v_env_5189_, v_d_5190_, v_act_5191_);
lean_dec(v_d_5190_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03b1_5194_, lean_object* v_cctx_5195_, lean_object* v_env_5196_, lean_object* v_modName_5197_, lean_object* v_d_5198_, lean_object* v_val_5199_, lean_object* v_act_5200_, lean_object* v_as_5201_, size_t v_sz_5202_, size_t v_i_5203_, lean_object* v_b_5204_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_cctx_5195_, v_env_5196_, v_modName_5197_, v_d_5198_, v_val_5199_, v_act_5200_, v_as_5201_, v_sz_5202_, v_i_5203_, v_b_5204_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03b1_5207_, lean_object* v_cctx_5208_, lean_object* v_env_5209_, lean_object* v_modName_5210_, lean_object* v_d_5211_, lean_object* v_val_5212_, lean_object* v_act_5213_, lean_object* v_as_5214_, lean_object* v_sz_5215_, lean_object* v_i_5216_, lean_object* v_b_5217_, lean_object* v___y_5218_){
_start:
{
size_t v_sz_boxed_5219_; size_t v_i_boxed_5220_; lean_object* v_res_5221_; 
v_sz_boxed_5219_ = lean_unbox_usize(v_sz_5215_);
lean_dec(v_sz_5215_);
v_i_boxed_5220_ = lean_unbox_usize(v_i_5216_);
lean_dec(v_i_5216_);
v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03b1_5207_, v_cctx_5208_, v_env_5209_, v_modName_5210_, v_d_5211_, v_val_5212_, v_act_5213_, v_as_5214_, v_sz_boxed_5219_, v_i_boxed_5220_, v_b_5217_);
lean_dec_ref(v_as_5214_);
lean_dec(v_val_5212_);
lean_dec(v_d_5211_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5222_, lean_object* v_x_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
if (lean_obj_tag(v_x_5223_) == 0)
{
lean_object* v___x_5229_; 
v___x_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5229_, 0, v_x_5222_);
return v___x_5229_;
}
else
{
lean_object* v_head_5230_; lean_object* v_tail_5231_; lean_object* v___x_5232_; 
v_head_5230_ = lean_ctor_get(v_x_5223_, 0);
lean_inc(v_head_5230_);
v_tail_5231_ = lean_ctor_get(v_x_5223_, 1);
lean_inc(v_tail_5231_);
lean_dec_ref_known(v_x_5223_, 2);
v___x_5232_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5222_, v_head_5230_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref_known(v___x_5232_, 1);
v_x_5222_ = v_a_5233_;
v_x_5223_ = v_tail_5231_;
goto _start;
}
else
{
lean_dec(v_tail_5231_);
return v___x_5232_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5235_, lean_object* v_x_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5235_, v_x_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5243_, lean_object* v_keys_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5243_, v_keys_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5251_, lean_object* v_keys_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5251_, v_keys_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_);
lean_dec(v_a_5256_);
lean_dec_ref(v_a_5255_);
lean_dec(v_a_5254_);
lean_dec_ref(v_a_5253_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5259_, lean_object* v_t_5260_, lean_object* v_keys_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5260_, v_keys_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5268_, lean_object* v_t_5269_, lean_object* v_keys_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5268_, v_t_5269_, v_keys_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
lean_dec(v_a_5274_);
lean_dec_ref(v_a_5273_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5277_, lean_object* v_x_5278_, lean_object* v_x_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5278_, v_x_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5286_, lean_object* v_x_5287_, lean_object* v_x_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5286_, v_x_5287_, v_x_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5295_, size_t v_sz_5296_, size_t v_i_5297_, lean_object* v_b_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_){
_start:
{
uint8_t v___x_5305_; 
v___x_5305_ = lean_usize_dec_lt(v_i_5297_, v_sz_5296_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; 
v___x_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5306_, 0, v_b_5298_);
return v___x_5306_;
}
else
{
lean_object* v_a_5307_; lean_object* v___x_5308_; 
v_a_5307_ = lean_array_uget_borrowed(v_as_5295_, v_i_5297_);
v___x_5308_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5307_, v_b_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_);
if (lean_obj_tag(v___x_5308_) == 0)
{
lean_object* v_a_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5321_; 
v_a_5309_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5311_ = v___x_5308_;
v_isShared_5312_ = v_isSharedCheck_5321_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_a_5309_);
lean_dec(v___x_5308_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5321_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
if (lean_obj_tag(v_a_5309_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; 
v_a_5313_ = lean_ctor_get(v_a_5309_, 0);
lean_inc(v_a_5313_);
lean_dec_ref_known(v_a_5309_, 1);
if (v_isShared_5312_ == 0)
{
lean_ctor_set(v___x_5311_, 0, v_a_5313_);
v___x_5315_ = v___x_5311_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
else
{
lean_object* v_a_5317_; size_t v___x_5318_; size_t v___x_5319_; 
lean_del_object(v___x_5311_);
v_a_5317_ = lean_ctor_get(v_a_5309_, 0);
lean_inc(v_a_5317_);
lean_dec_ref_known(v_a_5309_, 1);
v___x_5318_ = ((size_t)1ULL);
v___x_5319_ = lean_usize_add(v_i_5297_, v___x_5318_);
v_i_5297_ = v___x_5319_;
v_b_5298_ = v_a_5317_;
goto _start;
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
v_a_5322_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___x_5308_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5308_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v___x_5337_; uint8_t v___x_5338_; 
v___x_5337_ = lean_unsigned_to_nat(0u);
v___x_5338_ = lean_nat_dec_eq(v_next_5330_, v___x_5337_);
if (v___x_5338_ == 0)
{
lean_object* v___x_5339_; 
v___x_5339_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v_a_5340_; lean_object* v_snd_5341_; lean_object* v_fst_5342_; lean_object* v_fst_5343_; lean_object* v_snd_5344_; lean_object* v___x_5345_; 
v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_a_5340_);
lean_dec_ref_known(v___x_5339_, 1);
v_snd_5341_ = lean_ctor_get(v_a_5340_, 1);
lean_inc(v_snd_5341_);
v_fst_5342_ = lean_ctor_get(v_a_5340_, 0);
lean_inc(v_fst_5342_);
lean_dec(v_a_5340_);
v_fst_5343_ = lean_ctor_get(v_snd_5341_, 0);
lean_inc(v_fst_5343_);
v_snd_5344_ = lean_ctor_get(v_snd_5341_, 1);
lean_inc(v_snd_5344_);
lean_dec(v_snd_5341_);
v___x_5345_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5343_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; lean_object* v_buckets_5347_; lean_object* v___x_5348_; size_t v_sz_5349_; size_t v___x_5350_; lean_object* v___x_5351_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
lean_inc(v_a_5346_);
lean_dec_ref_known(v___x_5345_, 1);
v_buckets_5347_ = lean_ctor_get(v_snd_5344_, 1);
v___x_5348_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5349_ = lean_array_size(v_buckets_5347_);
v___x_5350_ = ((size_t)0ULL);
v___x_5351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5347_, v_sz_5349_, v___x_5350_, v___x_5348_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5351_) == 0)
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5365_; 
v_a_5352_ = lean_ctor_get(v___x_5351_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5354_ = v___x_5351_;
v_isShared_5355_ = v_isSharedCheck_5365_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5351_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5365_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5363_; 
v___x_5356_ = lean_st_ref_take(v_a_5331_);
v___x_5357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5348_);
lean_ctor_set(v___x_5357_, 1, v_fst_5343_);
lean_ctor_set(v___x_5357_, 2, v_snd_5344_);
lean_ctor_set(v___x_5357_, 3, v___x_5348_);
v___x_5358_ = lean_array_set(v___x_5356_, v_next_5330_, v___x_5357_);
v___x_5359_ = lean_st_ref_put(v_a_5331_, v___x_5358_);
v___x_5360_ = l_Array_append___redArg(v_fst_5342_, v_a_5346_);
lean_dec(v_a_5346_);
v___x_5361_ = l_Array_append___redArg(v___x_5360_, v_a_5352_);
lean_dec(v_a_5352_);
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 0, v___x_5361_);
v___x_5363_ = v___x_5354_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5361_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
else
{
lean_dec(v_a_5346_);
lean_dec(v_snd_5344_);
lean_dec(v_fst_5343_);
lean_dec(v_fst_5342_);
return v___x_5351_;
}
}
else
{
lean_dec(v_snd_5344_);
lean_dec(v_fst_5343_);
lean_dec(v_fst_5342_);
return v___x_5345_;
}
}
else
{
lean_object* v_a_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5373_; 
v_a_5366_ = lean_ctor_get(v___x_5339_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5368_ = v___x_5339_;
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_a_5366_);
lean_dec(v___x_5339_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v___x_5371_; 
if (v_isShared_5369_ == 0)
{
v___x_5371_ = v___x_5368_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
else
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5374_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5374_);
return v___x_5375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
if (lean_obj_tag(v_a_5376_) == 0)
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5384_, 0, v_a_5377_);
v___x_5385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5384_);
return v___x_5385_;
}
else
{
lean_object* v_value_5386_; lean_object* v_tail_5387_; lean_object* v___x_5388_; 
v_value_5386_ = lean_ctor_get(v_a_5376_, 1);
v_tail_5387_ = lean_ctor_get(v_a_5376_, 2);
v___x_5388_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5386_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
if (lean_obj_tag(v___x_5388_) == 0)
{
lean_object* v_a_5389_; lean_object* v___x_5390_; 
v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
lean_inc(v_a_5389_);
lean_dec_ref_known(v___x_5388_, 1);
v___x_5390_ = l_Array_append___redArg(v_a_5377_, v_a_5389_);
lean_dec(v_a_5389_);
v_a_5376_ = v_tail_5387_;
v_a_5377_ = v___x_5390_;
goto _start;
}
else
{
lean_object* v_a_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5399_; 
lean_dec_ref(v_a_5377_);
v_a_5392_ = lean_ctor_get(v___x_5388_, 0);
v_isSharedCheck_5399_ = !lean_is_exclusive(v___x_5388_);
if (v_isSharedCheck_5399_ == 0)
{
v___x_5394_ = v___x_5388_;
v_isShared_5395_ = v_isSharedCheck_5399_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_a_5392_);
lean_dec(v___x_5388_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5399_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v___x_5397_; 
if (v_isShared_5395_ == 0)
{
v___x_5397_ = v___x_5394_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_a_5392_);
v___x_5397_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
return v___x_5397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5400_, v_a_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
lean_dec(v___y_5406_);
lean_dec_ref(v___y_5405_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v___y_5402_);
lean_dec(v_a_5400_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5409_, lean_object* v_sz_5410_, lean_object* v_i_5411_, lean_object* v_b_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
size_t v_sz_boxed_5419_; size_t v_i_boxed_5420_; lean_object* v_res_5421_; 
v_sz_boxed_5419_ = lean_unbox_usize(v_sz_5410_);
lean_dec(v_sz_5410_);
v_i_boxed_5420_ = lean_unbox_usize(v_i_5411_);
lean_dec(v_i_5411_);
v_res_5421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5409_, v_sz_boxed_5419_, v_i_boxed_5420_, v_b_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec(v___y_5413_);
lean_dec_ref(v_as_5409_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5422_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_, v_a_5427_);
lean_dec(v_a_5427_);
lean_dec_ref(v_a_5426_);
lean_dec(v_a_5425_);
lean_dec_ref(v_a_5424_);
lean_dec(v_a_5423_);
lean_dec(v_next_5422_);
return v_res_5429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5430_, lean_object* v_next_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v___x_5438_; 
v___x_5438_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_);
return v___x_5438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5439_, lean_object* v_next_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5439_, v_next_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
lean_dec(v_a_5445_);
lean_dec_ref(v_a_5444_);
lean_dec(v_a_5443_);
lean_dec_ref(v_a_5442_);
lean_dec(v_a_5441_);
lean_dec(v_next_5440_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_){
_start:
{
lean_object* v___x_5457_; 
v___x_5457_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5449_, v_a_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5458_, v_a_5459_, v_a_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec(v_a_5459_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5468_, lean_object* v_as_5469_, size_t v_sz_5470_, size_t v_i_5471_, lean_object* v_b_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5469_, v_sz_5470_, v_i_5471_, v_b_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5480_, lean_object* v_as_5481_, lean_object* v_sz_5482_, lean_object* v_i_5483_, lean_object* v_b_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_){
_start:
{
size_t v_sz_boxed_5491_; size_t v_i_boxed_5492_; lean_object* v_res_5493_; 
v_sz_boxed_5491_ = lean_unbox_usize(v_sz_5482_);
lean_dec(v_sz_5482_);
v_i_boxed_5492_ = lean_unbox_usize(v_i_5483_);
lean_dec(v_i_5483_);
v_res_5493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5480_, v_as_5481_, v_sz_boxed_5491_, v_i_boxed_5492_, v_b_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
lean_dec(v___y_5487_);
lean_dec_ref(v___y_5486_);
lean_dec(v___y_5485_);
lean_dec_ref(v_as_5481_);
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5494_, lean_object* v_rest_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_){
_start:
{
lean_object* v___x_5502_; uint8_t v___x_5503_; 
v___x_5502_ = lean_unsigned_to_nat(0u);
v___x_5503_ = lean_nat_dec_eq(v_next_5494_, v___x_5502_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; 
v___x_5504_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5494_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; lean_object* v_snd_5506_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
lean_inc(v_a_5505_);
lean_dec_ref_known(v___x_5504_, 1);
v_snd_5506_ = lean_ctor_get(v_a_5505_, 1);
lean_inc(v_snd_5506_);
lean_dec(v_a_5505_);
if (lean_obj_tag(v_rest_5495_) == 0)
{
lean_object* v___x_5507_; 
lean_dec(v_snd_5506_);
v___x_5507_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5494_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_);
lean_dec(v_next_5494_);
return v___x_5507_;
}
else
{
lean_object* v_fst_5508_; lean_object* v_snd_5509_; lean_object* v_head_5510_; lean_object* v_tail_5511_; lean_object* v___x_5512_; uint8_t v___x_5513_; 
lean_dec(v_next_5494_);
v_fst_5508_ = lean_ctor_get(v_snd_5506_, 0);
lean_inc(v_fst_5508_);
v_snd_5509_ = lean_ctor_get(v_snd_5506_, 1);
lean_inc(v_snd_5509_);
lean_dec(v_snd_5506_);
v_head_5510_ = lean_ctor_get(v_rest_5495_, 0);
v_tail_5511_ = lean_ctor_get(v_rest_5495_, 1);
v___x_5512_ = lean_box(3);
v___x_5513_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5510_, v___x_5512_);
if (v___x_5513_ == 0)
{
lean_object* v___x_5514_; 
lean_dec(v_fst_5508_);
v___x_5514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5509_, v_head_5510_, v___x_5502_);
lean_dec(v_snd_5509_);
v_next_5494_ = v___x_5514_;
v_rest_5495_ = v_tail_5511_;
goto _start;
}
else
{
lean_dec(v_snd_5509_);
v_next_5494_ = v_fst_5508_;
v_rest_5495_ = v_tail_5511_;
goto _start;
}
}
}
else
{
lean_object* v_a_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5524_; 
lean_dec(v_next_5494_);
v_a_5517_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5519_ = v___x_5504_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v___x_5504_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
if (v_isShared_5520_ == 0)
{
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_a_5517_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
}
else
{
lean_object* v___x_5525_; lean_object* v___x_5526_; 
lean_dec(v_next_5494_);
v___x_5525_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5525_);
return v___x_5526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5527_, lean_object* v_rest_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5527_, v_rest_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_);
lean_dec(v_a_5533_);
lean_dec_ref(v_a_5532_);
lean_dec(v_a_5531_);
lean_dec_ref(v_a_5530_);
lean_dec(v_a_5529_);
lean_dec(v_rest_5528_);
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5536_, lean_object* v_next_5537_, lean_object* v_rest_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_){
_start:
{
lean_object* v___x_5545_; 
v___x_5545_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5537_, v_rest_5538_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_);
return v___x_5545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5546_, lean_object* v_next_5547_, lean_object* v_rest_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_){
_start:
{
lean_object* v_res_5555_; 
v_res_5555_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5546_, v_next_5547_, v_rest_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_);
lean_dec(v_a_5553_);
lean_dec_ref(v_a_5552_);
lean_dec(v_a_5551_);
lean_dec_ref(v_a_5550_);
lean_dec(v_a_5549_);
lean_dec(v_rest_5548_);
return v_res_5555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5556_, lean_object* v_path_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_){
_start:
{
if (lean_obj_tag(v_path_5557_) == 0)
{
lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; 
v___x_5563_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5563_);
lean_ctor_set(v___x_5564_, 1, v_t_5556_);
v___x_5565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
return v___x_5565_;
}
else
{
lean_object* v_head_5566_; lean_object* v_tail_5567_; lean_object* v_roots_5568_; lean_object* v___x_5569_; lean_object* v_idx_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; 
v_head_5566_ = lean_ctor_get(v_path_5557_, 0);
lean_inc(v_head_5566_);
v_tail_5567_ = lean_ctor_get(v_path_5557_, 1);
lean_inc(v_tail_5567_);
lean_dec_ref_known(v_path_5557_, 2);
v_roots_5568_ = lean_ctor_get(v_t_5556_, 1);
v___x_5569_ = lean_unsigned_to_nat(0u);
v_idx_5570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5568_, v_head_5566_, v___x_5569_);
lean_dec(v_head_5566_);
v___x_5571_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5571_, 0, lean_box(0));
lean_closure_set(v___x_5571_, 1, v_idx_5570_);
lean_closure_set(v___x_5571_, 2, v_tail_5567_);
v___x_5572_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5556_, v___x_5571_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_);
return v___x_5572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5573_, lean_object* v_path_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_){
_start:
{
lean_object* v_res_5580_; 
v_res_5580_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5573_, v_path_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
lean_dec(v_a_5578_);
lean_dec_ref(v_a_5577_);
lean_dec(v_a_5576_);
lean_dec_ref(v_a_5575_);
return v_res_5580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5581_, lean_object* v_t_5582_, lean_object* v_path_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_){
_start:
{
lean_object* v___x_5589_; 
v___x_5589_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5582_, v_path_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5590_, lean_object* v_t_5591_, lean_object* v_path_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5590_, v_t_5591_, v_path_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_);
lean_dec(v_a_5596_);
lean_dec_ref(v_a_5595_);
lean_dec(v_a_5594_);
lean_dec_ref(v_a_5593_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5599_, lean_object* v_b_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
if (lean_obj_tag(v_as_x27_5599_) == 0)
{
lean_object* v___x_5606_; 
v___x_5606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5606_, 0, v_b_5600_);
return v___x_5606_;
}
else
{
lean_object* v_head_5607_; lean_object* v_tail_5608_; lean_object* v_fst_5609_; lean_object* v_snd_5610_; lean_object* v___x_5611_; 
v_head_5607_ = lean_ctor_get(v_as_x27_5599_, 0);
v_tail_5608_ = lean_ctor_get(v_as_x27_5599_, 1);
v_fst_5609_ = lean_ctor_get(v_b_5600_, 0);
lean_inc(v_fst_5609_);
v_snd_5610_ = lean_ctor_get(v_b_5600_, 1);
lean_inc(v_snd_5610_);
lean_dec_ref(v_b_5600_);
lean_inc(v_head_5607_);
v___x_5611_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5610_, v_head_5607_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v_a_5612_; lean_object* v_fst_5613_; lean_object* v_snd_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5623_; 
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
lean_inc(v_a_5612_);
lean_dec_ref_known(v___x_5611_, 1);
v_fst_5613_ = lean_ctor_get(v_a_5612_, 0);
v_snd_5614_ = lean_ctor_get(v_a_5612_, 1);
v_isSharedCheck_5623_ = !lean_is_exclusive(v_a_5612_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5616_ = v_a_5612_;
v_isShared_5617_ = v_isSharedCheck_5623_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_snd_5614_);
lean_inc(v_fst_5613_);
lean_dec(v_a_5612_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5623_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5618_; lean_object* v___x_5620_; 
v___x_5618_ = l_Array_append___redArg(v_fst_5609_, v_fst_5613_);
lean_dec(v_fst_5613_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 0, v___x_5618_);
v___x_5620_ = v___x_5616_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5618_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v_snd_5614_);
v___x_5620_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
v_as_x27_5599_ = v_tail_5608_;
v_b_5600_ = v___x_5620_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5609_);
return v___x_5611_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5624_, lean_object* v_b_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_){
_start:
{
lean_object* v_res_5631_; 
v_res_5631_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5624_, v_b_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec(v___y_5627_);
lean_dec_ref(v___y_5626_);
lean_dec(v_as_x27_5624_);
return v_res_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5632_, lean_object* v_keys_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_){
_start:
{
lean_object* v_allExtracted_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; 
v_allExtracted_5639_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5640_, 0, v_allExtracted_5639_);
lean_ctor_set(v___x_5640_, 1, v_t_5632_);
v___x_5641_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5633_, v___x_5640_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
if (lean_obj_tag(v___x_5641_) == 0)
{
lean_object* v_a_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5658_; 
v_a_5642_ = lean_ctor_get(v___x_5641_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5641_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5644_ = v___x_5641_;
v_isShared_5645_ = v_isSharedCheck_5658_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_a_5642_);
lean_dec(v___x_5641_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5658_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v_fst_5646_; lean_object* v_snd_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5657_; 
v_fst_5646_ = lean_ctor_get(v_a_5642_, 0);
v_snd_5647_ = lean_ctor_get(v_a_5642_, 1);
v_isSharedCheck_5657_ = !lean_is_exclusive(v_a_5642_);
if (v_isSharedCheck_5657_ == 0)
{
v___x_5649_ = v_a_5642_;
v_isShared_5650_ = v_isSharedCheck_5657_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_snd_5647_);
lean_inc(v_fst_5646_);
lean_dec(v_a_5642_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5657_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5652_; 
if (v_isShared_5650_ == 0)
{
v___x_5652_ = v___x_5649_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_fst_5646_);
lean_ctor_set(v_reuseFailAlloc_5656_, 1, v_snd_5647_);
v___x_5652_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
lean_object* v___x_5654_; 
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 0, v___x_5652_);
v___x_5654_ = v___x_5644_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v___x_5652_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
}
}
else
{
return v___x_5641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5659_, lean_object* v_keys_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5659_, v_keys_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
lean_dec(v_a_5664_);
lean_dec_ref(v_a_5663_);
lean_dec(v_a_5662_);
lean_dec_ref(v_a_5661_);
lean_dec(v_keys_5660_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5667_, lean_object* v_t_5668_, lean_object* v_keys_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_){
_start:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5668_, v_keys_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5676_, lean_object* v_t_5677_, lean_object* v_keys_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_){
_start:
{
lean_object* v_res_5684_; 
v_res_5684_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5676_, v_t_5677_, v_keys_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_);
lean_dec(v_a_5682_);
lean_dec_ref(v_a_5681_);
lean_dec(v_a_5680_);
lean_dec_ref(v_a_5679_);
lean_dec(v_keys_5678_);
return v_res_5684_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5685_, lean_object* v_as_5686_, lean_object* v_as_x27_5687_, lean_object* v_b_5688_, lean_object* v_a_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_){
_start:
{
lean_object* v___x_5695_; 
v___x_5695_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5687_, v_b_5688_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_);
return v___x_5695_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5696_, lean_object* v_as_5697_, lean_object* v_as_x27_5698_, lean_object* v_b_5699_, lean_object* v_a_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_){
_start:
{
lean_object* v_res_5706_; 
v_res_5706_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5696_, v_as_5697_, v_as_x27_5698_, v_b_5699_, v_a_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
lean_dec(v___y_5704_);
lean_dec_ref(v___y_5703_);
lean_dec(v___y_5702_);
lean_dec_ref(v___y_5701_);
lean_dec(v_as_x27_5698_);
lean_dec(v_as_5697_);
return v_res_5706_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5708_; lean_object* v___x_5709_; 
v___x_5708_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5709_ = l_Lean_stringToMessageData(v___x_5708_);
return v___x_5709_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5711_; lean_object* v___x_5712_; 
v___x_5711_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5712_ = l_Lean_stringToMessageData(v___x_5711_);
return v___x_5712_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5714_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5715_ = l_Lean_stringToMessageData(v___x_5714_);
return v___x_5715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5716_, lean_object* v_inst_5717_, lean_object* v_inst_5718_, lean_object* v_inst_5719_, lean_object* v_f_5720_){
_start:
{
lean_object* v_module_5721_; lean_object* v_const_5722_; lean_object* v_exception_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; 
v_module_5721_ = lean_ctor_get(v_f_5720_, 0);
lean_inc(v_module_5721_);
v_const_5722_ = lean_ctor_get(v_f_5720_, 1);
lean_inc(v_const_5722_);
v_exception_5723_ = lean_ctor_get(v_f_5720_, 2);
lean_inc_ref(v_exception_5723_);
lean_dec_ref(v_f_5720_);
v___x_5724_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5725_ = l_Lean_MessageData_ofName(v_const_5722_);
v___x_5726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5724_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
v___x_5727_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5726_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = l_Lean_MessageData_ofName(v_module_5721_);
v___x_5730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5728_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5730_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
v___x_5733_ = l_Lean_Exception_toMessageData(v_exception_5723_);
v___x_5734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5732_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = l_Lean_logError___redArg(v_inst_5716_, v_inst_5717_, v_inst_5718_, v_inst_5719_, v___x_5734_);
return v___x_5735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5736_, lean_object* v_inst_5737_, lean_object* v_inst_5738_, lean_object* v_inst_5739_, lean_object* v_inst_5740_, lean_object* v_f_5741_){
_start:
{
lean_object* v___x_5742_; 
v___x_5742_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5737_, v_inst_5738_, v_inst_5739_, v_inst_5740_, v_f_5741_);
return v___x_5742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_tasks_5743_, lean_object* v_toPure_5744_, lean_object* v_t_5745_){
_start:
{
lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5746_ = lean_array_push(v_tasks_5743_, v_t_5745_);
v___x_5747_ = lean_apply_2(v_toPure_5744_, lean_box(0), v___x_5746_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5748_, lean_object* v_inst_5749_, lean_object* v_cctx_5750_, lean_object* v_env_5751_, lean_object* v_act_5752_, lean_object* v_constantsPerTask_5753_, lean_object* v_n_5754_, lean_object* v_ngen_5755_, lean_object* v_tasks_5756_, lean_object* v_start_5757_, lean_object* v_cnt_5758_, lean_object* v_idx_5759_){
_start:
{
lean_object* v___x_5760_; lean_object* v_toApplicative_5761_; lean_object* v_moduleData_5762_; lean_object* v_toBind_5763_; lean_object* v_toPure_5764_; lean_object* v___x_5765_; uint8_t v___x_5766_; 
v___x_5760_ = l_Lean_Environment_header(v_env_5751_);
v_toApplicative_5761_ = lean_ctor_get(v_inst_5748_, 0);
v_moduleData_5762_ = lean_ctor_get(v___x_5760_, 6);
lean_inc_ref(v_moduleData_5762_);
lean_dec_ref(v___x_5760_);
v_toBind_5763_ = lean_ctor_get(v_inst_5748_, 1);
v_toPure_5764_ = lean_ctor_get(v_toApplicative_5761_, 1);
v___x_5765_ = lean_array_get_size(v_moduleData_5762_);
v___x_5766_ = lean_nat_dec_lt(v_idx_5759_, v___x_5765_);
if (v___x_5766_ == 0)
{
uint8_t v___x_5767_; 
lean_inc(v_toPure_5764_);
lean_inc(v_toBind_5763_);
lean_dec_ref(v_moduleData_5762_);
lean_dec(v_idx_5759_);
lean_dec(v_cnt_5758_);
lean_dec(v_constantsPerTask_5753_);
lean_dec_ref(v_inst_5748_);
v___x_5767_ = lean_nat_dec_lt(v_start_5757_, v_n_5754_);
if (v___x_5767_ == 0)
{
lean_object* v___x_5768_; 
lean_dec(v_toBind_5763_);
lean_dec(v_start_5757_);
lean_dec_ref(v_ngen_5755_);
lean_dec(v_n_5754_);
lean_dec_ref(v_act_5752_);
lean_dec_ref(v_env_5751_);
lean_dec_ref(v_cctx_5750_);
lean_dec(v_inst_5749_);
v___x_5768_ = lean_apply_2(v_toPure_5764_, lean_box(0), v_tasks_5756_);
return v___x_5768_;
}
else
{
lean_object* v_namePrefix_5769_; lean_object* v_idx_5770_; lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5785_; 
v_namePrefix_5769_ = lean_ctor_get(v_ngen_5755_, 0);
v_idx_5770_ = lean_ctor_get(v_ngen_5755_, 1);
v_isSharedCheck_5785_ = !lean_is_exclusive(v_ngen_5755_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5772_ = v_ngen_5755_;
v_isShared_5773_ = v_isSharedCheck_5785_;
goto v_resetjp_5771_;
}
else
{
lean_inc(v_idx_5770_);
lean_inc(v_namePrefix_5769_);
lean_dec(v_ngen_5755_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5785_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___f_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5778_; 
v___f_5774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5774_, 0, v_tasks_5756_);
lean_closure_set(v___f_5774_, 1, v_toPure_5764_);
v___x_5775_ = l_Lean_Name_num___override(v_namePrefix_5769_, v_idx_5770_);
v___x_5776_ = lean_unsigned_to_nat(1u);
if (v_isShared_5773_ == 0)
{
lean_ctor_set(v___x_5772_, 1, v___x_5776_);
lean_ctor_set(v___x_5772_, 0, v___x_5775_);
v___x_5778_ = v___x_5772_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5775_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v___x_5776_);
v___x_5778_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; 
v___x_5779_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5779_, 0, lean_box(0));
lean_closure_set(v___x_5779_, 1, v_cctx_5750_);
lean_closure_set(v___x_5779_, 2, v___x_5778_);
lean_closure_set(v___x_5779_, 3, v_env_5751_);
lean_closure_set(v___x_5779_, 4, v_act_5752_);
lean_closure_set(v___x_5779_, 5, v_start_5757_);
lean_closure_set(v___x_5779_, 6, v_n_5754_);
v___x_5780_ = lean_unsigned_to_nat(0u);
v___x_5781_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5781_, 0, lean_box(0));
lean_closure_set(v___x_5781_, 1, v___x_5779_);
lean_closure_set(v___x_5781_, 2, v___x_5780_);
v___x_5782_ = lean_apply_2(v_inst_5749_, lean_box(0), v___x_5781_);
v___x_5783_ = lean_apply_4(v_toBind_5763_, lean_box(0), lean_box(0), v___x_5782_, v___f_5774_);
return v___x_5783_;
}
}
}
}
else
{
lean_object* v_mdata_5786_; lean_object* v_constants_5787_; lean_object* v___x_5788_; lean_object* v_cnt_5789_; uint8_t v___x_5790_; 
v_mdata_5786_ = lean_array_fget(v_moduleData_5762_, v_idx_5759_);
lean_dec_ref(v_moduleData_5762_);
v_constants_5787_ = lean_ctor_get(v_mdata_5786_, 2);
lean_inc_ref(v_constants_5787_);
lean_dec(v_mdata_5786_);
v___x_5788_ = lean_array_get_size(v_constants_5787_);
lean_dec_ref(v_constants_5787_);
v_cnt_5789_ = lean_nat_add(v_cnt_5758_, v___x_5788_);
lean_dec(v_cnt_5758_);
v___x_5790_ = lean_nat_dec_lt(v_constantsPerTask_5753_, v_cnt_5789_);
if (v___x_5790_ == 0)
{
lean_object* v___x_5791_; lean_object* v___x_5792_; 
v___x_5791_ = lean_unsigned_to_nat(1u);
v___x_5792_ = lean_nat_add(v_idx_5759_, v___x_5791_);
lean_dec(v_idx_5759_);
v_cnt_5758_ = v_cnt_5789_;
v_idx_5759_ = v___x_5792_;
goto _start;
}
else
{
lean_object* v_namePrefix_5794_; lean_object* v_idx_5795_; lean_object* v___x_5797_; uint8_t v_isShared_5798_; uint8_t v_isSharedCheck_5813_; 
lean_inc(v_toBind_5763_);
lean_dec(v_cnt_5789_);
v_namePrefix_5794_ = lean_ctor_get(v_ngen_5755_, 0);
v_idx_5795_ = lean_ctor_get(v_ngen_5755_, 1);
v_isSharedCheck_5813_ = !lean_is_exclusive(v_ngen_5755_);
if (v_isSharedCheck_5813_ == 0)
{
v___x_5797_ = v_ngen_5755_;
v_isShared_5798_ = v_isSharedCheck_5813_;
goto v_resetjp_5796_;
}
else
{
lean_inc(v_idx_5795_);
lean_inc(v_namePrefix_5794_);
lean_dec(v_ngen_5755_);
v___x_5797_ = lean_box(0);
v_isShared_5798_ = v_isSharedCheck_5813_;
goto v_resetjp_5796_;
}
v_resetjp_5796_:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5802_; 
lean_inc(v_idx_5795_);
lean_inc(v_namePrefix_5794_);
v___x_5799_ = l_Lean_Name_num___override(v_namePrefix_5794_, v_idx_5795_);
v___x_5800_ = lean_unsigned_to_nat(1u);
if (v_isShared_5798_ == 0)
{
lean_ctor_set(v___x_5797_, 1, v___x_5800_);
lean_ctor_set(v___x_5797_, 0, v___x_5799_);
v___x_5802_ = v___x_5797_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5799_);
lean_ctor_set(v_reuseFailAlloc_5812_, 1, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___f_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5803_ = lean_nat_add(v_idx_5795_, v___x_5800_);
lean_dec(v_idx_5795_);
v___x_5804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5804_, 0, v_namePrefix_5794_);
lean_ctor_set(v___x_5804_, 1, v___x_5803_);
v___x_5805_ = lean_nat_add(v_idx_5759_, v___x_5800_);
lean_dec(v_idx_5759_);
lean_inc(v___x_5805_);
lean_inc_ref(v_act_5752_);
lean_inc_ref(v_env_5751_);
lean_inc_ref(v_cctx_5750_);
lean_inc(v_inst_5749_);
v___f_5806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5806_, 0, v_tasks_5756_);
lean_closure_set(v___f_5806_, 1, v_inst_5748_);
lean_closure_set(v___f_5806_, 2, v_inst_5749_);
lean_closure_set(v___f_5806_, 3, v_cctx_5750_);
lean_closure_set(v___f_5806_, 4, v_env_5751_);
lean_closure_set(v___f_5806_, 5, v_act_5752_);
lean_closure_set(v___f_5806_, 6, v_constantsPerTask_5753_);
lean_closure_set(v___f_5806_, 7, v_n_5754_);
lean_closure_set(v___f_5806_, 8, v___x_5804_);
lean_closure_set(v___f_5806_, 9, v___x_5805_);
v___x_5807_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5807_, 0, lean_box(0));
lean_closure_set(v___x_5807_, 1, v_cctx_5750_);
lean_closure_set(v___x_5807_, 2, v___x_5802_);
lean_closure_set(v___x_5807_, 3, v_env_5751_);
lean_closure_set(v___x_5807_, 4, v_act_5752_);
lean_closure_set(v___x_5807_, 5, v_start_5757_);
lean_closure_set(v___x_5807_, 6, v___x_5805_);
v___x_5808_ = lean_unsigned_to_nat(0u);
v___x_5809_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5809_, 0, lean_box(0));
lean_closure_set(v___x_5809_, 1, v___x_5807_);
lean_closure_set(v___x_5809_, 2, v___x_5808_);
v___x_5810_ = lean_apply_2(v_inst_5749_, lean_box(0), v___x_5809_);
v___x_5811_ = lean_apply_4(v_toBind_5763_, lean_box(0), lean_box(0), v___x_5810_, v___f_5806_);
return v___x_5811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5814_, lean_object* v_inst_5815_, lean_object* v_inst_5816_, lean_object* v_cctx_5817_, lean_object* v_env_5818_, lean_object* v_act_5819_, lean_object* v_constantsPerTask_5820_, lean_object* v_n_5821_, lean_object* v___x_5822_, lean_object* v___x_5823_, lean_object* v_t_5824_){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5825_ = lean_array_push(v_tasks_5814_, v_t_5824_);
v___x_5826_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5823_);
v___x_5827_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5815_, v_inst_5816_, v_cctx_5817_, v_env_5818_, v_act_5819_, v_constantsPerTask_5820_, v_n_5821_, v___x_5822_, v___x_5825_, v___x_5823_, v___x_5826_, v___x_5823_);
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5828_, lean_object* v_00_u03b1_5829_, lean_object* v_inst_5830_, lean_object* v_inst_5831_, lean_object* v_cctx_5832_, lean_object* v_env_5833_, lean_object* v_act_5834_, lean_object* v_constantsPerTask_5835_, lean_object* v_n_5836_, lean_object* v_ngen_5837_, lean_object* v_tasks_5838_, lean_object* v_start_5839_, lean_object* v_cnt_5840_, lean_object* v_idx_5841_){
_start:
{
lean_object* v___x_5842_; 
v___x_5842_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5830_, v_inst_5831_, v_cctx_5832_, v_env_5833_, v_act_5834_, v_constantsPerTask_5835_, v_n_5836_, v_ngen_5837_, v_tasks_5838_, v_start_5839_, v_cnt_5840_, v_idx_5841_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5843_, lean_object* v_h__1_5844_){
_start:
{
lean_object* v_fst_5845_; lean_object* v_snd_5846_; lean_object* v___x_5847_; 
v_fst_5845_ = lean_ctor_get(v_x_5843_, 0);
lean_inc(v_fst_5845_);
v_snd_5846_ = lean_ctor_get(v_x_5843_, 1);
lean_inc(v_snd_5846_);
lean_dec_ref(v_x_5843_);
v___x_5847_ = lean_apply_2(v_h__1_5844_, v_fst_5845_, v_snd_5846_);
return v___x_5847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5848_, lean_object* v_x_5849_, lean_object* v_h__1_5850_){
_start:
{
lean_object* v_fst_5851_; lean_object* v_snd_5852_; lean_object* v___x_5853_; 
v_fst_5851_ = lean_ctor_get(v_x_5849_, 0);
lean_inc(v_fst_5851_);
v_snd_5852_ = lean_ctor_get(v_x_5849_, 1);
lean_inc(v_snd_5852_);
lean_dec_ref(v_x_5849_);
v___x_5853_ = lean_apply_2(v_h__1_5850_, v_fst_5851_, v_snd_5852_);
return v___x_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5854_, lean_object* v_inst_5855_, lean_object* v_inst_5856_, lean_object* v_inst_5857_, lean_object* v_x_5858_, lean_object* v___y_5859_){
_start:
{
lean_object* v___x_5860_; 
v___x_5860_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5854_, v_inst_5855_, v_inst_5856_, v_inst_5857_, v___y_5859_);
return v___x_5860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5861_, lean_object* v_toPure_5862_, lean_object* v_____r_5863_){
_start:
{
lean_object* v_tree_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; 
v_tree_5864_ = lean_ctor_get(v_r_5861_, 0);
lean_inc_ref(v_tree_5864_);
lean_dec_ref(v_r_5861_);
v___x_5865_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5864_);
v___x_5866_ = lean_apply_2(v_toPure_5862_, lean_box(0), v___x_5865_);
return v___x_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5867_, lean_object* v___x_5868_, lean_object* v_toPure_5869_, lean_object* v_toBind_5870_, lean_object* v_inst_5871_, lean_object* v___f_5872_, lean_object* v_tasks_5873_){
_start:
{
lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v_r_5879_; lean_object* v_errors_5880_; lean_object* v___f_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; uint8_t v___x_5884_; 
v___x_5874_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5867_);
v___x_5875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5867_);
lean_ctor_set(v___x_5875_, 1, v___x_5874_);
v___x_5876_ = lean_mk_empty_array_with_capacity(v___x_5867_);
lean_inc_ref(v___x_5876_);
v___x_5877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5877_, 0, v___x_5875_);
lean_ctor_set(v___x_5877_, 1, v___x_5876_);
v___x_5878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5877_);
lean_ctor_set(v___x_5878_, 1, v___x_5876_);
v_r_5879_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5868_, v___x_5878_, v_tasks_5873_);
v_errors_5880_ = lean_ctor_get(v_r_5879_, 1);
lean_inc_ref(v_errors_5880_);
lean_inc(v_toPure_5869_);
v___f_5881_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5881_, 0, v_r_5879_);
lean_closure_set(v___f_5881_, 1, v_toPure_5869_);
v___x_5882_ = lean_array_get_size(v_errors_5880_);
v___x_5883_ = lean_box(0);
v___x_5884_ = lean_nat_dec_lt(v___x_5867_, v___x_5882_);
lean_dec(v___x_5867_);
if (v___x_5884_ == 0)
{
lean_object* v___x_5885_; lean_object* v___x_5886_; 
lean_dec_ref(v_errors_5880_);
lean_dec(v___f_5872_);
lean_dec_ref(v_inst_5871_);
v___x_5885_ = lean_apply_2(v_toPure_5869_, lean_box(0), v___x_5883_);
v___x_5886_ = lean_apply_4(v_toBind_5870_, lean_box(0), lean_box(0), v___x_5885_, v___f_5881_);
return v___x_5886_;
}
else
{
uint8_t v___x_5887_; 
v___x_5887_ = lean_nat_dec_le(v___x_5882_, v___x_5882_);
if (v___x_5887_ == 0)
{
if (v___x_5884_ == 0)
{
lean_object* v___x_5888_; lean_object* v___x_5889_; 
lean_dec_ref(v_errors_5880_);
lean_dec(v___f_5872_);
lean_dec_ref(v_inst_5871_);
v___x_5888_ = lean_apply_2(v_toPure_5869_, lean_box(0), v___x_5883_);
v___x_5889_ = lean_apply_4(v_toBind_5870_, lean_box(0), lean_box(0), v___x_5888_, v___f_5881_);
return v___x_5889_;
}
else
{
size_t v___x_5890_; size_t v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; 
lean_dec(v_toPure_5869_);
v___x_5890_ = ((size_t)0ULL);
v___x_5891_ = lean_usize_of_nat(v___x_5882_);
v___x_5892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5871_, v___f_5872_, v_errors_5880_, v___x_5890_, v___x_5891_, v___x_5883_);
v___x_5893_ = lean_apply_4(v_toBind_5870_, lean_box(0), lean_box(0), v___x_5892_, v___f_5881_);
return v___x_5893_;
}
}
else
{
size_t v___x_5894_; size_t v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
lean_dec(v_toPure_5869_);
v___x_5894_ = ((size_t)0ULL);
v___x_5895_ = lean_usize_of_nat(v___x_5882_);
v___x_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5871_, v___f_5872_, v_errors_5880_, v___x_5894_, v___x_5895_, v___x_5883_);
v___x_5897_ = lean_apply_4(v_toBind_5870_, lean_box(0), lean_box(0), v___x_5896_, v___f_5881_);
return v___x_5897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_5900_, lean_object* v_inst_5901_, lean_object* v_inst_5902_, lean_object* v_inst_5903_, lean_object* v_inst_5904_, lean_object* v_cctx_5905_, lean_object* v_ngen_5906_, lean_object* v_env_5907_, lean_object* v_act_5908_, lean_object* v_constantsPerTask_5909_){
_start:
{
lean_object* v___x_5910_; lean_object* v_moduleData_5911_; lean_object* v_toApplicative_5912_; lean_object* v_toBind_5913_; lean_object* v_n_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v_toPure_5918_; lean_object* v___f_5919_; lean_object* v___x_5920_; lean_object* v___f_5921_; lean_object* v___x_5922_; 
v___x_5910_ = l_Lean_Environment_header(v_env_5907_);
v_moduleData_5911_ = lean_ctor_get(v___x_5910_, 6);
lean_inc_ref(v_moduleData_5911_);
lean_dec_ref(v___x_5910_);
v_toApplicative_5912_ = lean_ctor_get(v_inst_5900_, 0);
v_toBind_5913_ = lean_ctor_get(v_inst_5900_, 1);
lean_inc_n(v_toBind_5913_, 2);
v_n_5914_ = lean_array_get_size(v_moduleData_5911_);
lean_dec_ref(v_moduleData_5911_);
v___x_5915_ = lean_unsigned_to_nat(0u);
v___x_5916_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_5900_, 2);
v___x_5917_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5900_, v_inst_5904_, v_cctx_5905_, v_env_5907_, v_act_5908_, v_constantsPerTask_5909_, v_n_5914_, v_ngen_5906_, v___x_5916_, v___x_5915_, v___x_5915_, v___x_5915_);
v_toPure_5918_ = lean_ctor_get(v_toApplicative_5912_, 1);
lean_inc(v_toPure_5918_);
v___f_5919_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_5919_, 0, v_inst_5900_);
lean_closure_set(v___f_5919_, 1, v_inst_5901_);
lean_closure_set(v___f_5919_, 2, v_inst_5902_);
lean_closure_set(v___f_5919_, 3, v_inst_5903_);
v___x_5920_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_5921_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_5921_, 0, v___x_5915_);
lean_closure_set(v___f_5921_, 1, v___x_5920_);
lean_closure_set(v___f_5921_, 2, v_toPure_5918_);
lean_closure_set(v___f_5921_, 3, v_toBind_5913_);
lean_closure_set(v___f_5921_, 4, v_inst_5900_);
lean_closure_set(v___f_5921_, 5, v___f_5919_);
v___x_5922_ = lean_apply_4(v_toBind_5913_, lean_box(0), lean_box(0), v___x_5917_, v___f_5921_);
return v___x_5922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_5923_, lean_object* v_00_u03b1_5924_, lean_object* v_inst_5925_, lean_object* v_inst_5926_, lean_object* v_inst_5927_, lean_object* v_inst_5928_, lean_object* v_inst_5929_, lean_object* v_cctx_5930_, lean_object* v_ngen_5931_, lean_object* v_env_5932_, lean_object* v_act_5933_, lean_object* v_constantsPerTask_5934_){
_start:
{
lean_object* v___x_5935_; 
v___x_5935_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_5925_, v_inst_5926_, v_inst_5927_, v_inst_5928_, v_inst_5929_, v_cctx_5930_, v_ngen_5931_, v_env_5932_, v_act_5933_, v_constantsPerTask_5934_);
return v___x_5935_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; 
v___x_5936_ = lean_box(0);
v___x_5937_ = lean_unsigned_to_nat(16u);
v___x_5938_ = lean_mk_array(v___x_5937_, v___x_5936_);
return v___x_5938_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5939_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_5940_ = lean_unsigned_to_nat(0u);
v___x_5941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5939_);
return v___x_5941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_5942_){
_start:
{
lean_object* v_toCold_5943_; lean_object* v_options_5944_; lean_object* v_maxRecDepth_5945_; lean_object* v_ref_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5973_; 
v_toCold_5943_ = lean_ctor_get(v_ctx_5942_, 0);
v_options_5944_ = lean_ctor_get(v_ctx_5942_, 1);
v_maxRecDepth_5945_ = lean_ctor_get(v_ctx_5942_, 3);
v_ref_5946_ = lean_ctor_get(v_ctx_5942_, 4);
v_isSharedCheck_5973_ = !lean_is_exclusive(v_ctx_5942_);
if (v_isSharedCheck_5973_ == 0)
{
lean_object* v_unused_5974_; lean_object* v_unused_5975_; lean_object* v_unused_5976_; lean_object* v_unused_5977_; lean_object* v_unused_5978_; lean_object* v_unused_5979_; 
v_unused_5974_ = lean_ctor_get(v_ctx_5942_, 9);
lean_dec(v_unused_5974_);
v_unused_5975_ = lean_ctor_get(v_ctx_5942_, 8);
lean_dec(v_unused_5975_);
v_unused_5976_ = lean_ctor_get(v_ctx_5942_, 7);
lean_dec(v_unused_5976_);
v_unused_5977_ = lean_ctor_get(v_ctx_5942_, 6);
lean_dec(v_unused_5977_);
v_unused_5978_ = lean_ctor_get(v_ctx_5942_, 5);
lean_dec(v_unused_5978_);
v_unused_5979_ = lean_ctor_get(v_ctx_5942_, 2);
lean_dec(v_unused_5979_);
v___x_5948_ = v_ctx_5942_;
v_isShared_5949_ = v_isSharedCheck_5973_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_ref_5946_);
lean_inc(v_maxRecDepth_5945_);
lean_inc(v_options_5944_);
lean_inc(v_toCold_5943_);
lean_dec(v_ctx_5942_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5973_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v_fileName_5950_; lean_object* v_fileMap_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5969_; 
v_fileName_5950_ = lean_ctor_get(v_toCold_5943_, 0);
v_fileMap_5951_ = lean_ctor_get(v_toCold_5943_, 1);
v_isSharedCheck_5969_ = !lean_is_exclusive(v_toCold_5943_);
if (v_isSharedCheck_5969_ == 0)
{
lean_object* v_unused_5970_; lean_object* v_unused_5971_; lean_object* v_unused_5972_; 
v_unused_5970_ = lean_ctor_get(v_toCold_5943_, 4);
lean_dec(v_unused_5970_);
v_unused_5971_ = lean_ctor_get(v_toCold_5943_, 3);
lean_dec(v_unused_5971_);
v_unused_5972_ = lean_ctor_get(v_toCold_5943_, 2);
lean_dec(v_unused_5972_);
v___x_5953_ = v_toCold_5943_;
v_isShared_5954_ = v_isSharedCheck_5969_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_fileMap_5951_);
lean_inc(v_fileName_5950_);
lean_dec(v_toCold_5943_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5969_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5960_; 
v___x_5955_ = lean_box(0);
v___x_5956_ = lean_box(0);
v___x_5957_ = lean_unsigned_to_nat(0u);
v___x_5958_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 4, v___x_5958_);
lean_ctor_set(v___x_5953_, 3, v___x_5956_);
lean_ctor_set(v___x_5953_, 2, v___x_5955_);
v___x_5960_ = v___x_5953_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5968_; 
v_reuseFailAlloc_5968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_fileName_5950_);
lean_ctor_set(v_reuseFailAlloc_5968_, 1, v_fileMap_5951_);
lean_ctor_set(v_reuseFailAlloc_5968_, 2, v___x_5955_);
lean_ctor_set(v_reuseFailAlloc_5968_, 3, v___x_5956_);
lean_ctor_set(v_reuseFailAlloc_5968_, 4, v___x_5958_);
v___x_5960_ = v_reuseFailAlloc_5968_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
lean_object* v___x_5961_; lean_object* v___x_5962_; uint8_t v___x_5963_; uint8_t v___x_5964_; lean_object* v___x_5966_; 
v___x_5961_ = lean_box(0);
v___x_5962_ = l_Lean_firstFrontendMacroScope;
v___x_5963_ = l_Lean_getDiag(v_options_5944_);
v___x_5964_ = 0;
if (v_isShared_5949_ == 0)
{
lean_ctor_set(v___x_5948_, 9, v___x_5962_);
lean_ctor_set(v___x_5948_, 8, v___x_5957_);
lean_ctor_set(v___x_5948_, 7, v___x_5957_);
lean_ctor_set(v___x_5948_, 6, v___x_5961_);
lean_ctor_set(v___x_5948_, 5, v___x_5955_);
lean_ctor_set(v___x_5948_, 2, v___x_5957_);
lean_ctor_set(v___x_5948_, 0, v___x_5960_);
v___x_5966_ = v___x_5948_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5967_; 
v_reuseFailAlloc_5967_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_5967_, 0, v___x_5960_);
lean_ctor_set(v_reuseFailAlloc_5967_, 1, v_options_5944_);
lean_ctor_set(v_reuseFailAlloc_5967_, 2, v___x_5957_);
lean_ctor_set(v_reuseFailAlloc_5967_, 3, v_maxRecDepth_5945_);
lean_ctor_set(v_reuseFailAlloc_5967_, 4, v_ref_5946_);
lean_ctor_set(v_reuseFailAlloc_5967_, 5, v___x_5955_);
lean_ctor_set(v_reuseFailAlloc_5967_, 6, v___x_5961_);
lean_ctor_set(v_reuseFailAlloc_5967_, 7, v___x_5957_);
lean_ctor_set(v_reuseFailAlloc_5967_, 8, v___x_5957_);
lean_ctor_set(v_reuseFailAlloc_5967_, 9, v___x_5962_);
v___x_5966_ = v_reuseFailAlloc_5967_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
lean_ctor_set_uint8(v___x_5966_, sizeof(void*)*10, v___x_5963_);
lean_ctor_set_uint8(v___x_5966_, sizeof(void*)*10 + 1, v___x_5964_);
return v___x_5966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_5980_, lean_object* v_opts_5981_, lean_object* v_act_5982_, lean_object* v_decl_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_){
_start:
{
lean_object* v___x_5989_; lean_object* v___x_5990_; 
lean_inc(v___y_5987_);
lean_inc_ref(v___y_5986_);
lean_inc(v___y_5985_);
lean_inc_ref(v___y_5984_);
v___x_5989_ = lean_apply_4(v_act_5982_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
v___x_5990_ = l_Lean_profileitIOUnsafe___redArg(v_category_5980_, v_opts_5981_, v___x_5989_, v_decl_5983_);
return v___x_5990_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_5991_, lean_object* v_opts_5992_, lean_object* v_act_5993_, lean_object* v_decl_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_){
_start:
{
lean_object* v_res_6000_; 
v_res_6000_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_5991_, v_opts_5992_, v_act_5993_, v_decl_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_);
lean_dec(v___y_5998_);
lean_dec_ref(v___y_5997_);
lean_dec(v___y_5996_);
lean_dec_ref(v___y_5995_);
lean_dec_ref(v_opts_5992_);
lean_dec_ref(v_category_5991_);
return v_res_6000_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6001_, lean_object* v_category_6002_, lean_object* v_opts_6003_, lean_object* v_act_6004_, lean_object* v_decl_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_){
_start:
{
lean_object* v___x_6011_; 
v___x_6011_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6002_, v_opts_6003_, v_act_6004_, v_decl_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
return v___x_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6012_, lean_object* v_category_6013_, lean_object* v_opts_6014_, lean_object* v_act_6015_, lean_object* v_decl_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v_res_6022_; 
v_res_6022_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6012_, v_category_6013_, v_opts_6014_, v_act_6015_, v_decl_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_);
lean_dec(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec(v___y_6018_);
lean_dec_ref(v___y_6017_);
lean_dec_ref(v_opts_6014_);
lean_dec_ref(v_category_6013_);
return v_res_6022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6023_, lean_object* v_env_6024_, lean_object* v_act_6025_, lean_object* v_constantsPerTask_6026_, lean_object* v_n_6027_, lean_object* v_ngen_6028_, lean_object* v_tasks_6029_, lean_object* v_start_6030_, lean_object* v_cnt_6031_, lean_object* v_idx_6032_){
_start:
{
lean_object* v___x_6034_; lean_object* v_moduleData_6035_; lean_object* v___x_6036_; uint8_t v___x_6037_; 
v___x_6034_ = l_Lean_Environment_header(v_env_6024_);
v_moduleData_6035_ = lean_ctor_get(v___x_6034_, 6);
lean_inc_ref(v_moduleData_6035_);
lean_dec_ref(v___x_6034_);
v___x_6036_ = lean_array_get_size(v_moduleData_6035_);
v___x_6037_ = lean_nat_dec_lt(v_idx_6032_, v___x_6036_);
if (v___x_6037_ == 0)
{
uint8_t v___x_6038_; 
lean_dec_ref(v_moduleData_6035_);
lean_dec(v_idx_6032_);
lean_dec(v_cnt_6031_);
v___x_6038_ = lean_nat_dec_lt(v_start_6030_, v_n_6027_);
if (v___x_6038_ == 0)
{
lean_object* v___x_6039_; 
lean_dec(v_start_6030_);
lean_dec_ref(v_ngen_6028_);
lean_dec(v_n_6027_);
lean_dec_ref(v_act_6025_);
lean_dec_ref(v_env_6024_);
lean_dec_ref(v_cctx_6023_);
v___x_6039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6039_, 0, v_tasks_6029_);
return v___x_6039_;
}
else
{
lean_object* v_namePrefix_6040_; lean_object* v_idx_6041_; lean_object* v___x_6043_; uint8_t v_isShared_6044_; uint8_t v_isSharedCheck_6055_; 
v_namePrefix_6040_ = lean_ctor_get(v_ngen_6028_, 0);
v_idx_6041_ = lean_ctor_get(v_ngen_6028_, 1);
v_isSharedCheck_6055_ = !lean_is_exclusive(v_ngen_6028_);
if (v_isSharedCheck_6055_ == 0)
{
v___x_6043_ = v_ngen_6028_;
v_isShared_6044_ = v_isSharedCheck_6055_;
goto v_resetjp_6042_;
}
else
{
lean_inc(v_idx_6041_);
lean_inc(v_namePrefix_6040_);
lean_dec(v_ngen_6028_);
v___x_6043_ = lean_box(0);
v_isShared_6044_ = v_isSharedCheck_6055_;
goto v_resetjp_6042_;
}
v_resetjp_6042_:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6048_; 
v___x_6045_ = l_Lean_Name_num___override(v_namePrefix_6040_, v_idx_6041_);
v___x_6046_ = lean_unsigned_to_nat(1u);
if (v_isShared_6044_ == 0)
{
lean_ctor_set(v___x_6043_, 1, v___x_6046_);
lean_ctor_set(v___x_6043_, 0, v___x_6045_);
v___x_6048_ = v___x_6043_;
goto v_reusejp_6047_;
}
else
{
lean_object* v_reuseFailAlloc_6054_; 
v_reuseFailAlloc_6054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6054_, 0, v___x_6045_);
lean_ctor_set(v_reuseFailAlloc_6054_, 1, v___x_6046_);
v___x_6048_ = v_reuseFailAlloc_6054_;
goto v_reusejp_6047_;
}
v_reusejp_6047_:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6049_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6049_, 0, lean_box(0));
lean_closure_set(v___x_6049_, 1, v_cctx_6023_);
lean_closure_set(v___x_6049_, 2, v___x_6048_);
lean_closure_set(v___x_6049_, 3, v_env_6024_);
lean_closure_set(v___x_6049_, 4, v_act_6025_);
lean_closure_set(v___x_6049_, 5, v_start_6030_);
lean_closure_set(v___x_6049_, 6, v_n_6027_);
v___x_6050_ = lean_unsigned_to_nat(0u);
v___x_6051_ = lean_io_as_task(v___x_6049_, v___x_6050_);
v___x_6052_ = lean_array_push(v_tasks_6029_, v___x_6051_);
v___x_6053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
return v___x_6053_;
}
}
}
}
else
{
lean_object* v_mdata_6056_; lean_object* v_constants_6057_; lean_object* v___x_6058_; lean_object* v_cnt_6059_; uint8_t v___x_6060_; 
v_mdata_6056_ = lean_array_fget(v_moduleData_6035_, v_idx_6032_);
lean_dec_ref(v_moduleData_6035_);
v_constants_6057_ = lean_ctor_get(v_mdata_6056_, 2);
lean_inc_ref(v_constants_6057_);
lean_dec(v_mdata_6056_);
v___x_6058_ = lean_array_get_size(v_constants_6057_);
lean_dec_ref(v_constants_6057_);
v_cnt_6059_ = lean_nat_add(v_cnt_6031_, v___x_6058_);
lean_dec(v_cnt_6031_);
v___x_6060_ = lean_nat_dec_lt(v_constantsPerTask_6026_, v_cnt_6059_);
if (v___x_6060_ == 0)
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6061_ = lean_unsigned_to_nat(1u);
v___x_6062_ = lean_nat_add(v_idx_6032_, v___x_6061_);
lean_dec(v_idx_6032_);
v_cnt_6031_ = v_cnt_6059_;
v_idx_6032_ = v___x_6062_;
goto _start;
}
else
{
lean_object* v_namePrefix_6064_; lean_object* v_idx_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6082_; 
lean_dec(v_cnt_6059_);
v_namePrefix_6064_ = lean_ctor_get(v_ngen_6028_, 0);
v_idx_6065_ = lean_ctor_get(v_ngen_6028_, 1);
v_isSharedCheck_6082_ = !lean_is_exclusive(v_ngen_6028_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6067_ = v_ngen_6028_;
v_isShared_6068_ = v_isSharedCheck_6082_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_idx_6065_);
lean_inc(v_namePrefix_6064_);
lean_dec(v_ngen_6028_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6082_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6072_; 
lean_inc(v_idx_6065_);
lean_inc(v_namePrefix_6064_);
v___x_6069_ = l_Lean_Name_num___override(v_namePrefix_6064_, v_idx_6065_);
v___x_6070_ = lean_unsigned_to_nat(1u);
if (v_isShared_6068_ == 0)
{
lean_ctor_set(v___x_6067_, 1, v___x_6070_);
lean_ctor_set(v___x_6067_, 0, v___x_6069_);
v___x_6072_ = v___x_6067_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v___x_6069_);
lean_ctor_set(v_reuseFailAlloc_6081_, 1, v___x_6070_);
v___x_6072_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
v___x_6073_ = lean_nat_add(v_idx_6032_, v___x_6070_);
lean_dec(v_idx_6032_);
lean_inc_n(v___x_6073_, 2);
lean_inc_ref(v_act_6025_);
lean_inc_ref(v_env_6024_);
lean_inc_ref(v_cctx_6023_);
v___x_6074_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6074_, 0, lean_box(0));
lean_closure_set(v___x_6074_, 1, v_cctx_6023_);
lean_closure_set(v___x_6074_, 2, v___x_6072_);
lean_closure_set(v___x_6074_, 3, v_env_6024_);
lean_closure_set(v___x_6074_, 4, v_act_6025_);
lean_closure_set(v___x_6074_, 5, v_start_6030_);
lean_closure_set(v___x_6074_, 6, v___x_6073_);
v___x_6075_ = lean_unsigned_to_nat(0u);
v___x_6076_ = lean_io_as_task(v___x_6074_, v___x_6075_);
v___x_6077_ = lean_nat_add(v_idx_6065_, v___x_6070_);
lean_dec(v_idx_6065_);
v___x_6078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6078_, 0, v_namePrefix_6064_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_array_push(v_tasks_6029_, v___x_6076_);
v_ngen_6028_ = v___x_6078_;
v_tasks_6029_ = v___x_6079_;
v_start_6030_ = v___x_6073_;
v_cnt_6031_ = v___x_6075_;
v_idx_6032_ = v___x_6073_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6083_, lean_object* v_env_6084_, lean_object* v_act_6085_, lean_object* v_constantsPerTask_6086_, lean_object* v_n_6087_, lean_object* v_ngen_6088_, lean_object* v_tasks_6089_, lean_object* v_start_6090_, lean_object* v_cnt_6091_, lean_object* v_idx_6092_, lean_object* v___y_6093_){
_start:
{
lean_object* v_res_6094_; 
v_res_6094_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6083_, v_env_6084_, v_act_6085_, v_constantsPerTask_6086_, v_n_6087_, v_ngen_6088_, v_tasks_6089_, v_start_6090_, v_cnt_6091_, v_idx_6092_);
lean_dec(v_constantsPerTask_6086_);
return v_res_6094_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v_suppressElabErrors_6103_, uint8_t v___y_6104_, lean_object* v_x_6105_){
_start:
{
if (lean_obj_tag(v_x_6105_) == 1)
{
lean_object* v_pre_6106_; 
v_pre_6106_ = lean_ctor_get(v_x_6105_, 0);
switch(lean_obj_tag(v_pre_6106_))
{
case 1:
{
lean_object* v_pre_6107_; 
v_pre_6107_ = lean_ctor_get(v_pre_6106_, 0);
switch(lean_obj_tag(v_pre_6107_))
{
case 0:
{
lean_object* v_str_6108_; lean_object* v_str_6109_; lean_object* v___x_6110_; uint8_t v___x_6111_; 
v_str_6108_ = lean_ctor_get(v_x_6105_, 1);
v_str_6109_ = lean_ctor_get(v_pre_6106_, 1);
v___x_6110_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6111_ = lean_string_dec_eq(v_str_6109_, v___x_6110_);
if (v___x_6111_ == 0)
{
lean_object* v___x_6112_; uint8_t v___x_6113_; 
v___x_6112_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6113_ = lean_string_dec_eq(v_str_6109_, v___x_6112_);
if (v___x_6113_ == 0)
{
return v___x_6113_;
}
else
{
lean_object* v___x_6114_; uint8_t v___x_6115_; 
v___x_6114_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6115_ = lean_string_dec_eq(v_str_6108_, v___x_6114_);
if (v___x_6115_ == 0)
{
return v___x_6115_;
}
else
{
return v_suppressElabErrors_6103_;
}
}
}
else
{
lean_object* v___x_6116_; uint8_t v___x_6117_; 
v___x_6116_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6117_ = lean_string_dec_eq(v_str_6108_, v___x_6116_);
if (v___x_6117_ == 0)
{
return v___x_6117_;
}
else
{
return v_suppressElabErrors_6103_;
}
}
}
case 1:
{
lean_object* v_pre_6118_; 
v_pre_6118_ = lean_ctor_get(v_pre_6107_, 0);
if (lean_obj_tag(v_pre_6118_) == 0)
{
lean_object* v_str_6119_; lean_object* v_str_6120_; lean_object* v_str_6121_; lean_object* v___x_6122_; uint8_t v___x_6123_; 
v_str_6119_ = lean_ctor_get(v_x_6105_, 1);
v_str_6120_ = lean_ctor_get(v_pre_6106_, 1);
v_str_6121_ = lean_ctor_get(v_pre_6107_, 1);
v___x_6122_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6123_ = lean_string_dec_eq(v_str_6121_, v___x_6122_);
if (v___x_6123_ == 0)
{
return v___x_6123_;
}
else
{
lean_object* v___x_6124_; uint8_t v___x_6125_; 
v___x_6124_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6125_ = lean_string_dec_eq(v_str_6120_, v___x_6124_);
if (v___x_6125_ == 0)
{
return v___x_6125_;
}
else
{
lean_object* v___x_6126_; uint8_t v___x_6127_; 
v___x_6126_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6127_ = lean_string_dec_eq(v_str_6119_, v___x_6126_);
if (v___x_6127_ == 0)
{
return v___x_6127_;
}
else
{
return v_suppressElabErrors_6103_;
}
}
}
}
else
{
return v___y_6104_;
}
}
default: 
{
return v___y_6104_;
}
}
}
case 0:
{
lean_object* v_str_6128_; lean_object* v___x_6129_; uint8_t v___x_6130_; 
v_str_6128_ = lean_ctor_get(v_x_6105_, 1);
v___x_6129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6130_ = lean_string_dec_eq(v_str_6128_, v___x_6129_);
if (v___x_6130_ == 0)
{
return v___x_6130_;
}
else
{
return v_suppressElabErrors_6103_;
}
}
default: 
{
return v___y_6104_;
}
}
}
else
{
return v___y_6104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_6131_, lean_object* v___y_6132_, lean_object* v_x_6133_){
_start:
{
uint8_t v_suppressElabErrors_boxed_6134_; uint8_t v___y_8045__boxed_6135_; uint8_t v_res_6136_; lean_object* v_r_6137_; 
v_suppressElabErrors_boxed_6134_ = lean_unbox(v_suppressElabErrors_6131_);
v___y_8045__boxed_6135_ = lean_unbox(v___y_6132_);
v_res_6136_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v_suppressElabErrors_boxed_6134_, v___y_8045__boxed_6135_, v_x_6133_);
lean_dec(v_x_6133_);
v_r_6137_ = lean_box(v_res_6136_);
return v_r_6137_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6139_, lean_object* v_msgData_6140_, uint8_t v_severity_6141_, uint8_t v_isSilent_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_){
_start:
{
lean_object* v___y_6149_; lean_object* v___y_6150_; lean_object* v___y_6151_; lean_object* v___y_6152_; lean_object* v___y_6153_; uint8_t v___y_6154_; uint8_t v___y_6155_; lean_object* v___y_6156_; lean_object* v___y_6157_; lean_object* v___y_6185_; lean_object* v___y_6186_; uint8_t v___y_6187_; uint8_t v___y_6188_; uint8_t v___y_6189_; lean_object* v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6211_; lean_object* v___y_6212_; uint8_t v___y_6213_; uint8_t v___y_6214_; uint8_t v___y_6215_; lean_object* v___y_6216_; lean_object* v___y_6217_; lean_object* v___y_6221_; uint8_t v___y_6222_; lean_object* v___y_6223_; uint8_t v___y_6224_; lean_object* v___y_6225_; uint8_t v___y_6226_; uint8_t v___x_6231_; uint8_t v___y_6233_; lean_object* v___y_6234_; lean_object* v___y_6235_; lean_object* v___y_6236_; uint8_t v___y_6237_; uint8_t v___y_6238_; uint8_t v___y_6240_; uint8_t v___x_6254_; 
v___x_6231_ = 2;
v___x_6254_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6141_, v___x_6231_);
if (v___x_6254_ == 0)
{
v___y_6240_ = v___x_6254_;
goto v___jp_6239_;
}
else
{
uint8_t v___x_6255_; 
lean_inc_ref(v_msgData_6140_);
v___x_6255_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6140_);
v___y_6240_ = v___x_6255_;
goto v___jp_6239_;
}
v___jp_6148_:
{
lean_object* v___x_6158_; lean_object* v_currNamespace_6159_; lean_object* v_openDecls_6160_; lean_object* v_env_6161_; lean_object* v_nextMacroScope_6162_; lean_object* v_ngen_6163_; lean_object* v_auxDeclNGen_6164_; lean_object* v_traceState_6165_; lean_object* v_cache_6166_; lean_object* v_messages_6167_; lean_object* v_infoState_6168_; lean_object* v_snapshotTasks_6169_; lean_object* v___x_6171_; uint8_t v_isShared_6172_; uint8_t v_isSharedCheck_6183_; 
v___x_6158_ = lean_st_ref_take(v___y_6157_);
v_currNamespace_6159_ = lean_ctor_get(v___y_6156_, 5);
v_openDecls_6160_ = lean_ctor_get(v___y_6156_, 6);
v_env_6161_ = lean_ctor_get(v___x_6158_, 0);
v_nextMacroScope_6162_ = lean_ctor_get(v___x_6158_, 1);
v_ngen_6163_ = lean_ctor_get(v___x_6158_, 2);
v_auxDeclNGen_6164_ = lean_ctor_get(v___x_6158_, 3);
v_traceState_6165_ = lean_ctor_get(v___x_6158_, 4);
v_cache_6166_ = lean_ctor_get(v___x_6158_, 5);
v_messages_6167_ = lean_ctor_get(v___x_6158_, 6);
v_infoState_6168_ = lean_ctor_get(v___x_6158_, 7);
v_snapshotTasks_6169_ = lean_ctor_get(v___x_6158_, 8);
v_isSharedCheck_6183_ = !lean_is_exclusive(v___x_6158_);
if (v_isSharedCheck_6183_ == 0)
{
v___x_6171_ = v___x_6158_;
v_isShared_6172_ = v_isSharedCheck_6183_;
goto v_resetjp_6170_;
}
else
{
lean_inc(v_snapshotTasks_6169_);
lean_inc(v_infoState_6168_);
lean_inc(v_messages_6167_);
lean_inc(v_cache_6166_);
lean_inc(v_traceState_6165_);
lean_inc(v_auxDeclNGen_6164_);
lean_inc(v_ngen_6163_);
lean_inc(v_nextMacroScope_6162_);
lean_inc(v_env_6161_);
lean_dec(v___x_6158_);
v___x_6171_ = lean_box(0);
v_isShared_6172_ = v_isSharedCheck_6183_;
goto v_resetjp_6170_;
}
v_resetjp_6170_:
{
lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6178_; 
lean_inc(v_openDecls_6160_);
lean_inc(v_currNamespace_6159_);
v___x_6173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6173_, 0, v_currNamespace_6159_);
lean_ctor_set(v___x_6173_, 1, v_openDecls_6160_);
v___x_6174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6174_, 0, v___x_6173_);
lean_ctor_set(v___x_6174_, 1, v___y_6153_);
lean_inc_ref(v___y_6151_);
lean_inc_ref(v___y_6150_);
v___x_6175_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6175_, 0, v___y_6150_);
lean_ctor_set(v___x_6175_, 1, v___y_6149_);
lean_ctor_set(v___x_6175_, 2, v___y_6152_);
lean_ctor_set(v___x_6175_, 3, v___y_6151_);
lean_ctor_set(v___x_6175_, 4, v___x_6174_);
lean_ctor_set_uint8(v___x_6175_, sizeof(void*)*5, v___y_6154_);
lean_ctor_set_uint8(v___x_6175_, sizeof(void*)*5 + 1, v___y_6155_);
lean_ctor_set_uint8(v___x_6175_, sizeof(void*)*5 + 2, v_isSilent_6142_);
v___x_6176_ = l_Lean_MessageLog_add(v___x_6175_, v_messages_6167_);
if (v_isShared_6172_ == 0)
{
lean_ctor_set(v___x_6171_, 6, v___x_6176_);
v___x_6178_ = v___x_6171_;
goto v_reusejp_6177_;
}
else
{
lean_object* v_reuseFailAlloc_6182_; 
v_reuseFailAlloc_6182_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_env_6161_);
lean_ctor_set(v_reuseFailAlloc_6182_, 1, v_nextMacroScope_6162_);
lean_ctor_set(v_reuseFailAlloc_6182_, 2, v_ngen_6163_);
lean_ctor_set(v_reuseFailAlloc_6182_, 3, v_auxDeclNGen_6164_);
lean_ctor_set(v_reuseFailAlloc_6182_, 4, v_traceState_6165_);
lean_ctor_set(v_reuseFailAlloc_6182_, 5, v_cache_6166_);
lean_ctor_set(v_reuseFailAlloc_6182_, 6, v___x_6176_);
lean_ctor_set(v_reuseFailAlloc_6182_, 7, v_infoState_6168_);
lean_ctor_set(v_reuseFailAlloc_6182_, 8, v_snapshotTasks_6169_);
v___x_6178_ = v_reuseFailAlloc_6182_;
goto v_reusejp_6177_;
}
v_reusejp_6177_:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; 
v___x_6179_ = lean_st_ref_put(v___y_6157_, v___x_6178_);
v___x_6180_ = lean_box(0);
v___x_6181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
return v___x_6181_;
}
}
}
v___jp_6184_:
{
lean_object* v_fileName_6192_; lean_object* v_fileMap_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v_a_6196_; lean_object* v___x_6198_; uint8_t v_isShared_6199_; uint8_t v_isSharedCheck_6209_; 
v_fileName_6192_ = lean_ctor_get(v___y_6190_, 0);
v_fileMap_6193_ = lean_ctor_get(v___y_6190_, 1);
v___x_6194_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6140_);
v___x_6195_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6194_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_);
v_a_6196_ = lean_ctor_get(v___x_6195_, 0);
v_isSharedCheck_6209_ = !lean_is_exclusive(v___x_6195_);
if (v_isSharedCheck_6209_ == 0)
{
v___x_6198_ = v___x_6195_;
v_isShared_6199_ = v_isSharedCheck_6209_;
goto v_resetjp_6197_;
}
else
{
lean_inc(v_a_6196_);
lean_dec(v___x_6195_);
v___x_6198_ = lean_box(0);
v_isShared_6199_ = v_isSharedCheck_6209_;
goto v_resetjp_6197_;
}
v_resetjp_6197_:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; 
lean_inc_ref_n(v_fileMap_6193_, 2);
v___x_6200_ = l_Lean_FileMap_toPosition(v_fileMap_6193_, v___y_6186_);
lean_dec(v___y_6186_);
v___x_6201_ = l_Lean_FileMap_toPosition(v_fileMap_6193_, v___y_6191_);
lean_dec(v___y_6191_);
v___x_6202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6201_);
v___x_6203_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6187_ == 0)
{
lean_del_object(v___x_6198_);
lean_dec_ref(v___y_6185_);
v___y_6149_ = v___x_6200_;
v___y_6150_ = v_fileName_6192_;
v___y_6151_ = v___x_6203_;
v___y_6152_ = v___x_6202_;
v___y_6153_ = v_a_6196_;
v___y_6154_ = v___y_6188_;
v___y_6155_ = v___y_6189_;
v___y_6156_ = v___y_6145_;
v___y_6157_ = v___y_6146_;
goto v___jp_6148_;
}
else
{
uint8_t v___x_6204_; 
lean_inc(v_a_6196_);
v___x_6204_ = l_Lean_MessageData_hasTag(v___y_6185_, v_a_6196_);
if (v___x_6204_ == 0)
{
lean_object* v___x_6205_; lean_object* v___x_6207_; 
lean_dec_ref_known(v___x_6202_, 1);
lean_dec_ref(v___x_6200_);
lean_dec(v_a_6196_);
v___x_6205_ = lean_box(0);
if (v_isShared_6199_ == 0)
{
lean_ctor_set(v___x_6198_, 0, v___x_6205_);
v___x_6207_ = v___x_6198_;
goto v_reusejp_6206_;
}
else
{
lean_object* v_reuseFailAlloc_6208_; 
v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6208_, 0, v___x_6205_);
v___x_6207_ = v_reuseFailAlloc_6208_;
goto v_reusejp_6206_;
}
v_reusejp_6206_:
{
return v___x_6207_;
}
}
else
{
lean_del_object(v___x_6198_);
v___y_6149_ = v___x_6200_;
v___y_6150_ = v_fileName_6192_;
v___y_6151_ = v___x_6203_;
v___y_6152_ = v___x_6202_;
v___y_6153_ = v_a_6196_;
v___y_6154_ = v___y_6188_;
v___y_6155_ = v___y_6189_;
v___y_6156_ = v___y_6145_;
v___y_6157_ = v___y_6146_;
goto v___jp_6148_;
}
}
}
}
v___jp_6210_:
{
lean_object* v___x_6218_; 
v___x_6218_ = l_Lean_Syntax_getTailPos_x3f(v___y_6212_, v___y_6214_);
lean_dec(v___y_6212_);
if (lean_obj_tag(v___x_6218_) == 0)
{
lean_inc(v___y_6217_);
v___y_6185_ = v___y_6211_;
v___y_6186_ = v___y_6217_;
v___y_6187_ = v___y_6213_;
v___y_6188_ = v___y_6214_;
v___y_6189_ = v___y_6215_;
v___y_6190_ = v___y_6216_;
v___y_6191_ = v___y_6217_;
goto v___jp_6184_;
}
else
{
lean_object* v_val_6219_; 
v_val_6219_ = lean_ctor_get(v___x_6218_, 0);
lean_inc(v_val_6219_);
lean_dec_ref_known(v___x_6218_, 1);
v___y_6185_ = v___y_6211_;
v___y_6186_ = v___y_6217_;
v___y_6187_ = v___y_6213_;
v___y_6188_ = v___y_6214_;
v___y_6189_ = v___y_6215_;
v___y_6190_ = v___y_6216_;
v___y_6191_ = v_val_6219_;
goto v___jp_6184_;
}
}
v___jp_6220_:
{
lean_object* v_ref_6227_; lean_object* v___x_6228_; 
v_ref_6227_ = l_Lean_replaceRef(v_ref_6139_, v___y_6223_);
v___x_6228_ = l_Lean_Syntax_getPos_x3f(v_ref_6227_, v___y_6224_);
if (lean_obj_tag(v___x_6228_) == 0)
{
lean_object* v___x_6229_; 
v___x_6229_ = lean_unsigned_to_nat(0u);
v___y_6211_ = v___y_6221_;
v___y_6212_ = v_ref_6227_;
v___y_6213_ = v___y_6222_;
v___y_6214_ = v___y_6224_;
v___y_6215_ = v___y_6226_;
v___y_6216_ = v___y_6225_;
v___y_6217_ = v___x_6229_;
goto v___jp_6210_;
}
else
{
lean_object* v_val_6230_; 
v_val_6230_ = lean_ctor_get(v___x_6228_, 0);
lean_inc(v_val_6230_);
lean_dec_ref_known(v___x_6228_, 1);
v___y_6211_ = v___y_6221_;
v___y_6212_ = v_ref_6227_;
v___y_6213_ = v___y_6222_;
v___y_6214_ = v___y_6224_;
v___y_6215_ = v___y_6226_;
v___y_6216_ = v___y_6225_;
v___y_6217_ = v_val_6230_;
goto v___jp_6210_;
}
}
v___jp_6232_:
{
if (v___y_6238_ == 0)
{
v___y_6221_ = v___y_6235_;
v___y_6222_ = v___y_6233_;
v___y_6223_ = v___y_6234_;
v___y_6224_ = v___y_6237_;
v___y_6225_ = v___y_6236_;
v___y_6226_ = v_severity_6141_;
goto v___jp_6220_;
}
else
{
v___y_6221_ = v___y_6235_;
v___y_6222_ = v___y_6233_;
v___y_6223_ = v___y_6234_;
v___y_6224_ = v___y_6237_;
v___y_6225_ = v___y_6236_;
v___y_6226_ = v___x_6231_;
goto v___jp_6220_;
}
}
v___jp_6239_:
{
if (v___y_6240_ == 0)
{
lean_object* v_toCold_6241_; lean_object* v_options_6242_; lean_object* v_ref_6243_; uint8_t v_suppressElabErrors_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___f_6247_; uint8_t v___x_6248_; uint8_t v___x_6249_; 
v_toCold_6241_ = lean_ctor_get(v___y_6145_, 0);
v_options_6242_ = lean_ctor_get(v___y_6145_, 1);
v_ref_6243_ = lean_ctor_get(v___y_6145_, 4);
v_suppressElabErrors_6244_ = lean_ctor_get_uint8(v___y_6145_, sizeof(void*)*10 + 1);
v___x_6245_ = lean_box(v_suppressElabErrors_6244_);
v___x_6246_ = lean_box(v___y_6240_);
v___f_6247_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6247_, 0, v___x_6245_);
lean_closure_set(v___f_6247_, 1, v___x_6246_);
v___x_6248_ = 1;
v___x_6249_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6141_, v___x_6248_);
if (v___x_6249_ == 0)
{
v___y_6233_ = v_suppressElabErrors_6244_;
v___y_6234_ = v_ref_6243_;
v___y_6235_ = v___f_6247_;
v___y_6236_ = v_toCold_6241_;
v___y_6237_ = v___y_6240_;
v___y_6238_ = v___x_6249_;
goto v___jp_6232_;
}
else
{
lean_object* v___x_6250_; uint8_t v___x_6251_; 
v___x_6250_ = l_Lean_warningAsError;
v___x_6251_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6242_, v___x_6250_);
v___y_6233_ = v_suppressElabErrors_6244_;
v___y_6234_ = v_ref_6243_;
v___y_6235_ = v___f_6247_;
v___y_6236_ = v_toCold_6241_;
v___y_6237_ = v___y_6240_;
v___y_6238_ = v___x_6251_;
goto v___jp_6232_;
}
}
else
{
lean_object* v___x_6252_; lean_object* v___x_6253_; 
lean_dec_ref(v_msgData_6140_);
v___x_6252_ = lean_box(0);
v___x_6253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6253_, 0, v___x_6252_);
return v___x_6253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6256_, lean_object* v_msgData_6257_, lean_object* v_severity_6258_, lean_object* v_isSilent_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_){
_start:
{
uint8_t v_severity_boxed_6265_; uint8_t v_isSilent_boxed_6266_; lean_object* v_res_6267_; 
v_severity_boxed_6265_ = lean_unbox(v_severity_6258_);
v_isSilent_boxed_6266_ = lean_unbox(v_isSilent_6259_);
v_res_6267_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6256_, v_msgData_6257_, v_severity_boxed_6265_, v_isSilent_boxed_6266_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
lean_dec(v___y_6263_);
lean_dec_ref(v___y_6262_);
lean_dec(v___y_6261_);
lean_dec_ref(v___y_6260_);
lean_dec(v_ref_6256_);
return v_res_6267_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6268_, uint8_t v_severity_6269_, uint8_t v_isSilent_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_){
_start:
{
lean_object* v_ref_6276_; lean_object* v___x_6277_; 
v_ref_6276_ = lean_ctor_get(v___y_6273_, 4);
v___x_6277_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6276_, v_msgData_6268_, v_severity_6269_, v_isSilent_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
return v___x_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6278_, lean_object* v_severity_6279_, lean_object* v_isSilent_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
uint8_t v_severity_boxed_6286_; uint8_t v_isSilent_boxed_6287_; lean_object* v_res_6288_; 
v_severity_boxed_6286_ = lean_unbox(v_severity_6279_);
v_isSilent_boxed_6287_ = lean_unbox(v_isSilent_6280_);
v_res_6288_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6278_, v_severity_boxed_6286_, v_isSilent_boxed_6287_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_);
lean_dec(v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec(v___y_6282_);
lean_dec_ref(v___y_6281_);
return v_res_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_){
_start:
{
uint8_t v___x_6295_; uint8_t v___x_6296_; lean_object* v___x_6297_; 
v___x_6295_ = 2;
v___x_6296_ = 0;
v___x_6297_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6289_, v___x_6295_, v___x_6296_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
return v___x_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_){
_start:
{
lean_object* v_res_6304_; 
v_res_6304_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_);
lean_dec(v___y_6302_);
lean_dec_ref(v___y_6301_);
lean_dec(v___y_6300_);
lean_dec_ref(v___y_6299_);
return v_res_6304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_){
_start:
{
lean_object* v_module_6311_; lean_object* v_const_6312_; lean_object* v_exception_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; 
v_module_6311_ = lean_ctor_get(v_f_6305_, 0);
lean_inc(v_module_6311_);
v_const_6312_ = lean_ctor_get(v_f_6305_, 1);
lean_inc(v_const_6312_);
v_exception_6313_ = lean_ctor_get(v_f_6305_, 2);
lean_inc_ref(v_exception_6313_);
lean_dec_ref(v_f_6305_);
v___x_6314_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6315_ = l_Lean_MessageData_ofName(v_const_6312_);
v___x_6316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6316_, 0, v___x_6314_);
lean_ctor_set(v___x_6316_, 1, v___x_6315_);
v___x_6317_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6318_, 0, v___x_6316_);
lean_ctor_set(v___x_6318_, 1, v___x_6317_);
v___x_6319_ = l_Lean_MessageData_ofName(v_module_6311_);
v___x_6320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6320_, 0, v___x_6318_);
lean_ctor_set(v___x_6320_, 1, v___x_6319_);
v___x_6321_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6322_, 0, v___x_6320_);
lean_ctor_set(v___x_6322_, 1, v___x_6321_);
v___x_6323_ = l_Lean_Exception_toMessageData(v_exception_6313_);
v___x_6324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6324_, 0, v___x_6322_);
lean_ctor_set(v___x_6324_, 1, v___x_6323_);
v___x_6325_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6324_, v___y_6306_, v___y_6307_, v___y_6308_, v___y_6309_);
return v___x_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6326_, lean_object* v___y_6327_, lean_object* v___y_6328_, lean_object* v___y_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_){
_start:
{
lean_object* v_res_6332_; 
v_res_6332_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6326_, v___y_6327_, v___y_6328_, v___y_6329_, v___y_6330_);
lean_dec(v___y_6330_);
lean_dec_ref(v___y_6329_);
lean_dec(v___y_6328_);
lean_dec_ref(v___y_6327_);
return v_res_6332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6333_, size_t v_i_6334_, size_t v_stop_6335_, lean_object* v_b_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_){
_start:
{
uint8_t v___x_6342_; 
v___x_6342_ = lean_usize_dec_eq(v_i_6334_, v_stop_6335_);
if (v___x_6342_ == 0)
{
lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6343_ = lean_array_uget_borrowed(v_as_6333_, v_i_6334_);
lean_inc(v___x_6343_);
v___x_6344_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6343_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
if (lean_obj_tag(v___x_6344_) == 0)
{
lean_object* v_a_6345_; size_t v___x_6346_; size_t v___x_6347_; 
v_a_6345_ = lean_ctor_get(v___x_6344_, 0);
lean_inc(v_a_6345_);
lean_dec_ref_known(v___x_6344_, 1);
v___x_6346_ = ((size_t)1ULL);
v___x_6347_ = lean_usize_add(v_i_6334_, v___x_6346_);
v_i_6334_ = v___x_6347_;
v_b_6336_ = v_a_6345_;
goto _start;
}
else
{
return v___x_6344_;
}
}
else
{
lean_object* v___x_6349_; 
v___x_6349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6349_, 0, v_b_6336_);
return v___x_6349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6350_, lean_object* v_i_6351_, lean_object* v_stop_6352_, lean_object* v_b_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_){
_start:
{
size_t v_i_boxed_6359_; size_t v_stop_boxed_6360_; lean_object* v_res_6361_; 
v_i_boxed_6359_ = lean_unbox_usize(v_i_6351_);
lean_dec(v_i_6351_);
v_stop_boxed_6360_ = lean_unbox_usize(v_stop_6352_);
lean_dec(v_stop_6352_);
v_res_6361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6350_, v_i_boxed_6359_, v_stop_boxed_6360_, v_b_6353_, v___y_6354_, v___y_6355_, v___y_6356_, v___y_6357_);
lean_dec(v___y_6357_);
lean_dec_ref(v___y_6356_);
lean_dec(v___y_6355_);
lean_dec_ref(v___y_6354_);
lean_dec_ref(v_as_6350_);
return v_res_6361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6362_, size_t v_i_6363_, size_t v_stop_6364_, lean_object* v_b_6365_){
_start:
{
uint8_t v___x_6366_; 
v___x_6366_ = lean_usize_dec_eq(v_i_6363_, v_stop_6364_);
if (v___x_6366_ == 0)
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; size_t v___x_6370_; size_t v___x_6371_; 
v___x_6367_ = lean_array_uget_borrowed(v_as_6362_, v_i_6363_);
lean_inc(v___x_6367_);
v___x_6368_ = lean_task_get_own(v___x_6367_);
v___x_6369_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6365_, v___x_6368_);
v___x_6370_ = ((size_t)1ULL);
v___x_6371_ = lean_usize_add(v_i_6363_, v___x_6370_);
v_i_6363_ = v___x_6371_;
v_b_6365_ = v___x_6369_;
goto _start;
}
else
{
return v_b_6365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6373_, lean_object* v_i_6374_, lean_object* v_stop_6375_, lean_object* v_b_6376_){
_start:
{
size_t v_i_boxed_6377_; size_t v_stop_boxed_6378_; lean_object* v_res_6379_; 
v_i_boxed_6377_ = lean_unbox_usize(v_i_6374_);
lean_dec(v_i_6374_);
v_stop_boxed_6378_ = lean_unbox_usize(v_stop_6375_);
lean_dec(v_stop_6375_);
v_res_6379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6373_, v_i_boxed_6377_, v_stop_boxed_6378_, v_b_6376_);
lean_dec_ref(v_as_6373_);
return v_res_6379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6380_, lean_object* v_tasks_6381_){
_start:
{
lean_object* v___x_6382_; lean_object* v___x_6383_; uint8_t v___x_6384_; 
v___x_6382_ = lean_unsigned_to_nat(0u);
v___x_6383_ = lean_array_get_size(v_tasks_6381_);
v___x_6384_ = lean_nat_dec_lt(v___x_6382_, v___x_6383_);
if (v___x_6384_ == 0)
{
return v_z_6380_;
}
else
{
size_t v___x_6385_; size_t v___x_6386_; lean_object* v___x_6387_; 
v___x_6385_ = ((size_t)0ULL);
v___x_6386_ = lean_usize_of_nat(v___x_6383_);
v___x_6387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6381_, v___x_6385_, v___x_6386_, v_z_6380_);
return v___x_6387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6388_, lean_object* v_tasks_6389_){
_start:
{
lean_object* v_res_6390_; 
v_res_6390_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6388_, v_tasks_6389_);
lean_dec_ref(v_tasks_6389_);
return v_res_6390_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; 
v___x_6391_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6392_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6393_, 0, v___x_6392_);
lean_ctor_set(v___x_6393_, 1, v___x_6391_);
return v___x_6393_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6394_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6395_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6396_, 0, v___x_6395_);
lean_ctor_set(v___x_6396_, 1, v___x_6394_);
return v___x_6396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6397_, lean_object* v_ngen_6398_, lean_object* v_env_6399_, lean_object* v_act_6400_, lean_object* v_constantsPerTask_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_){
_start:
{
lean_object* v___x_6407_; lean_object* v_moduleData_6408_; lean_object* v_n_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v_a_6413_; lean_object* v___x_6415_; uint8_t v_isShared_6416_; uint8_t v_isSharedCheck_6448_; 
v___x_6407_ = l_Lean_Environment_header(v_env_6399_);
v_moduleData_6408_ = lean_ctor_get(v___x_6407_, 6);
lean_inc_ref(v_moduleData_6408_);
lean_dec_ref(v___x_6407_);
v_n_6409_ = lean_array_get_size(v_moduleData_6408_);
lean_dec_ref(v_moduleData_6408_);
v___x_6410_ = lean_unsigned_to_nat(0u);
v___x_6411_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6412_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6397_, v_env_6399_, v_act_6400_, v_constantsPerTask_6401_, v_n_6409_, v_ngen_6398_, v___x_6411_, v___x_6410_, v___x_6410_, v___x_6410_);
v_a_6413_ = lean_ctor_get(v___x_6412_, 0);
v_isSharedCheck_6448_ = !lean_is_exclusive(v___x_6412_);
if (v_isSharedCheck_6448_ == 0)
{
v___x_6415_ = v___x_6412_;
v_isShared_6416_ = v_isSharedCheck_6448_;
goto v_resetjp_6414_;
}
else
{
lean_inc(v_a_6413_);
lean_dec(v___x_6412_);
v___x_6415_ = lean_box(0);
v_isShared_6416_ = v_isSharedCheck_6448_;
goto v_resetjp_6414_;
}
v_resetjp_6414_:
{
lean_object* v___x_6417_; lean_object* v_r_6418_; lean_object* v_tree_6419_; lean_object* v_errors_6420_; lean_object* v___x_6421_; uint8_t v___x_6422_; 
v___x_6417_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6418_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6417_, v_a_6413_);
lean_dec(v_a_6413_);
v_tree_6419_ = lean_ctor_get(v_r_6418_, 0);
lean_inc_ref(v_tree_6419_);
v_errors_6420_ = lean_ctor_get(v_r_6418_, 1);
lean_inc_ref(v_errors_6420_);
lean_dec_ref(v_r_6418_);
v___x_6421_ = lean_array_get_size(v_errors_6420_);
v___x_6422_ = lean_nat_dec_lt(v___x_6410_, v___x_6421_);
if (v___x_6422_ == 0)
{
lean_object* v___x_6423_; lean_object* v___x_6425_; 
lean_dec_ref(v_errors_6420_);
v___x_6423_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6419_);
if (v_isShared_6416_ == 0)
{
lean_ctor_set(v___x_6415_, 0, v___x_6423_);
v___x_6425_ = v___x_6415_;
goto v_reusejp_6424_;
}
else
{
lean_object* v_reuseFailAlloc_6426_; 
v_reuseFailAlloc_6426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6426_, 0, v___x_6423_);
v___x_6425_ = v_reuseFailAlloc_6426_;
goto v_reusejp_6424_;
}
v_reusejp_6424_:
{
return v___x_6425_;
}
}
else
{
lean_object* v___x_6427_; size_t v___x_6428_; size_t v___x_6429_; lean_object* v___x_6430_; 
lean_del_object(v___x_6415_);
v___x_6427_ = lean_box(0);
v___x_6428_ = ((size_t)0ULL);
v___x_6429_ = lean_usize_of_nat(v___x_6421_);
v___x_6430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6420_, v___x_6428_, v___x_6429_, v___x_6427_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_);
lean_dec_ref(v_errors_6420_);
if (lean_obj_tag(v___x_6430_) == 0)
{
lean_object* v___x_6432_; uint8_t v_isShared_6433_; uint8_t v_isSharedCheck_6438_; 
v_isSharedCheck_6438_ = !lean_is_exclusive(v___x_6430_);
if (v_isSharedCheck_6438_ == 0)
{
lean_object* v_unused_6439_; 
v_unused_6439_ = lean_ctor_get(v___x_6430_, 0);
lean_dec(v_unused_6439_);
v___x_6432_ = v___x_6430_;
v_isShared_6433_ = v_isSharedCheck_6438_;
goto v_resetjp_6431_;
}
else
{
lean_dec(v___x_6430_);
v___x_6432_ = lean_box(0);
v_isShared_6433_ = v_isSharedCheck_6438_;
goto v_resetjp_6431_;
}
v_resetjp_6431_:
{
lean_object* v___x_6434_; lean_object* v___x_6436_; 
v___x_6434_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6419_);
if (v_isShared_6433_ == 0)
{
lean_ctor_set(v___x_6432_, 0, v___x_6434_);
v___x_6436_ = v___x_6432_;
goto v_reusejp_6435_;
}
else
{
lean_object* v_reuseFailAlloc_6437_; 
v_reuseFailAlloc_6437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6437_, 0, v___x_6434_);
v___x_6436_ = v_reuseFailAlloc_6437_;
goto v_reusejp_6435_;
}
v_reusejp_6435_:
{
return v___x_6436_;
}
}
}
else
{
lean_object* v_a_6440_; lean_object* v___x_6442_; uint8_t v_isShared_6443_; uint8_t v_isSharedCheck_6447_; 
lean_dec_ref(v_tree_6419_);
v_a_6440_ = lean_ctor_get(v___x_6430_, 0);
v_isSharedCheck_6447_ = !lean_is_exclusive(v___x_6430_);
if (v_isSharedCheck_6447_ == 0)
{
v___x_6442_ = v___x_6430_;
v_isShared_6443_ = v_isSharedCheck_6447_;
goto v_resetjp_6441_;
}
else
{
lean_inc(v_a_6440_);
lean_dec(v___x_6430_);
v___x_6442_ = lean_box(0);
v_isShared_6443_ = v_isSharedCheck_6447_;
goto v_resetjp_6441_;
}
v_resetjp_6441_:
{
lean_object* v___x_6445_; 
if (v_isShared_6443_ == 0)
{
v___x_6445_ = v___x_6442_;
goto v_reusejp_6444_;
}
else
{
lean_object* v_reuseFailAlloc_6446_; 
v_reuseFailAlloc_6446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_a_6440_);
v___x_6445_ = v_reuseFailAlloc_6446_;
goto v_reusejp_6444_;
}
v_reusejp_6444_:
{
return v___x_6445_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6449_, lean_object* v_ngen_6450_, lean_object* v_env_6451_, lean_object* v_act_6452_, lean_object* v_constantsPerTask_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_){
_start:
{
lean_object* v_res_6459_; 
v_res_6459_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6449_, v_ngen_6450_, v_env_6451_, v_act_6452_, v_constantsPerTask_6453_, v___y_6454_, v___y_6455_, v___y_6456_, v___y_6457_);
lean_dec(v___y_6457_);
lean_dec_ref(v___y_6456_);
lean_dec(v___y_6455_);
lean_dec_ref(v___y_6454_);
lean_dec(v_constantsPerTask_6453_);
return v_res_6459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6460_, lean_object* v___x_6461_, lean_object* v_addEntry_6462_, lean_object* v_constantsPerTask_6463_, lean_object* v_droppedEntriesRef_6464_, lean_object* v_droppedKeys_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_){
_start:
{
lean_object* v___x_6471_; lean_object* v_env_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6471_ = lean_st_ref_get(v___y_6469_);
v_env_6472_ = lean_ctor_get(v___x_6471_, 0);
lean_inc_ref(v_env_6472_);
lean_dec(v___x_6471_);
lean_inc_ref(v_a_6460_);
v___x_6473_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6460_);
v___x_6474_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6473_, v___x_6461_, v_env_6472_, v_addEntry_6462_, v_constantsPerTask_6463_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
if (lean_obj_tag(v___x_6474_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6464_) == 1)
{
lean_object* v_a_6475_; lean_object* v_val_6476_; lean_object* v___x_6478_; uint8_t v_isShared_6479_; uint8_t v_isSharedCheck_6509_; 
v_a_6475_ = lean_ctor_get(v___x_6474_, 0);
lean_inc(v_a_6475_);
lean_dec_ref_known(v___x_6474_, 1);
v_val_6476_ = lean_ctor_get(v_droppedEntriesRef_6464_, 0);
v_isSharedCheck_6509_ = !lean_is_exclusive(v_droppedEntriesRef_6464_);
if (v_isSharedCheck_6509_ == 0)
{
v___x_6478_ = v_droppedEntriesRef_6464_;
v_isShared_6479_ = v_isSharedCheck_6509_;
goto v_resetjp_6477_;
}
else
{
lean_inc(v_val_6476_);
lean_dec(v_droppedEntriesRef_6464_);
v___x_6478_ = lean_box(0);
v_isShared_6479_ = v_isSharedCheck_6509_;
goto v_resetjp_6477_;
}
v_resetjp_6477_:
{
lean_object* v___x_6480_; 
v___x_6480_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6475_, v_droppedKeys_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
lean_dec(v_droppedKeys_6465_);
if (lean_obj_tag(v___x_6480_) == 0)
{
lean_object* v_a_6481_; lean_object* v___x_6483_; uint8_t v_isShared_6484_; uint8_t v_isSharedCheck_6500_; 
v_a_6481_ = lean_ctor_get(v___x_6480_, 0);
v_isSharedCheck_6500_ = !lean_is_exclusive(v___x_6480_);
if (v_isSharedCheck_6500_ == 0)
{
v___x_6483_ = v___x_6480_;
v_isShared_6484_ = v_isSharedCheck_6500_;
goto v_resetjp_6482_;
}
else
{
lean_inc(v_a_6481_);
lean_dec(v___x_6480_);
v___x_6483_ = lean_box(0);
v_isShared_6484_ = v_isSharedCheck_6500_;
goto v_resetjp_6482_;
}
v_resetjp_6482_:
{
lean_object* v_fst_6485_; lean_object* v_snd_6486_; lean_object* v___x_6487_; lean_object* v___y_6489_; 
v_fst_6485_ = lean_ctor_get(v_a_6481_, 0);
lean_inc(v_fst_6485_);
v_snd_6486_ = lean_ctor_get(v_a_6481_, 1);
lean_inc(v_snd_6486_);
lean_dec(v_a_6481_);
v___x_6487_ = lean_st_ref_get(v_val_6476_);
if (lean_obj_tag(v___x_6487_) == 0)
{
lean_object* v___x_6498_; 
v___x_6498_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6489_ = v___x_6498_;
goto v___jp_6488_;
}
else
{
lean_object* v_val_6499_; 
v_val_6499_ = lean_ctor_get(v___x_6487_, 0);
lean_inc(v_val_6499_);
lean_dec_ref_known(v___x_6487_, 1);
v___y_6489_ = v_val_6499_;
goto v___jp_6488_;
}
v___jp_6488_:
{
lean_object* v___x_6490_; lean_object* v___x_6492_; 
v___x_6490_ = l_Array_append___redArg(v___y_6489_, v_fst_6485_);
lean_dec(v_fst_6485_);
if (v_isShared_6479_ == 0)
{
lean_ctor_set(v___x_6478_, 0, v___x_6490_);
v___x_6492_ = v___x_6478_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6497_; 
v_reuseFailAlloc_6497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6497_, 0, v___x_6490_);
v___x_6492_ = v_reuseFailAlloc_6497_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
lean_object* v___x_6493_; lean_object* v___x_6495_; 
v___x_6493_ = lean_st_ref_swap(v_val_6476_, v___x_6492_);
lean_dec(v_val_6476_);
lean_dec(v___x_6493_);
if (v_isShared_6484_ == 0)
{
lean_ctor_set(v___x_6483_, 0, v_snd_6486_);
v___x_6495_ = v___x_6483_;
goto v_reusejp_6494_;
}
else
{
lean_object* v_reuseFailAlloc_6496_; 
v_reuseFailAlloc_6496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_snd_6486_);
v___x_6495_ = v_reuseFailAlloc_6496_;
goto v_reusejp_6494_;
}
v_reusejp_6494_:
{
return v___x_6495_;
}
}
}
}
}
else
{
lean_object* v_a_6501_; lean_object* v___x_6503_; uint8_t v_isShared_6504_; uint8_t v_isSharedCheck_6508_; 
lean_del_object(v___x_6478_);
lean_dec(v_val_6476_);
v_a_6501_ = lean_ctor_get(v___x_6480_, 0);
v_isSharedCheck_6508_ = !lean_is_exclusive(v___x_6480_);
if (v_isSharedCheck_6508_ == 0)
{
v___x_6503_ = v___x_6480_;
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
else
{
lean_inc(v_a_6501_);
lean_dec(v___x_6480_);
v___x_6503_ = lean_box(0);
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
v_resetjp_6502_:
{
lean_object* v___x_6506_; 
if (v_isShared_6504_ == 0)
{
v___x_6506_ = v___x_6503_;
goto v_reusejp_6505_;
}
else
{
lean_object* v_reuseFailAlloc_6507_; 
v_reuseFailAlloc_6507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_a_6501_);
v___x_6506_ = v_reuseFailAlloc_6507_;
goto v_reusejp_6505_;
}
v_reusejp_6505_:
{
return v___x_6506_;
}
}
}
}
}
else
{
lean_object* v_a_6510_; lean_object* v___x_6511_; 
lean_dec(v_droppedEntriesRef_6464_);
v_a_6510_ = lean_ctor_get(v___x_6474_, 0);
lean_inc(v_a_6510_);
lean_dec_ref_known(v___x_6474_, 1);
v___x_6511_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6510_, v_droppedKeys_6465_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
return v___x_6511_;
}
}
else
{
lean_dec(v_droppedKeys_6465_);
lean_dec(v_droppedEntriesRef_6464_);
return v___x_6474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6512_, lean_object* v___x_6513_, lean_object* v_addEntry_6514_, lean_object* v_constantsPerTask_6515_, lean_object* v_droppedEntriesRef_6516_, lean_object* v_droppedKeys_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_){
_start:
{
lean_object* v_res_6523_; 
v_res_6523_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6512_, v___x_6513_, v_addEntry_6514_, v_constantsPerTask_6515_, v_droppedEntriesRef_6516_, v_droppedKeys_6517_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_);
lean_dec(v___y_6521_);
lean_dec_ref(v___y_6520_);
lean_dec(v___y_6519_);
lean_dec_ref(v___y_6518_);
lean_dec(v_constantsPerTask_6515_);
lean_dec_ref(v_a_6512_);
return v_res_6523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ref_6525_, lean_object* v_addEntry_6526_, lean_object* v_droppedKeys_6527_, lean_object* v_constantsPerTask_6528_, lean_object* v_droppedEntriesRef_6529_, lean_object* v_ty_6530_, lean_object* v_a_6531_, lean_object* v_a_6532_, lean_object* v_a_6533_, lean_object* v_a_6534_){
_start:
{
lean_object* v_a_6537_; lean_object* v___x_6559_; lean_object* v_ngen_6560_; lean_object* v_namePrefix_6561_; lean_object* v_idx_6562_; lean_object* v___x_6564_; uint8_t v_isShared_6565_; uint8_t v_isSharedCheck_6607_; 
v___x_6559_ = lean_st_ref_get(v_a_6534_);
v_ngen_6560_ = lean_ctor_get(v___x_6559_, 2);
lean_inc_ref(v_ngen_6560_);
lean_dec(v___x_6559_);
v_namePrefix_6561_ = lean_ctor_get(v_ngen_6560_, 0);
v_idx_6562_ = lean_ctor_get(v_ngen_6560_, 1);
v_isSharedCheck_6607_ = !lean_is_exclusive(v_ngen_6560_);
if (v_isSharedCheck_6607_ == 0)
{
v___x_6564_ = v_ngen_6560_;
v_isShared_6565_ = v_isSharedCheck_6607_;
goto v_resetjp_6563_;
}
else
{
lean_inc(v_idx_6562_);
lean_inc(v_namePrefix_6561_);
lean_dec(v_ngen_6560_);
v___x_6564_ = lean_box(0);
v_isShared_6565_ = v_isSharedCheck_6607_;
goto v_resetjp_6563_;
}
v___jp_6536_:
{
lean_object* v___x_6538_; 
v___x_6538_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6537_, v_ty_6530_, v_a_6531_, v_a_6532_, v_a_6533_, v_a_6534_);
if (lean_obj_tag(v___x_6538_) == 0)
{
lean_object* v_a_6539_; lean_object* v___x_6541_; uint8_t v_isShared_6542_; uint8_t v_isSharedCheck_6550_; 
v_a_6539_ = lean_ctor_get(v___x_6538_, 0);
v_isSharedCheck_6550_ = !lean_is_exclusive(v___x_6538_);
if (v_isSharedCheck_6550_ == 0)
{
v___x_6541_ = v___x_6538_;
v_isShared_6542_ = v_isSharedCheck_6550_;
goto v_resetjp_6540_;
}
else
{
lean_inc(v_a_6539_);
lean_dec(v___x_6538_);
v___x_6541_ = lean_box(0);
v_isShared_6542_ = v_isSharedCheck_6550_;
goto v_resetjp_6540_;
}
v_resetjp_6540_:
{
lean_object* v_fst_6543_; lean_object* v_snd_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6548_; 
v_fst_6543_ = lean_ctor_get(v_a_6539_, 0);
lean_inc(v_fst_6543_);
v_snd_6544_ = lean_ctor_get(v_a_6539_, 1);
lean_inc(v_snd_6544_);
lean_dec(v_a_6539_);
v___x_6545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6545_, 0, v_snd_6544_);
v___x_6546_ = lean_st_ref_swap(v_ref_6525_, v___x_6545_);
lean_dec(v___x_6546_);
if (v_isShared_6542_ == 0)
{
lean_ctor_set(v___x_6541_, 0, v_fst_6543_);
v___x_6548_ = v___x_6541_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_fst_6543_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
else
{
lean_object* v_a_6551_; lean_object* v___x_6553_; uint8_t v_isShared_6554_; uint8_t v_isSharedCheck_6558_; 
v_a_6551_ = lean_ctor_get(v___x_6538_, 0);
v_isSharedCheck_6558_ = !lean_is_exclusive(v___x_6538_);
if (v_isSharedCheck_6558_ == 0)
{
v___x_6553_ = v___x_6538_;
v_isShared_6554_ = v_isSharedCheck_6558_;
goto v_resetjp_6552_;
}
else
{
lean_inc(v_a_6551_);
lean_dec(v___x_6538_);
v___x_6553_ = lean_box(0);
v_isShared_6554_ = v_isSharedCheck_6558_;
goto v_resetjp_6552_;
}
v_resetjp_6552_:
{
lean_object* v___x_6556_; 
if (v_isShared_6554_ == 0)
{
v___x_6556_ = v___x_6553_;
goto v_reusejp_6555_;
}
else
{
lean_object* v_reuseFailAlloc_6557_; 
v_reuseFailAlloc_6557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6557_, 0, v_a_6551_);
v___x_6556_ = v_reuseFailAlloc_6557_;
goto v_reusejp_6555_;
}
v_reusejp_6555_:
{
return v___x_6556_;
}
}
}
}
v_resetjp_6563_:
{
lean_object* v___x_6566_; lean_object* v_env_6567_; lean_object* v_nextMacroScope_6568_; lean_object* v_auxDeclNGen_6569_; lean_object* v_traceState_6570_; lean_object* v_cache_6571_; lean_object* v_messages_6572_; lean_object* v_infoState_6573_; lean_object* v_snapshotTasks_6574_; lean_object* v___x_6576_; uint8_t v_isShared_6577_; uint8_t v_isSharedCheck_6605_; 
v___x_6566_ = lean_st_ref_take(v_a_6534_);
v_env_6567_ = lean_ctor_get(v___x_6566_, 0);
v_nextMacroScope_6568_ = lean_ctor_get(v___x_6566_, 1);
v_auxDeclNGen_6569_ = lean_ctor_get(v___x_6566_, 3);
v_traceState_6570_ = lean_ctor_get(v___x_6566_, 4);
v_cache_6571_ = lean_ctor_get(v___x_6566_, 5);
v_messages_6572_ = lean_ctor_get(v___x_6566_, 6);
v_infoState_6573_ = lean_ctor_get(v___x_6566_, 7);
v_snapshotTasks_6574_ = lean_ctor_get(v___x_6566_, 8);
v_isSharedCheck_6605_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6605_ == 0)
{
lean_object* v_unused_6606_; 
v_unused_6606_ = lean_ctor_get(v___x_6566_, 2);
lean_dec(v_unused_6606_);
v___x_6576_ = v___x_6566_;
v_isShared_6577_ = v_isSharedCheck_6605_;
goto v_resetjp_6575_;
}
else
{
lean_inc(v_snapshotTasks_6574_);
lean_inc(v_infoState_6573_);
lean_inc(v_messages_6572_);
lean_inc(v_cache_6571_);
lean_inc(v_traceState_6570_);
lean_inc(v_auxDeclNGen_6569_);
lean_inc(v_nextMacroScope_6568_);
lean_inc(v_env_6567_);
lean_dec(v___x_6566_);
v___x_6576_ = lean_box(0);
v_isShared_6577_ = v_isSharedCheck_6605_;
goto v_resetjp_6575_;
}
v_resetjp_6575_:
{
lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6582_; 
lean_inc(v_idx_6562_);
lean_inc(v_namePrefix_6561_);
v___x_6578_ = l_Lean_Name_num___override(v_namePrefix_6561_, v_idx_6562_);
v___x_6579_ = lean_unsigned_to_nat(1u);
v___x_6580_ = lean_nat_add(v_idx_6562_, v___x_6579_);
lean_dec(v_idx_6562_);
if (v_isShared_6565_ == 0)
{
lean_ctor_set(v___x_6564_, 1, v___x_6580_);
v___x_6582_ = v___x_6564_;
goto v_reusejp_6581_;
}
else
{
lean_object* v_reuseFailAlloc_6604_; 
v_reuseFailAlloc_6604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_namePrefix_6561_);
lean_ctor_set(v_reuseFailAlloc_6604_, 1, v___x_6580_);
v___x_6582_ = v_reuseFailAlloc_6604_;
goto v_reusejp_6581_;
}
v_reusejp_6581_:
{
lean_object* v___x_6584_; 
if (v_isShared_6577_ == 0)
{
lean_ctor_set(v___x_6576_, 2, v___x_6582_);
v___x_6584_ = v___x_6576_;
goto v_reusejp_6583_;
}
else
{
lean_object* v_reuseFailAlloc_6603_; 
v_reuseFailAlloc_6603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6603_, 0, v_env_6567_);
lean_ctor_set(v_reuseFailAlloc_6603_, 1, v_nextMacroScope_6568_);
lean_ctor_set(v_reuseFailAlloc_6603_, 2, v___x_6582_);
lean_ctor_set(v_reuseFailAlloc_6603_, 3, v_auxDeclNGen_6569_);
lean_ctor_set(v_reuseFailAlloc_6603_, 4, v_traceState_6570_);
lean_ctor_set(v_reuseFailAlloc_6603_, 5, v_cache_6571_);
lean_ctor_set(v_reuseFailAlloc_6603_, 6, v_messages_6572_);
lean_ctor_set(v_reuseFailAlloc_6603_, 7, v_infoState_6573_);
lean_ctor_set(v_reuseFailAlloc_6603_, 8, v_snapshotTasks_6574_);
v___x_6584_ = v_reuseFailAlloc_6603_;
goto v_reusejp_6583_;
}
v_reusejp_6583_:
{
lean_object* v___x_6585_; lean_object* v___x_6586_; 
v___x_6585_ = lean_st_ref_put(v_a_6534_, v___x_6584_);
v___x_6586_ = lean_st_ref_get(v_ref_6525_);
if (lean_obj_tag(v___x_6586_) == 0)
{
lean_object* v_options_6587_; lean_object* v___x_6588_; lean_object* v___f_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; 
v_options_6587_ = lean_ctor_get(v_a_6533_, 1);
v___x_6588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6588_, 0, v___x_6578_);
lean_ctor_set(v___x_6588_, 1, v___x_6579_);
lean_inc_ref(v_a_6533_);
v___f_6589_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6589_, 0, v_a_6533_);
lean_closure_set(v___f_6589_, 1, v___x_6588_);
lean_closure_set(v___f_6589_, 2, v_addEntry_6526_);
lean_closure_set(v___f_6589_, 3, v_constantsPerTask_6528_);
lean_closure_set(v___f_6589_, 4, v_droppedEntriesRef_6529_);
lean_closure_set(v___f_6589_, 5, v_droppedKeys_6527_);
v___x_6590_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6591_ = lean_box(0);
v___x_6592_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6590_, v_options_6587_, v___f_6589_, v___x_6591_, v_a_6531_, v_a_6532_, v_a_6533_, v_a_6534_);
if (lean_obj_tag(v___x_6592_) == 0)
{
lean_object* v_a_6593_; 
v_a_6593_ = lean_ctor_get(v___x_6592_, 0);
lean_inc(v_a_6593_);
lean_dec_ref_known(v___x_6592_, 1);
v_a_6537_ = v_a_6593_;
goto v___jp_6536_;
}
else
{
lean_object* v_a_6594_; lean_object* v___x_6596_; uint8_t v_isShared_6597_; uint8_t v_isSharedCheck_6601_; 
lean_dec_ref(v_ty_6530_);
v_a_6594_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6601_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6601_ == 0)
{
v___x_6596_ = v___x_6592_;
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
else
{
lean_inc(v_a_6594_);
lean_dec(v___x_6592_);
v___x_6596_ = lean_box(0);
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
v_resetjp_6595_:
{
lean_object* v___x_6599_; 
if (v_isShared_6597_ == 0)
{
v___x_6599_ = v___x_6596_;
goto v_reusejp_6598_;
}
else
{
lean_object* v_reuseFailAlloc_6600_; 
v_reuseFailAlloc_6600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6600_, 0, v_a_6594_);
v___x_6599_ = v_reuseFailAlloc_6600_;
goto v_reusejp_6598_;
}
v_reusejp_6598_:
{
return v___x_6599_;
}
}
}
}
else
{
lean_object* v_val_6602_; 
lean_dec(v___x_6578_);
lean_dec(v_droppedEntriesRef_6529_);
lean_dec(v_constantsPerTask_6528_);
lean_dec(v_droppedKeys_6527_);
lean_dec_ref(v_addEntry_6526_);
v_val_6602_ = lean_ctor_get(v___x_6586_, 0);
lean_inc(v_val_6602_);
lean_dec_ref_known(v___x_6586_, 1);
v_a_6537_ = v_val_6602_;
goto v___jp_6536_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ref_6608_, lean_object* v_addEntry_6609_, lean_object* v_droppedKeys_6610_, lean_object* v_constantsPerTask_6611_, lean_object* v_droppedEntriesRef_6612_, lean_object* v_ty_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_){
_start:
{
lean_object* v_res_6619_; 
v_res_6619_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6608_, v_addEntry_6609_, v_droppedKeys_6610_, v_constantsPerTask_6611_, v_droppedEntriesRef_6612_, v_ty_6613_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_);
lean_dec(v_a_6617_);
lean_dec_ref(v_a_6616_);
lean_dec(v_a_6615_);
lean_dec_ref(v_a_6614_);
lean_dec(v_ref_6608_);
return v_res_6619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6620_, lean_object* v_ref_6621_, lean_object* v_addEntry_6622_, lean_object* v_droppedKeys_6623_, lean_object* v_constantsPerTask_6624_, lean_object* v_droppedEntriesRef_6625_, lean_object* v_ty_6626_, lean_object* v_a_6627_, lean_object* v_a_6628_, lean_object* v_a_6629_, lean_object* v_a_6630_){
_start:
{
lean_object* v___x_6632_; 
v___x_6632_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_6621_, v_addEntry_6622_, v_droppedKeys_6623_, v_constantsPerTask_6624_, v_droppedEntriesRef_6625_, v_ty_6626_, v_a_6627_, v_a_6628_, v_a_6629_, v_a_6630_);
return v___x_6632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6633_, lean_object* v_ref_6634_, lean_object* v_addEntry_6635_, lean_object* v_droppedKeys_6636_, lean_object* v_constantsPerTask_6637_, lean_object* v_droppedEntriesRef_6638_, lean_object* v_ty_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_, lean_object* v_a_6642_, lean_object* v_a_6643_, lean_object* v_a_6644_){
_start:
{
lean_object* v_res_6645_; 
v_res_6645_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6633_, v_ref_6634_, v_addEntry_6635_, v_droppedKeys_6636_, v_constantsPerTask_6637_, v_droppedEntriesRef_6638_, v_ty_6639_, v_a_6640_, v_a_6641_, v_a_6642_, v_a_6643_);
lean_dec(v_a_6643_);
lean_dec_ref(v_a_6642_);
lean_dec(v_a_6641_);
lean_dec_ref(v_a_6640_);
lean_dec(v_ref_6634_);
return v_res_6645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6646_, lean_object* v_cctx_6647_, lean_object* v_ngen_6648_, lean_object* v_env_6649_, lean_object* v_act_6650_, lean_object* v_constantsPerTask_6651_, lean_object* v___y_6652_, lean_object* v___y_6653_, lean_object* v___y_6654_, lean_object* v___y_6655_){
_start:
{
lean_object* v___x_6657_; 
v___x_6657_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6647_, v_ngen_6648_, v_env_6649_, v_act_6650_, v_constantsPerTask_6651_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
return v___x_6657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6658_, lean_object* v_cctx_6659_, lean_object* v_ngen_6660_, lean_object* v_env_6661_, lean_object* v_act_6662_, lean_object* v_constantsPerTask_6663_, lean_object* v___y_6664_, lean_object* v___y_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_){
_start:
{
lean_object* v_res_6669_; 
v_res_6669_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6658_, v_cctx_6659_, v_ngen_6660_, v_env_6661_, v_act_6662_, v_constantsPerTask_6663_, v___y_6664_, v___y_6665_, v___y_6666_, v___y_6667_);
lean_dec(v___y_6667_);
lean_dec_ref(v___y_6666_);
lean_dec(v___y_6665_);
lean_dec_ref(v___y_6664_);
lean_dec(v_constantsPerTask_6663_);
return v_res_6669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6670_, lean_object* v_cctx_6671_, lean_object* v_env_6672_, lean_object* v_act_6673_, lean_object* v_constantsPerTask_6674_, lean_object* v_n_6675_, lean_object* v_ngen_6676_, lean_object* v_tasks_6677_, lean_object* v_start_6678_, lean_object* v_cnt_6679_, lean_object* v_idx_6680_, lean_object* v___y_6681_, lean_object* v___y_6682_, lean_object* v___y_6683_, lean_object* v___y_6684_){
_start:
{
lean_object* v___x_6686_; 
v___x_6686_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6671_, v_env_6672_, v_act_6673_, v_constantsPerTask_6674_, v_n_6675_, v_ngen_6676_, v_tasks_6677_, v_start_6678_, v_cnt_6679_, v_idx_6680_);
return v___x_6686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6687_, lean_object* v_cctx_6688_, lean_object* v_env_6689_, lean_object* v_act_6690_, lean_object* v_constantsPerTask_6691_, lean_object* v_n_6692_, lean_object* v_ngen_6693_, lean_object* v_tasks_6694_, lean_object* v_start_6695_, lean_object* v_cnt_6696_, lean_object* v_idx_6697_, lean_object* v___y_6698_, lean_object* v___y_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_){
_start:
{
lean_object* v_res_6703_; 
v_res_6703_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6687_, v_cctx_6688_, v_env_6689_, v_act_6690_, v_constantsPerTask_6691_, v_n_6692_, v_ngen_6693_, v_tasks_6694_, v_start_6695_, v_cnt_6696_, v_idx_6697_, v___y_6698_, v___y_6699_, v___y_6700_, v___y_6701_);
lean_dec(v___y_6701_);
lean_dec_ref(v___y_6700_);
lean_dec(v___y_6699_);
lean_dec_ref(v___y_6698_);
lean_dec(v_constantsPerTask_6691_);
return v_res_6703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6704_, lean_object* v_z_6705_, lean_object* v_tasks_6706_){
_start:
{
lean_object* v___x_6707_; 
v___x_6707_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6705_, v_tasks_6706_);
return v___x_6707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6708_, lean_object* v_z_6709_, lean_object* v_tasks_6710_){
_start:
{
lean_object* v_res_6711_; 
v_res_6711_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6708_, v_z_6709_, v_tasks_6710_);
lean_dec_ref(v_tasks_6710_);
return v_res_6711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6712_, lean_object* v_as_6713_, size_t v_i_6714_, size_t v_stop_6715_, lean_object* v_b_6716_){
_start:
{
lean_object* v___x_6717_; 
v___x_6717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6713_, v_i_6714_, v_stop_6715_, v_b_6716_);
return v___x_6717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6718_, lean_object* v_as_6719_, lean_object* v_i_6720_, lean_object* v_stop_6721_, lean_object* v_b_6722_){
_start:
{
size_t v_i_boxed_6723_; size_t v_stop_boxed_6724_; lean_object* v_res_6725_; 
v_i_boxed_6723_ = lean_unbox_usize(v_i_6720_);
lean_dec(v_i_6720_);
v_stop_boxed_6724_ = lean_unbox_usize(v_stop_6721_);
lean_dec(v_stop_6721_);
v_res_6725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6718_, v_as_6719_, v_i_boxed_6723_, v_stop_boxed_6724_, v_b_6722_);
lean_dec_ref(v_as_6719_);
return v_res_6725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6726_){
_start:
{
lean_object* v___x_6728_; lean_object* v_ngen_6729_; lean_object* v_namePrefix_6730_; lean_object* v_idx_6731_; lean_object* v___x_6733_; uint8_t v_isShared_6734_; uint8_t v_isSharedCheck_6761_; 
v___x_6728_ = lean_st_ref_get(v___y_6726_);
v_ngen_6729_ = lean_ctor_get(v___x_6728_, 2);
lean_inc_ref(v_ngen_6729_);
lean_dec(v___x_6728_);
v_namePrefix_6730_ = lean_ctor_get(v_ngen_6729_, 0);
v_idx_6731_ = lean_ctor_get(v_ngen_6729_, 1);
v_isSharedCheck_6761_ = !lean_is_exclusive(v_ngen_6729_);
if (v_isSharedCheck_6761_ == 0)
{
v___x_6733_ = v_ngen_6729_;
v_isShared_6734_ = v_isSharedCheck_6761_;
goto v_resetjp_6732_;
}
else
{
lean_inc(v_idx_6731_);
lean_inc(v_namePrefix_6730_);
lean_dec(v_ngen_6729_);
v___x_6733_ = lean_box(0);
v_isShared_6734_ = v_isSharedCheck_6761_;
goto v_resetjp_6732_;
}
v_resetjp_6732_:
{
lean_object* v___x_6735_; lean_object* v_env_6736_; lean_object* v_nextMacroScope_6737_; lean_object* v_auxDeclNGen_6738_; lean_object* v_traceState_6739_; lean_object* v_cache_6740_; lean_object* v_messages_6741_; lean_object* v_infoState_6742_; lean_object* v_snapshotTasks_6743_; lean_object* v___x_6745_; uint8_t v_isShared_6746_; uint8_t v_isSharedCheck_6759_; 
v___x_6735_ = lean_st_ref_take(v___y_6726_);
v_env_6736_ = lean_ctor_get(v___x_6735_, 0);
v_nextMacroScope_6737_ = lean_ctor_get(v___x_6735_, 1);
v_auxDeclNGen_6738_ = lean_ctor_get(v___x_6735_, 3);
v_traceState_6739_ = lean_ctor_get(v___x_6735_, 4);
v_cache_6740_ = lean_ctor_get(v___x_6735_, 5);
v_messages_6741_ = lean_ctor_get(v___x_6735_, 6);
v_infoState_6742_ = lean_ctor_get(v___x_6735_, 7);
v_snapshotTasks_6743_ = lean_ctor_get(v___x_6735_, 8);
v_isSharedCheck_6759_ = !lean_is_exclusive(v___x_6735_);
if (v_isSharedCheck_6759_ == 0)
{
lean_object* v_unused_6760_; 
v_unused_6760_ = lean_ctor_get(v___x_6735_, 2);
lean_dec(v_unused_6760_);
v___x_6745_ = v___x_6735_;
v_isShared_6746_ = v_isSharedCheck_6759_;
goto v_resetjp_6744_;
}
else
{
lean_inc(v_snapshotTasks_6743_);
lean_inc(v_infoState_6742_);
lean_inc(v_messages_6741_);
lean_inc(v_cache_6740_);
lean_inc(v_traceState_6739_);
lean_inc(v_auxDeclNGen_6738_);
lean_inc(v_nextMacroScope_6737_);
lean_inc(v_env_6736_);
lean_dec(v___x_6735_);
v___x_6745_ = lean_box(0);
v_isShared_6746_ = v_isSharedCheck_6759_;
goto v_resetjp_6744_;
}
v_resetjp_6744_:
{
lean_object* v___x_6747_; lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6751_; 
lean_inc(v_idx_6731_);
lean_inc(v_namePrefix_6730_);
v___x_6747_ = l_Lean_Name_num___override(v_namePrefix_6730_, v_idx_6731_);
v___x_6748_ = lean_unsigned_to_nat(1u);
v___x_6749_ = lean_nat_add(v_idx_6731_, v___x_6748_);
lean_dec(v_idx_6731_);
if (v_isShared_6734_ == 0)
{
lean_ctor_set(v___x_6733_, 1, v___x_6749_);
v___x_6751_ = v___x_6733_;
goto v_reusejp_6750_;
}
else
{
lean_object* v_reuseFailAlloc_6758_; 
v_reuseFailAlloc_6758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_namePrefix_6730_);
lean_ctor_set(v_reuseFailAlloc_6758_, 1, v___x_6749_);
v___x_6751_ = v_reuseFailAlloc_6758_;
goto v_reusejp_6750_;
}
v_reusejp_6750_:
{
lean_object* v___x_6753_; 
if (v_isShared_6746_ == 0)
{
lean_ctor_set(v___x_6745_, 2, v___x_6751_);
v___x_6753_ = v___x_6745_;
goto v_reusejp_6752_;
}
else
{
lean_object* v_reuseFailAlloc_6757_; 
v_reuseFailAlloc_6757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_env_6736_);
lean_ctor_set(v_reuseFailAlloc_6757_, 1, v_nextMacroScope_6737_);
lean_ctor_set(v_reuseFailAlloc_6757_, 2, v___x_6751_);
lean_ctor_set(v_reuseFailAlloc_6757_, 3, v_auxDeclNGen_6738_);
lean_ctor_set(v_reuseFailAlloc_6757_, 4, v_traceState_6739_);
lean_ctor_set(v_reuseFailAlloc_6757_, 5, v_cache_6740_);
lean_ctor_set(v_reuseFailAlloc_6757_, 6, v_messages_6741_);
lean_ctor_set(v_reuseFailAlloc_6757_, 7, v_infoState_6742_);
lean_ctor_set(v_reuseFailAlloc_6757_, 8, v_snapshotTasks_6743_);
v___x_6753_ = v_reuseFailAlloc_6757_;
goto v_reusejp_6752_;
}
v_reusejp_6752_:
{
lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; 
v___x_6754_ = lean_st_ref_put(v___y_6726_, v___x_6753_);
v___x_6755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6755_, 0, v___x_6747_);
lean_ctor_set(v___x_6755_, 1, v___x_6748_);
v___x_6756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6756_, 0, v___x_6755_);
return v___x_6756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6762_, lean_object* v___y_6763_){
_start:
{
lean_object* v_res_6764_; 
v_res_6764_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6762_);
lean_dec(v___y_6762_);
return v_res_6764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6765_, lean_object* v___y_6766_){
_start:
{
lean_object* v___x_6768_; 
v___x_6768_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6766_);
return v___x_6768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_){
_start:
{
lean_object* v_res_6772_; 
v_res_6772_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6769_, v___y_6770_);
lean_dec(v___y_6770_);
lean_dec_ref(v___y_6769_);
return v_res_6772_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; 
v___x_6773_ = lean_unsigned_to_nat(32u);
v___x_6774_ = lean_mk_empty_array_with_capacity(v___x_6773_);
v___x_6775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6775_, 0, v___x_6774_);
return v___x_6775_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; 
v___x_6776_ = ((size_t)5ULL);
v___x_6777_ = lean_unsigned_to_nat(0u);
v___x_6778_ = lean_unsigned_to_nat(32u);
v___x_6779_ = lean_mk_empty_array_with_capacity(v___x_6778_);
v___x_6780_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6781_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6781_, 0, v___x_6780_);
lean_ctor_set(v___x_6781_, 1, v___x_6779_);
lean_ctor_set(v___x_6781_, 2, v___x_6777_);
lean_ctor_set(v___x_6781_, 3, v___x_6777_);
lean_ctor_set_usize(v___x_6781_, 4, v___x_6776_);
return v___x_6781_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6782_; lean_object* v___x_6783_; lean_object* v___x_6784_; lean_object* v___x_6785_; 
v___x_6782_ = lean_box(1);
v___x_6783_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6784_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6785_, 0, v___x_6784_);
lean_ctor_set(v___x_6785_, 1, v___x_6783_);
lean_ctor_set(v___x_6785_, 2, v___x_6782_);
return v___x_6785_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_){
_start:
{
lean_object* v___x_6790_; lean_object* v_env_6791_; lean_object* v_options_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; 
v___x_6790_ = lean_st_ref_get(v___y_6788_);
v_env_6791_ = lean_ctor_get(v___x_6790_, 0);
lean_inc_ref(v_env_6791_);
lean_dec(v___x_6790_);
v_options_6792_ = lean_ctor_get(v___y_6787_, 1);
v___x_6793_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6794_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6792_);
v___x_6795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6795_, 0, v_env_6791_);
lean_ctor_set(v___x_6795_, 1, v___x_6793_);
lean_ctor_set(v___x_6795_, 2, v___x_6794_);
lean_ctor_set(v___x_6795_, 3, v_options_6792_);
v___x_6796_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6796_, 0, v___x_6795_);
lean_ctor_set(v___x_6796_, 1, v_msgData_6786_);
v___x_6797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6797_, 0, v___x_6796_);
return v___x_6797_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_){
_start:
{
lean_object* v_res_6802_; 
v_res_6802_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6798_, v___y_6799_, v___y_6800_);
lean_dec(v___y_6800_);
lean_dec_ref(v___y_6799_);
return v_res_6802_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6803_, lean_object* v_msgData_6804_, uint8_t v_severity_6805_, uint8_t v_isSilent_6806_, lean_object* v___y_6807_, lean_object* v___y_6808_){
_start:
{
lean_object* v___y_6811_; lean_object* v___y_6812_; uint8_t v___y_6813_; lean_object* v___y_6814_; lean_object* v___y_6815_; lean_object* v___y_6816_; uint8_t v___y_6817_; lean_object* v___y_6818_; lean_object* v___y_6819_; lean_object* v___y_6847_; uint8_t v___y_6848_; uint8_t v___y_6849_; lean_object* v___y_6850_; lean_object* v___y_6851_; uint8_t v___y_6852_; lean_object* v___y_6853_; lean_object* v___y_6873_; uint8_t v___y_6874_; lean_object* v___y_6875_; uint8_t v___y_6876_; lean_object* v___y_6877_; uint8_t v___y_6878_; lean_object* v___y_6879_; lean_object* v___y_6883_; uint8_t v___y_6884_; uint8_t v___y_6885_; lean_object* v___y_6886_; lean_object* v___y_6887_; uint8_t v___y_6888_; uint8_t v___x_6893_; lean_object* v___y_6895_; lean_object* v___y_6896_; uint8_t v___y_6897_; lean_object* v___y_6898_; uint8_t v___y_6899_; uint8_t v___y_6900_; uint8_t v___y_6902_; uint8_t v___x_6916_; 
v___x_6893_ = 2;
v___x_6916_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6805_, v___x_6893_);
if (v___x_6916_ == 0)
{
v___y_6902_ = v___x_6916_;
goto v___jp_6901_;
}
else
{
uint8_t v___x_6917_; 
lean_inc_ref(v_msgData_6804_);
v___x_6917_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6804_);
v___y_6902_ = v___x_6917_;
goto v___jp_6901_;
}
v___jp_6810_:
{
lean_object* v___x_6820_; lean_object* v_currNamespace_6821_; lean_object* v_openDecls_6822_; lean_object* v_env_6823_; lean_object* v_nextMacroScope_6824_; lean_object* v_ngen_6825_; lean_object* v_auxDeclNGen_6826_; lean_object* v_traceState_6827_; lean_object* v_cache_6828_; lean_object* v_messages_6829_; lean_object* v_infoState_6830_; lean_object* v_snapshotTasks_6831_; lean_object* v___x_6833_; uint8_t v_isShared_6834_; uint8_t v_isSharedCheck_6845_; 
v___x_6820_ = lean_st_ref_take(v___y_6819_);
v_currNamespace_6821_ = lean_ctor_get(v___y_6818_, 5);
v_openDecls_6822_ = lean_ctor_get(v___y_6818_, 6);
v_env_6823_ = lean_ctor_get(v___x_6820_, 0);
v_nextMacroScope_6824_ = lean_ctor_get(v___x_6820_, 1);
v_ngen_6825_ = lean_ctor_get(v___x_6820_, 2);
v_auxDeclNGen_6826_ = lean_ctor_get(v___x_6820_, 3);
v_traceState_6827_ = lean_ctor_get(v___x_6820_, 4);
v_cache_6828_ = lean_ctor_get(v___x_6820_, 5);
v_messages_6829_ = lean_ctor_get(v___x_6820_, 6);
v_infoState_6830_ = lean_ctor_get(v___x_6820_, 7);
v_snapshotTasks_6831_ = lean_ctor_get(v___x_6820_, 8);
v_isSharedCheck_6845_ = !lean_is_exclusive(v___x_6820_);
if (v_isSharedCheck_6845_ == 0)
{
v___x_6833_ = v___x_6820_;
v_isShared_6834_ = v_isSharedCheck_6845_;
goto v_resetjp_6832_;
}
else
{
lean_inc(v_snapshotTasks_6831_);
lean_inc(v_infoState_6830_);
lean_inc(v_messages_6829_);
lean_inc(v_cache_6828_);
lean_inc(v_traceState_6827_);
lean_inc(v_auxDeclNGen_6826_);
lean_inc(v_ngen_6825_);
lean_inc(v_nextMacroScope_6824_);
lean_inc(v_env_6823_);
lean_dec(v___x_6820_);
v___x_6833_ = lean_box(0);
v_isShared_6834_ = v_isSharedCheck_6845_;
goto v_resetjp_6832_;
}
v_resetjp_6832_:
{
lean_object* v___x_6835_; lean_object* v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6840_; 
lean_inc(v_openDecls_6822_);
lean_inc(v_currNamespace_6821_);
v___x_6835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6835_, 0, v_currNamespace_6821_);
lean_ctor_set(v___x_6835_, 1, v_openDecls_6822_);
v___x_6836_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6836_, 0, v___x_6835_);
lean_ctor_set(v___x_6836_, 1, v___y_6815_);
lean_inc_ref(v___y_6816_);
lean_inc_ref(v___y_6811_);
v___x_6837_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6837_, 0, v___y_6811_);
lean_ctor_set(v___x_6837_, 1, v___y_6812_);
lean_ctor_set(v___x_6837_, 2, v___y_6814_);
lean_ctor_set(v___x_6837_, 3, v___y_6816_);
lean_ctor_set(v___x_6837_, 4, v___x_6836_);
lean_ctor_set_uint8(v___x_6837_, sizeof(void*)*5, v___y_6813_);
lean_ctor_set_uint8(v___x_6837_, sizeof(void*)*5 + 1, v___y_6817_);
lean_ctor_set_uint8(v___x_6837_, sizeof(void*)*5 + 2, v_isSilent_6806_);
v___x_6838_ = l_Lean_MessageLog_add(v___x_6837_, v_messages_6829_);
if (v_isShared_6834_ == 0)
{
lean_ctor_set(v___x_6833_, 6, v___x_6838_);
v___x_6840_ = v___x_6833_;
goto v_reusejp_6839_;
}
else
{
lean_object* v_reuseFailAlloc_6844_; 
v_reuseFailAlloc_6844_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6844_, 0, v_env_6823_);
lean_ctor_set(v_reuseFailAlloc_6844_, 1, v_nextMacroScope_6824_);
lean_ctor_set(v_reuseFailAlloc_6844_, 2, v_ngen_6825_);
lean_ctor_set(v_reuseFailAlloc_6844_, 3, v_auxDeclNGen_6826_);
lean_ctor_set(v_reuseFailAlloc_6844_, 4, v_traceState_6827_);
lean_ctor_set(v_reuseFailAlloc_6844_, 5, v_cache_6828_);
lean_ctor_set(v_reuseFailAlloc_6844_, 6, v___x_6838_);
lean_ctor_set(v_reuseFailAlloc_6844_, 7, v_infoState_6830_);
lean_ctor_set(v_reuseFailAlloc_6844_, 8, v_snapshotTasks_6831_);
v___x_6840_ = v_reuseFailAlloc_6844_;
goto v_reusejp_6839_;
}
v_reusejp_6839_:
{
lean_object* v___x_6841_; lean_object* v___x_6842_; lean_object* v___x_6843_; 
v___x_6841_ = lean_st_ref_put(v___y_6819_, v___x_6840_);
v___x_6842_ = lean_box(0);
v___x_6843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6843_, 0, v___x_6842_);
return v___x_6843_;
}
}
}
v___jp_6846_:
{
lean_object* v_fileName_6854_; lean_object* v_fileMap_6855_; lean_object* v___x_6856_; lean_object* v___x_6857_; lean_object* v_a_6858_; lean_object* v___x_6860_; uint8_t v_isShared_6861_; uint8_t v_isSharedCheck_6871_; 
v_fileName_6854_ = lean_ctor_get(v___y_6850_, 0);
v_fileMap_6855_ = lean_ctor_get(v___y_6850_, 1);
v___x_6856_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6804_);
v___x_6857_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6856_, v___y_6807_, v___y_6808_);
v_a_6858_ = lean_ctor_get(v___x_6857_, 0);
v_isSharedCheck_6871_ = !lean_is_exclusive(v___x_6857_);
if (v_isSharedCheck_6871_ == 0)
{
v___x_6860_ = v___x_6857_;
v_isShared_6861_ = v_isSharedCheck_6871_;
goto v_resetjp_6859_;
}
else
{
lean_inc(v_a_6858_);
lean_dec(v___x_6857_);
v___x_6860_ = lean_box(0);
v_isShared_6861_ = v_isSharedCheck_6871_;
goto v_resetjp_6859_;
}
v_resetjp_6859_:
{
lean_object* v___x_6862_; lean_object* v___x_6863_; lean_object* v___x_6864_; lean_object* v___x_6865_; 
lean_inc_ref_n(v_fileMap_6855_, 2);
v___x_6862_ = l_Lean_FileMap_toPosition(v_fileMap_6855_, v___y_6851_);
lean_dec(v___y_6851_);
v___x_6863_ = l_Lean_FileMap_toPosition(v_fileMap_6855_, v___y_6853_);
lean_dec(v___y_6853_);
v___x_6864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6864_, 0, v___x_6863_);
v___x_6865_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6849_ == 0)
{
lean_del_object(v___x_6860_);
lean_dec_ref(v___y_6847_);
v___y_6811_ = v_fileName_6854_;
v___y_6812_ = v___x_6862_;
v___y_6813_ = v___y_6848_;
v___y_6814_ = v___x_6864_;
v___y_6815_ = v_a_6858_;
v___y_6816_ = v___x_6865_;
v___y_6817_ = v___y_6852_;
v___y_6818_ = v___y_6807_;
v___y_6819_ = v___y_6808_;
goto v___jp_6810_;
}
else
{
uint8_t v___x_6866_; 
lean_inc(v_a_6858_);
v___x_6866_ = l_Lean_MessageData_hasTag(v___y_6847_, v_a_6858_);
if (v___x_6866_ == 0)
{
lean_object* v___x_6867_; lean_object* v___x_6869_; 
lean_dec_ref_known(v___x_6864_, 1);
lean_dec_ref(v___x_6862_);
lean_dec(v_a_6858_);
v___x_6867_ = lean_box(0);
if (v_isShared_6861_ == 0)
{
lean_ctor_set(v___x_6860_, 0, v___x_6867_);
v___x_6869_ = v___x_6860_;
goto v_reusejp_6868_;
}
else
{
lean_object* v_reuseFailAlloc_6870_; 
v_reuseFailAlloc_6870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6870_, 0, v___x_6867_);
v___x_6869_ = v_reuseFailAlloc_6870_;
goto v_reusejp_6868_;
}
v_reusejp_6868_:
{
return v___x_6869_;
}
}
else
{
lean_del_object(v___x_6860_);
v___y_6811_ = v_fileName_6854_;
v___y_6812_ = v___x_6862_;
v___y_6813_ = v___y_6848_;
v___y_6814_ = v___x_6864_;
v___y_6815_ = v_a_6858_;
v___y_6816_ = v___x_6865_;
v___y_6817_ = v___y_6852_;
v___y_6818_ = v___y_6807_;
v___y_6819_ = v___y_6808_;
goto v___jp_6810_;
}
}
}
}
v___jp_6872_:
{
lean_object* v___x_6880_; 
v___x_6880_ = l_Lean_Syntax_getTailPos_x3f(v___y_6877_, v___y_6874_);
lean_dec(v___y_6877_);
if (lean_obj_tag(v___x_6880_) == 0)
{
lean_inc(v___y_6879_);
v___y_6847_ = v___y_6873_;
v___y_6848_ = v___y_6874_;
v___y_6849_ = v___y_6876_;
v___y_6850_ = v___y_6875_;
v___y_6851_ = v___y_6879_;
v___y_6852_ = v___y_6878_;
v___y_6853_ = v___y_6879_;
goto v___jp_6846_;
}
else
{
lean_object* v_val_6881_; 
v_val_6881_ = lean_ctor_get(v___x_6880_, 0);
lean_inc(v_val_6881_);
lean_dec_ref_known(v___x_6880_, 1);
v___y_6847_ = v___y_6873_;
v___y_6848_ = v___y_6874_;
v___y_6849_ = v___y_6876_;
v___y_6850_ = v___y_6875_;
v___y_6851_ = v___y_6879_;
v___y_6852_ = v___y_6878_;
v___y_6853_ = v_val_6881_;
goto v___jp_6846_;
}
}
v___jp_6882_:
{
lean_object* v_ref_6889_; lean_object* v___x_6890_; 
v_ref_6889_ = l_Lean_replaceRef(v_ref_6803_, v___y_6887_);
v___x_6890_ = l_Lean_Syntax_getPos_x3f(v_ref_6889_, v___y_6884_);
if (lean_obj_tag(v___x_6890_) == 0)
{
lean_object* v___x_6891_; 
v___x_6891_ = lean_unsigned_to_nat(0u);
v___y_6873_ = v___y_6883_;
v___y_6874_ = v___y_6884_;
v___y_6875_ = v___y_6886_;
v___y_6876_ = v___y_6885_;
v___y_6877_ = v_ref_6889_;
v___y_6878_ = v___y_6888_;
v___y_6879_ = v___x_6891_;
goto v___jp_6872_;
}
else
{
lean_object* v_val_6892_; 
v_val_6892_ = lean_ctor_get(v___x_6890_, 0);
lean_inc(v_val_6892_);
lean_dec_ref_known(v___x_6890_, 1);
v___y_6873_ = v___y_6883_;
v___y_6874_ = v___y_6884_;
v___y_6875_ = v___y_6886_;
v___y_6876_ = v___y_6885_;
v___y_6877_ = v_ref_6889_;
v___y_6878_ = v___y_6888_;
v___y_6879_ = v_val_6892_;
goto v___jp_6872_;
}
}
v___jp_6894_:
{
if (v___y_6900_ == 0)
{
v___y_6883_ = v___y_6895_;
v___y_6884_ = v___y_6899_;
v___y_6885_ = v___y_6897_;
v___y_6886_ = v___y_6896_;
v___y_6887_ = v___y_6898_;
v___y_6888_ = v_severity_6805_;
goto v___jp_6882_;
}
else
{
v___y_6883_ = v___y_6895_;
v___y_6884_ = v___y_6899_;
v___y_6885_ = v___y_6897_;
v___y_6886_ = v___y_6896_;
v___y_6887_ = v___y_6898_;
v___y_6888_ = v___x_6893_;
goto v___jp_6882_;
}
}
v___jp_6901_:
{
if (v___y_6902_ == 0)
{
lean_object* v_toCold_6903_; lean_object* v_options_6904_; lean_object* v_ref_6905_; uint8_t v_suppressElabErrors_6906_; lean_object* v___x_6907_; lean_object* v___x_6908_; lean_object* v___f_6909_; uint8_t v___x_6910_; uint8_t v___x_6911_; 
v_toCold_6903_ = lean_ctor_get(v___y_6807_, 0);
v_options_6904_ = lean_ctor_get(v___y_6807_, 1);
v_ref_6905_ = lean_ctor_get(v___y_6807_, 4);
v_suppressElabErrors_6906_ = lean_ctor_get_uint8(v___y_6807_, sizeof(void*)*10 + 1);
v___x_6907_ = lean_box(v_suppressElabErrors_6906_);
v___x_6908_ = lean_box(v___y_6902_);
v___f_6909_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6909_, 0, v___x_6907_);
lean_closure_set(v___f_6909_, 1, v___x_6908_);
v___x_6910_ = 1;
v___x_6911_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6805_, v___x_6910_);
if (v___x_6911_ == 0)
{
v___y_6895_ = v___f_6909_;
v___y_6896_ = v_toCold_6903_;
v___y_6897_ = v_suppressElabErrors_6906_;
v___y_6898_ = v_ref_6905_;
v___y_6899_ = v___y_6902_;
v___y_6900_ = v___x_6911_;
goto v___jp_6894_;
}
else
{
lean_object* v___x_6912_; uint8_t v___x_6913_; 
v___x_6912_ = l_Lean_warningAsError;
v___x_6913_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6904_, v___x_6912_);
v___y_6895_ = v___f_6909_;
v___y_6896_ = v_toCold_6903_;
v___y_6897_ = v_suppressElabErrors_6906_;
v___y_6898_ = v_ref_6905_;
v___y_6899_ = v___y_6902_;
v___y_6900_ = v___x_6913_;
goto v___jp_6894_;
}
}
else
{
lean_object* v___x_6914_; lean_object* v___x_6915_; 
lean_dec_ref(v_msgData_6804_);
v___x_6914_ = lean_box(0);
v___x_6915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6915_, 0, v___x_6914_);
return v___x_6915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_6918_, lean_object* v_msgData_6919_, lean_object* v_severity_6920_, lean_object* v_isSilent_6921_, lean_object* v___y_6922_, lean_object* v___y_6923_, lean_object* v___y_6924_){
_start:
{
uint8_t v_severity_boxed_6925_; uint8_t v_isSilent_boxed_6926_; lean_object* v_res_6927_; 
v_severity_boxed_6925_ = lean_unbox(v_severity_6920_);
v_isSilent_boxed_6926_ = lean_unbox(v_isSilent_6921_);
v_res_6927_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6918_, v_msgData_6919_, v_severity_boxed_6925_, v_isSilent_boxed_6926_, v___y_6922_, v___y_6923_);
lean_dec(v___y_6923_);
lean_dec_ref(v___y_6922_);
lean_dec(v_ref_6918_);
return v_res_6927_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_6928_, uint8_t v_severity_6929_, uint8_t v_isSilent_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_){
_start:
{
lean_object* v_ref_6934_; lean_object* v___x_6935_; 
v_ref_6934_ = lean_ctor_get(v___y_6931_, 4);
v___x_6935_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_6934_, v_msgData_6928_, v_severity_6929_, v_isSilent_6930_, v___y_6931_, v___y_6932_);
return v___x_6935_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6936_, lean_object* v_severity_6937_, lean_object* v_isSilent_6938_, lean_object* v___y_6939_, lean_object* v___y_6940_, lean_object* v___y_6941_){
_start:
{
uint8_t v_severity_boxed_6942_; uint8_t v_isSilent_boxed_6943_; lean_object* v_res_6944_; 
v_severity_boxed_6942_ = lean_unbox(v_severity_6937_);
v_isSilent_boxed_6943_ = lean_unbox(v_isSilent_6938_);
v_res_6944_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6936_, v_severity_boxed_6942_, v_isSilent_boxed_6943_, v___y_6939_, v___y_6940_);
lean_dec(v___y_6940_);
lean_dec_ref(v___y_6939_);
return v_res_6944_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_6945_, lean_object* v___y_6946_, lean_object* v___y_6947_){
_start:
{
uint8_t v___x_6949_; uint8_t v___x_6950_; lean_object* v___x_6951_; 
v___x_6949_ = 2;
v___x_6950_ = 0;
v___x_6951_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_6945_, v___x_6949_, v___x_6950_, v___y_6946_, v___y_6947_);
return v___x_6951_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_){
_start:
{
lean_object* v_res_6956_; 
v_res_6956_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_6952_, v___y_6953_, v___y_6954_);
lean_dec(v___y_6954_);
lean_dec_ref(v___y_6953_);
return v_res_6956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_6957_, lean_object* v___y_6958_, lean_object* v___y_6959_){
_start:
{
lean_object* v_module_6961_; lean_object* v_const_6962_; lean_object* v_exception_6963_; lean_object* v___x_6964_; lean_object* v___x_6965_; lean_object* v___x_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; lean_object* v___x_6975_; 
v_module_6961_ = lean_ctor_get(v_f_6957_, 0);
lean_inc(v_module_6961_);
v_const_6962_ = lean_ctor_get(v_f_6957_, 1);
lean_inc(v_const_6962_);
v_exception_6963_ = lean_ctor_get(v_f_6957_, 2);
lean_inc_ref(v_exception_6963_);
lean_dec_ref(v_f_6957_);
v___x_6964_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6965_ = l_Lean_MessageData_ofName(v_const_6962_);
v___x_6966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6966_, 0, v___x_6964_);
lean_ctor_set(v___x_6966_, 1, v___x_6965_);
v___x_6967_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6968_, 0, v___x_6966_);
lean_ctor_set(v___x_6968_, 1, v___x_6967_);
v___x_6969_ = l_Lean_MessageData_ofName(v_module_6961_);
v___x_6970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6970_, 0, v___x_6968_);
lean_ctor_set(v___x_6970_, 1, v___x_6969_);
v___x_6971_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6972_, 0, v___x_6970_);
lean_ctor_set(v___x_6972_, 1, v___x_6971_);
v___x_6973_ = l_Lean_Exception_toMessageData(v_exception_6963_);
v___x_6974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6974_, 0, v___x_6972_);
lean_ctor_set(v___x_6974_, 1, v___x_6973_);
v___x_6975_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_6974_, v___y_6958_, v___y_6959_);
return v___x_6975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_6976_, lean_object* v___y_6977_, lean_object* v___y_6978_, lean_object* v___y_6979_){
_start:
{
lean_object* v_res_6980_; 
v_res_6980_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_6976_, v___y_6977_, v___y_6978_);
lean_dec(v___y_6978_);
lean_dec_ref(v___y_6977_);
return v_res_6980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_6981_, size_t v_i_6982_, size_t v_stop_6983_, lean_object* v_b_6984_, lean_object* v___y_6985_, lean_object* v___y_6986_){
_start:
{
uint8_t v___x_6988_; 
v___x_6988_ = lean_usize_dec_eq(v_i_6982_, v_stop_6983_);
if (v___x_6988_ == 0)
{
lean_object* v___x_6989_; lean_object* v___x_6990_; 
v___x_6989_ = lean_array_uget_borrowed(v_as_6981_, v_i_6982_);
lean_inc(v___x_6989_);
v___x_6990_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_6989_, v___y_6985_, v___y_6986_);
if (lean_obj_tag(v___x_6990_) == 0)
{
lean_object* v_a_6991_; size_t v___x_6992_; size_t v___x_6993_; 
v_a_6991_ = lean_ctor_get(v___x_6990_, 0);
lean_inc(v_a_6991_);
lean_dec_ref_known(v___x_6990_, 1);
v___x_6992_ = ((size_t)1ULL);
v___x_6993_ = lean_usize_add(v_i_6982_, v___x_6992_);
v_i_6982_ = v___x_6993_;
v_b_6984_ = v_a_6991_;
goto _start;
}
else
{
return v___x_6990_;
}
}
else
{
lean_object* v___x_6995_; 
v___x_6995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6995_, 0, v_b_6984_);
return v___x_6995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_6996_, lean_object* v_i_6997_, lean_object* v_stop_6998_, lean_object* v_b_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_){
_start:
{
size_t v_i_boxed_7003_; size_t v_stop_boxed_7004_; lean_object* v_res_7005_; 
v_i_boxed_7003_ = lean_unbox_usize(v_i_6997_);
lean_dec(v_i_6997_);
v_stop_boxed_7004_ = lean_unbox_usize(v_stop_6998_);
lean_dec(v_stop_6998_);
v_res_7005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_6996_, v_i_boxed_7003_, v_stop_boxed_7004_, v_b_6999_, v___y_7000_, v___y_7001_);
lean_dec(v___y_7001_);
lean_dec_ref(v___y_7000_);
lean_dec_ref(v_as_6996_);
return v_res_7005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7006_, lean_object* v_a_7007_, lean_object* v_a_7008_){
_start:
{
lean_object* v___x_7010_; lean_object* v___x_7011_; lean_object* v_a_7012_; lean_object* v___x_7014_; uint8_t v_isShared_7015_; uint8_t v_isSharedCheck_7046_; 
v___x_7010_ = lean_st_ref_get(v_a_7008_);
v___x_7011_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7008_);
v_a_7012_ = lean_ctor_get(v___x_7011_, 0);
v_isSharedCheck_7046_ = !lean_is_exclusive(v___x_7011_);
if (v_isSharedCheck_7046_ == 0)
{
v___x_7014_ = v___x_7011_;
v_isShared_7015_ = v_isSharedCheck_7046_;
goto v_resetjp_7013_;
}
else
{
lean_inc(v_a_7012_);
lean_dec(v___x_7011_);
v___x_7014_ = lean_box(0);
v_isShared_7015_ = v_isSharedCheck_7046_;
goto v_resetjp_7013_;
}
v_resetjp_7013_:
{
lean_object* v___x_7016_; lean_object* v_env_7017_; lean_object* v___x_7018_; lean_object* v___y_7025_; lean_object* v___x_7034_; lean_object* v___x_7035_; lean_object* v___x_7036_; uint8_t v___x_7037_; 
v___x_7016_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_7017_ = lean_ctor_get(v___x_7010_, 0);
lean_inc_ref(v_env_7017_);
lean_dec(v___x_7010_);
lean_inc_ref(v_a_7007_);
v___x_7018_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7007_, v_a_7012_, v_env_7017_, v___x_7016_, v_entriesForConst_7006_);
v___x_7034_ = lean_st_ref_get(v___x_7016_);
lean_dec(v___x_7016_);
v___x_7035_ = lean_unsigned_to_nat(0u);
v___x_7036_ = lean_array_get_size(v___x_7034_);
v___x_7037_ = lean_nat_dec_lt(v___x_7035_, v___x_7036_);
if (v___x_7037_ == 0)
{
lean_dec(v___x_7034_);
goto v___jp_7019_;
}
else
{
lean_object* v___x_7038_; uint8_t v___x_7039_; 
v___x_7038_ = lean_box(0);
v___x_7039_ = lean_nat_dec_le(v___x_7036_, v___x_7036_);
if (v___x_7039_ == 0)
{
if (v___x_7037_ == 0)
{
lean_dec(v___x_7034_);
goto v___jp_7019_;
}
else
{
size_t v___x_7040_; size_t v___x_7041_; lean_object* v___x_7042_; 
v___x_7040_ = ((size_t)0ULL);
v___x_7041_ = lean_usize_of_nat(v___x_7036_);
v___x_7042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7034_, v___x_7040_, v___x_7041_, v___x_7038_, v_a_7007_, v_a_7008_);
lean_dec(v___x_7034_);
v___y_7025_ = v___x_7042_;
goto v___jp_7024_;
}
}
else
{
size_t v___x_7043_; size_t v___x_7044_; lean_object* v___x_7045_; 
v___x_7043_ = ((size_t)0ULL);
v___x_7044_ = lean_usize_of_nat(v___x_7036_);
v___x_7045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7034_, v___x_7043_, v___x_7044_, v___x_7038_, v_a_7007_, v_a_7008_);
lean_dec(v___x_7034_);
v___y_7025_ = v___x_7045_;
goto v___jp_7024_;
}
}
v___jp_7019_:
{
lean_object* v___x_7020_; lean_object* v___x_7022_; 
v___x_7020_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7018_);
if (v_isShared_7015_ == 0)
{
lean_ctor_set(v___x_7014_, 0, v___x_7020_);
v___x_7022_ = v___x_7014_;
goto v_reusejp_7021_;
}
else
{
lean_object* v_reuseFailAlloc_7023_; 
v_reuseFailAlloc_7023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7023_, 0, v___x_7020_);
v___x_7022_ = v_reuseFailAlloc_7023_;
goto v_reusejp_7021_;
}
v_reusejp_7021_:
{
return v___x_7022_;
}
}
v___jp_7024_:
{
if (lean_obj_tag(v___y_7025_) == 0)
{
lean_dec_ref_known(v___y_7025_, 1);
goto v___jp_7019_;
}
else
{
lean_object* v_a_7026_; lean_object* v___x_7028_; uint8_t v_isShared_7029_; uint8_t v_isSharedCheck_7033_; 
lean_dec_ref(v___x_7018_);
lean_del_object(v___x_7014_);
v_a_7026_ = lean_ctor_get(v___y_7025_, 0);
v_isSharedCheck_7033_ = !lean_is_exclusive(v___y_7025_);
if (v_isSharedCheck_7033_ == 0)
{
v___x_7028_ = v___y_7025_;
v_isShared_7029_ = v_isSharedCheck_7033_;
goto v_resetjp_7027_;
}
else
{
lean_inc(v_a_7026_);
lean_dec(v___y_7025_);
v___x_7028_ = lean_box(0);
v_isShared_7029_ = v_isSharedCheck_7033_;
goto v_resetjp_7027_;
}
v_resetjp_7027_:
{
lean_object* v___x_7031_; 
if (v_isShared_7029_ == 0)
{
v___x_7031_ = v___x_7028_;
goto v_reusejp_7030_;
}
else
{
lean_object* v_reuseFailAlloc_7032_; 
v_reuseFailAlloc_7032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7032_, 0, v_a_7026_);
v___x_7031_ = v_reuseFailAlloc_7032_;
goto v_reusejp_7030_;
}
v_reusejp_7030_:
{
return v___x_7031_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7047_, lean_object* v_a_7048_, lean_object* v_a_7049_, lean_object* v_a_7050_){
_start:
{
lean_object* v_res_7051_; 
v_res_7051_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7047_, v_a_7048_, v_a_7049_);
lean_dec(v_a_7049_);
lean_dec_ref(v_a_7048_);
return v_res_7051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7052_, lean_object* v_entriesForConst_7053_, lean_object* v_a_7054_, lean_object* v_a_7055_){
_start:
{
lean_object* v___x_7057_; 
v___x_7057_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7053_, v_a_7054_, v_a_7055_);
return v___x_7057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7058_, lean_object* v_entriesForConst_7059_, lean_object* v_a_7060_, lean_object* v_a_7061_, lean_object* v_a_7062_){
_start:
{
lean_object* v_res_7063_; 
v_res_7063_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7058_, v_entriesForConst_7059_, v_a_7060_, v_a_7061_);
lean_dec(v_a_7061_);
lean_dec_ref(v_a_7060_);
return v_res_7063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7064_, lean_object* v_droppedEntriesRef_7065_, lean_object* v_droppedKeys_7066_, lean_object* v___y_7067_, lean_object* v___y_7068_, lean_object* v___y_7069_, lean_object* v___y_7070_){
_start:
{
lean_object* v_t_7073_; lean_object* v___x_7076_; 
v___x_7076_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7064_, v___y_7069_, v___y_7070_);
if (lean_obj_tag(v___x_7076_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7065_) == 1)
{
lean_object* v_a_7077_; lean_object* v_val_7078_; lean_object* v___x_7080_; uint8_t v_isShared_7081_; uint8_t v_isSharedCheck_7104_; 
v_a_7077_ = lean_ctor_get(v___x_7076_, 0);
lean_inc(v_a_7077_);
lean_dec_ref_known(v___x_7076_, 1);
v_val_7078_ = lean_ctor_get(v_droppedEntriesRef_7065_, 0);
v_isSharedCheck_7104_ = !lean_is_exclusive(v_droppedEntriesRef_7065_);
if (v_isSharedCheck_7104_ == 0)
{
v___x_7080_ = v_droppedEntriesRef_7065_;
v_isShared_7081_ = v_isSharedCheck_7104_;
goto v_resetjp_7079_;
}
else
{
lean_inc(v_val_7078_);
lean_dec(v_droppedEntriesRef_7065_);
v___x_7080_ = lean_box(0);
v_isShared_7081_ = v_isSharedCheck_7104_;
goto v_resetjp_7079_;
}
v_resetjp_7079_:
{
lean_object* v___x_7082_; 
v___x_7082_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7077_, v_droppedKeys_7066_, v___y_7067_, v___y_7068_, v___y_7069_, v___y_7070_);
lean_dec(v_droppedKeys_7066_);
if (lean_obj_tag(v___x_7082_) == 0)
{
lean_object* v_a_7083_; lean_object* v_fst_7084_; lean_object* v_snd_7085_; lean_object* v___x_7086_; lean_object* v___y_7088_; 
v_a_7083_ = lean_ctor_get(v___x_7082_, 0);
lean_inc(v_a_7083_);
lean_dec_ref_known(v___x_7082_, 1);
v_fst_7084_ = lean_ctor_get(v_a_7083_, 0);
lean_inc(v_fst_7084_);
v_snd_7085_ = lean_ctor_get(v_a_7083_, 1);
lean_inc(v_snd_7085_);
lean_dec(v_a_7083_);
v___x_7086_ = lean_st_ref_get(v_val_7078_);
if (lean_obj_tag(v___x_7086_) == 0)
{
lean_object* v___x_7094_; 
v___x_7094_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7088_ = v___x_7094_;
goto v___jp_7087_;
}
else
{
lean_object* v_val_7095_; 
v_val_7095_ = lean_ctor_get(v___x_7086_, 0);
lean_inc(v_val_7095_);
lean_dec_ref_known(v___x_7086_, 1);
v___y_7088_ = v_val_7095_;
goto v___jp_7087_;
}
v___jp_7087_:
{
lean_object* v___x_7089_; lean_object* v___x_7091_; 
v___x_7089_ = l_Array_append___redArg(v___y_7088_, v_fst_7084_);
lean_dec(v_fst_7084_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 0, v___x_7089_);
v___x_7091_ = v___x_7080_;
goto v_reusejp_7090_;
}
else
{
lean_object* v_reuseFailAlloc_7093_; 
v_reuseFailAlloc_7093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7093_, 0, v___x_7089_);
v___x_7091_ = v_reuseFailAlloc_7093_;
goto v_reusejp_7090_;
}
v_reusejp_7090_:
{
lean_object* v___x_7092_; 
v___x_7092_ = lean_st_ref_swap(v_val_7078_, v___x_7091_);
lean_dec(v_val_7078_);
lean_dec(v___x_7092_);
v_t_7073_ = v_snd_7085_;
goto v___jp_7072_;
}
}
}
else
{
lean_object* v_a_7096_; lean_object* v___x_7098_; uint8_t v_isShared_7099_; uint8_t v_isSharedCheck_7103_; 
lean_del_object(v___x_7080_);
lean_dec(v_val_7078_);
v_a_7096_ = lean_ctor_get(v___x_7082_, 0);
v_isSharedCheck_7103_ = !lean_is_exclusive(v___x_7082_);
if (v_isSharedCheck_7103_ == 0)
{
v___x_7098_ = v___x_7082_;
v_isShared_7099_ = v_isSharedCheck_7103_;
goto v_resetjp_7097_;
}
else
{
lean_inc(v_a_7096_);
lean_dec(v___x_7082_);
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
}
}
else
{
lean_object* v_a_7105_; lean_object* v___x_7106_; 
lean_dec(v_droppedEntriesRef_7065_);
v_a_7105_ = lean_ctor_get(v___x_7076_, 0);
lean_inc(v_a_7105_);
lean_dec_ref_known(v___x_7076_, 1);
v___x_7106_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7105_, v_droppedKeys_7066_, v___y_7067_, v___y_7068_, v___y_7069_, v___y_7070_);
if (lean_obj_tag(v___x_7106_) == 0)
{
lean_object* v_a_7107_; 
v_a_7107_ = lean_ctor_get(v___x_7106_, 0);
lean_inc(v_a_7107_);
lean_dec_ref_known(v___x_7106_, 1);
v_t_7073_ = v_a_7107_;
goto v___jp_7072_;
}
else
{
lean_object* v_a_7108_; lean_object* v___x_7110_; uint8_t v_isShared_7111_; uint8_t v_isSharedCheck_7115_; 
v_a_7108_ = lean_ctor_get(v___x_7106_, 0);
v_isSharedCheck_7115_ = !lean_is_exclusive(v___x_7106_);
if (v_isSharedCheck_7115_ == 0)
{
v___x_7110_ = v___x_7106_;
v_isShared_7111_ = v_isSharedCheck_7115_;
goto v_resetjp_7109_;
}
else
{
lean_inc(v_a_7108_);
lean_dec(v___x_7106_);
v___x_7110_ = lean_box(0);
v_isShared_7111_ = v_isSharedCheck_7115_;
goto v_resetjp_7109_;
}
v_resetjp_7109_:
{
lean_object* v___x_7113_; 
if (v_isShared_7111_ == 0)
{
v___x_7113_ = v___x_7110_;
goto v_reusejp_7112_;
}
else
{
lean_object* v_reuseFailAlloc_7114_; 
v_reuseFailAlloc_7114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7114_, 0, v_a_7108_);
v___x_7113_ = v_reuseFailAlloc_7114_;
goto v_reusejp_7112_;
}
v_reusejp_7112_:
{
return v___x_7113_;
}
}
}
}
}
else
{
lean_object* v_a_7116_; lean_object* v___x_7118_; uint8_t v_isShared_7119_; uint8_t v_isSharedCheck_7123_; 
lean_dec(v_droppedKeys_7066_);
lean_dec(v_droppedEntriesRef_7065_);
v_a_7116_ = lean_ctor_get(v___x_7076_, 0);
v_isSharedCheck_7123_ = !lean_is_exclusive(v___x_7076_);
if (v_isSharedCheck_7123_ == 0)
{
v___x_7118_ = v___x_7076_;
v_isShared_7119_ = v_isSharedCheck_7123_;
goto v_resetjp_7117_;
}
else
{
lean_inc(v_a_7116_);
lean_dec(v___x_7076_);
v___x_7118_ = lean_box(0);
v_isShared_7119_ = v_isSharedCheck_7123_;
goto v_resetjp_7117_;
}
v_resetjp_7117_:
{
lean_object* v___x_7121_; 
if (v_isShared_7119_ == 0)
{
v___x_7121_ = v___x_7118_;
goto v_reusejp_7120_;
}
else
{
lean_object* v_reuseFailAlloc_7122_; 
v_reuseFailAlloc_7122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7122_, 0, v_a_7116_);
v___x_7121_ = v_reuseFailAlloc_7122_;
goto v_reusejp_7120_;
}
v_reusejp_7120_:
{
return v___x_7121_;
}
}
}
v___jp_7072_:
{
lean_object* v___x_7074_; lean_object* v___x_7075_; 
v___x_7074_ = lean_st_mk_ref(v_t_7073_);
v___x_7075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7075_, 0, v___x_7074_);
return v___x_7075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7124_, lean_object* v_droppedEntriesRef_7125_, lean_object* v_droppedKeys_7126_, lean_object* v___y_7127_, lean_object* v___y_7128_, lean_object* v___y_7129_, lean_object* v___y_7130_, lean_object* v___y_7131_){
_start:
{
lean_object* v_res_7132_; 
v_res_7132_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7124_, v_droppedEntriesRef_7125_, v_droppedKeys_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_);
lean_dec(v___y_7130_);
lean_dec_ref(v___y_7129_);
lean_dec(v___y_7128_);
lean_dec_ref(v___y_7127_);
return v_res_7132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7134_, lean_object* v_droppedKeys_7135_, lean_object* v_droppedEntriesRef_7136_, lean_object* v_a_7137_, lean_object* v_a_7138_, lean_object* v_a_7139_, lean_object* v_a_7140_){
_start:
{
lean_object* v_options_7142_; lean_object* v___f_7143_; lean_object* v___x_7144_; lean_object* v___x_7145_; lean_object* v___x_7146_; 
v_options_7142_ = lean_ctor_get(v_a_7139_, 1);
v___f_7143_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7143_, 0, v_entriesForConst_7134_);
lean_closure_set(v___f_7143_, 1, v_droppedEntriesRef_7136_);
lean_closure_set(v___f_7143_, 2, v_droppedKeys_7135_);
v___x_7144_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7145_ = lean_box(0);
v___x_7146_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7144_, v_options_7142_, v___f_7143_, v___x_7145_, v_a_7137_, v_a_7138_, v_a_7139_, v_a_7140_);
return v___x_7146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7147_, lean_object* v_droppedKeys_7148_, lean_object* v_droppedEntriesRef_7149_, lean_object* v_a_7150_, lean_object* v_a_7151_, lean_object* v_a_7152_, lean_object* v_a_7153_, lean_object* v_a_7154_){
_start:
{
lean_object* v_res_7155_; 
v_res_7155_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7147_, v_droppedKeys_7148_, v_droppedEntriesRef_7149_, v_a_7150_, v_a_7151_, v_a_7152_, v_a_7153_);
lean_dec(v_a_7153_);
lean_dec_ref(v_a_7152_);
lean_dec(v_a_7151_);
lean_dec_ref(v_a_7150_);
return v_res_7155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7156_, lean_object* v_entriesForConst_7157_, lean_object* v_droppedKeys_7158_, lean_object* v_droppedEntriesRef_7159_, lean_object* v_a_7160_, lean_object* v_a_7161_, lean_object* v_a_7162_, lean_object* v_a_7163_){
_start:
{
lean_object* v___x_7165_; 
v___x_7165_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7157_, v_droppedKeys_7158_, v_droppedEntriesRef_7159_, v_a_7160_, v_a_7161_, v_a_7162_, v_a_7163_);
return v___x_7165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7166_, lean_object* v_entriesForConst_7167_, lean_object* v_droppedKeys_7168_, lean_object* v_droppedEntriesRef_7169_, lean_object* v_a_7170_, lean_object* v_a_7171_, lean_object* v_a_7172_, lean_object* v_a_7173_, lean_object* v_a_7174_){
_start:
{
lean_object* v_res_7175_; 
v_res_7175_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7166_, v_entriesForConst_7167_, v_droppedKeys_7168_, v_droppedEntriesRef_7169_, v_a_7170_, v_a_7171_, v_a_7172_, v_a_7173_);
lean_dec(v_a_7173_);
lean_dec_ref(v_a_7172_);
lean_dec(v_a_7171_);
lean_dec_ref(v_a_7170_);
return v_res_7175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7176_, lean_object* v_ty_7177_, lean_object* v___y_7178_, lean_object* v___y_7179_, lean_object* v___y_7180_, lean_object* v___y_7181_){
_start:
{
lean_object* v___x_7183_; lean_object* v___x_7184_; 
v___x_7183_ = lean_st_ref_get(v_moduleRef_7176_);
v___x_7184_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7183_, v_ty_7177_, v___y_7178_, v___y_7179_, v___y_7180_, v___y_7181_);
if (lean_obj_tag(v___x_7184_) == 0)
{
lean_object* v_a_7185_; lean_object* v___x_7187_; uint8_t v_isShared_7188_; uint8_t v_isSharedCheck_7195_; 
v_a_7185_ = lean_ctor_get(v___x_7184_, 0);
v_isSharedCheck_7195_ = !lean_is_exclusive(v___x_7184_);
if (v_isSharedCheck_7195_ == 0)
{
v___x_7187_ = v___x_7184_;
v_isShared_7188_ = v_isSharedCheck_7195_;
goto v_resetjp_7186_;
}
else
{
lean_inc(v_a_7185_);
lean_dec(v___x_7184_);
v___x_7187_ = lean_box(0);
v_isShared_7188_ = v_isSharedCheck_7195_;
goto v_resetjp_7186_;
}
v_resetjp_7186_:
{
lean_object* v_fst_7189_; lean_object* v_snd_7190_; lean_object* v___x_7191_; lean_object* v___x_7193_; 
v_fst_7189_ = lean_ctor_get(v_a_7185_, 0);
lean_inc(v_fst_7189_);
v_snd_7190_ = lean_ctor_get(v_a_7185_, 1);
lean_inc(v_snd_7190_);
lean_dec(v_a_7185_);
v___x_7191_ = lean_st_ref_swap(v_moduleRef_7176_, v_snd_7190_);
lean_dec(v___x_7191_);
if (v_isShared_7188_ == 0)
{
lean_ctor_set(v___x_7187_, 0, v_fst_7189_);
v___x_7193_ = v___x_7187_;
goto v_reusejp_7192_;
}
else
{
lean_object* v_reuseFailAlloc_7194_; 
v_reuseFailAlloc_7194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7194_, 0, v_fst_7189_);
v___x_7193_ = v_reuseFailAlloc_7194_;
goto v_reusejp_7192_;
}
v_reusejp_7192_:
{
return v___x_7193_;
}
}
}
else
{
lean_object* v_a_7196_; lean_object* v___x_7198_; uint8_t v_isShared_7199_; uint8_t v_isSharedCheck_7203_; 
v_a_7196_ = lean_ctor_get(v___x_7184_, 0);
v_isSharedCheck_7203_ = !lean_is_exclusive(v___x_7184_);
if (v_isSharedCheck_7203_ == 0)
{
v___x_7198_ = v___x_7184_;
v_isShared_7199_ = v_isSharedCheck_7203_;
goto v_resetjp_7197_;
}
else
{
lean_inc(v_a_7196_);
lean_dec(v___x_7184_);
v___x_7198_ = lean_box(0);
v_isShared_7199_ = v_isSharedCheck_7203_;
goto v_resetjp_7197_;
}
v_resetjp_7197_:
{
lean_object* v___x_7201_; 
if (v_isShared_7199_ == 0)
{
v___x_7201_ = v___x_7198_;
goto v_reusejp_7200_;
}
else
{
lean_object* v_reuseFailAlloc_7202_; 
v_reuseFailAlloc_7202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7202_, 0, v_a_7196_);
v___x_7201_ = v_reuseFailAlloc_7202_;
goto v_reusejp_7200_;
}
v_reusejp_7200_:
{
return v___x_7201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7204_, lean_object* v_ty_7205_, lean_object* v___y_7206_, lean_object* v___y_7207_, lean_object* v___y_7208_, lean_object* v___y_7209_, lean_object* v___y_7210_){
_start:
{
lean_object* v_res_7211_; 
v_res_7211_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7204_, v_ty_7205_, v___y_7206_, v___y_7207_, v___y_7208_, v___y_7209_);
lean_dec(v___y_7209_);
lean_dec_ref(v___y_7208_);
lean_dec(v___y_7207_);
lean_dec_ref(v___y_7206_);
lean_dec(v_moduleRef_7204_);
return v_res_7211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7213_, lean_object* v_ty_7214_, lean_object* v_a_7215_, lean_object* v_a_7216_, lean_object* v_a_7217_, lean_object* v_a_7218_){
_start:
{
lean_object* v_options_7220_; lean_object* v___f_7221_; lean_object* v___x_7222_; lean_object* v___x_7223_; lean_object* v___x_7224_; 
v_options_7220_ = lean_ctor_get(v_a_7217_, 1);
v___f_7221_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7221_, 0, v_moduleRef_7213_);
lean_closure_set(v___f_7221_, 1, v_ty_7214_);
v___x_7222_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7223_ = lean_box(0);
v___x_7224_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7222_, v_options_7220_, v___f_7221_, v___x_7223_, v_a_7215_, v_a_7216_, v_a_7217_, v_a_7218_);
return v___x_7224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7225_, lean_object* v_ty_7226_, lean_object* v_a_7227_, lean_object* v_a_7228_, lean_object* v_a_7229_, lean_object* v_a_7230_, lean_object* v_a_7231_){
_start:
{
lean_object* v_res_7232_; 
v_res_7232_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7225_, v_ty_7226_, v_a_7227_, v_a_7228_, v_a_7229_, v_a_7230_);
lean_dec(v_a_7230_);
lean_dec_ref(v_a_7229_);
lean_dec(v_a_7228_);
lean_dec_ref(v_a_7227_);
return v_res_7232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7233_, lean_object* v_moduleRef_7234_, lean_object* v_ty_7235_, lean_object* v_a_7236_, lean_object* v_a_7237_, lean_object* v_a_7238_, lean_object* v_a_7239_){
_start:
{
lean_object* v___x_7241_; 
v___x_7241_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7234_, v_ty_7235_, v_a_7236_, v_a_7237_, v_a_7238_, v_a_7239_);
return v___x_7241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7242_, lean_object* v_moduleRef_7243_, lean_object* v_ty_7244_, lean_object* v_a_7245_, lean_object* v_a_7246_, lean_object* v_a_7247_, lean_object* v_a_7248_, lean_object* v_a_7249_){
_start:
{
lean_object* v_res_7250_; 
v_res_7250_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7242_, v_moduleRef_7243_, v_ty_7244_, v_a_7245_, v_a_7246_, v_a_7247_, v_a_7248_);
lean_dec(v_a_7248_);
lean_dec_ref(v_a_7247_);
lean_dec(v_a_7246_);
lean_dec_ref(v_a_7245_);
return v_res_7250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7251_, lean_object* v_j_7252_, size_t v_sz_7253_, size_t v_i_7254_, lean_object* v_bs_7255_){
_start:
{
uint8_t v___x_7256_; 
v___x_7256_ = lean_usize_dec_lt(v_i_7254_, v_sz_7253_);
if (v___x_7256_ == 0)
{
lean_dec(v_j_7252_);
lean_dec(v_adjustResult_7251_);
return v_bs_7255_;
}
else
{
lean_object* v_v_7257_; lean_object* v___x_7258_; lean_object* v_bs_x27_7259_; lean_object* v___x_7260_; size_t v___x_7261_; size_t v___x_7262_; lean_object* v___x_7263_; 
v_v_7257_ = lean_array_uget(v_bs_7255_, v_i_7254_);
v___x_7258_ = lean_unsigned_to_nat(0u);
v_bs_x27_7259_ = lean_array_uset(v_bs_7255_, v_i_7254_, v___x_7258_);
lean_inc(v_adjustResult_7251_);
lean_inc(v_j_7252_);
v___x_7260_ = lean_apply_2(v_adjustResult_7251_, v_j_7252_, v_v_7257_);
v___x_7261_ = ((size_t)1ULL);
v___x_7262_ = lean_usize_add(v_i_7254_, v___x_7261_);
v___x_7263_ = lean_array_uset(v_bs_x27_7259_, v_i_7254_, v___x_7260_);
v_i_7254_ = v___x_7262_;
v_bs_7255_ = v___x_7263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7265_, lean_object* v_j_7266_, lean_object* v_sz_7267_, lean_object* v_i_7268_, lean_object* v_bs_7269_){
_start:
{
size_t v_sz_boxed_7270_; size_t v_i_boxed_7271_; lean_object* v_res_7272_; 
v_sz_boxed_7270_ = lean_unbox_usize(v_sz_7267_);
lean_dec(v_sz_7267_);
v_i_boxed_7271_ = lean_unbox_usize(v_i_7268_);
lean_dec(v_i_7268_);
v_res_7272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7265_, v_j_7266_, v_sz_boxed_7270_, v_i_boxed_7271_, v_bs_7269_);
return v_res_7272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7273_, lean_object* v_j_7274_, lean_object* v_as_7275_, size_t v_i_7276_, size_t v_stop_7277_, lean_object* v_b_7278_){
_start:
{
uint8_t v___x_7279_; 
v___x_7279_ = lean_usize_dec_eq(v_i_7276_, v_stop_7277_);
if (v___x_7279_ == 0)
{
lean_object* v___x_7280_; size_t v_sz_7281_; size_t v___x_7282_; lean_object* v___x_7283_; lean_object* v___x_7284_; size_t v___x_7285_; size_t v___x_7286_; 
v___x_7280_ = lean_array_uget_borrowed(v_as_7275_, v_i_7276_);
v_sz_7281_ = lean_array_size(v___x_7280_);
v___x_7282_ = ((size_t)0ULL);
lean_inc(v___x_7280_);
lean_inc(v_j_7274_);
lean_inc(v_adjustResult_7273_);
v___x_7283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7273_, v_j_7274_, v_sz_7281_, v___x_7282_, v___x_7280_);
v___x_7284_ = l_Array_append___redArg(v_b_7278_, v___x_7283_);
lean_dec_ref(v___x_7283_);
v___x_7285_ = ((size_t)1ULL);
v___x_7286_ = lean_usize_add(v_i_7276_, v___x_7285_);
v_i_7276_ = v___x_7286_;
v_b_7278_ = v___x_7284_;
goto _start;
}
else
{
lean_dec(v_j_7274_);
lean_dec(v_adjustResult_7273_);
return v_b_7278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7288_, lean_object* v_j_7289_, lean_object* v_as_7290_, lean_object* v_i_7291_, lean_object* v_stop_7292_, lean_object* v_b_7293_){
_start:
{
size_t v_i_boxed_7294_; size_t v_stop_boxed_7295_; lean_object* v_res_7296_; 
v_i_boxed_7294_ = lean_unbox_usize(v_i_7291_);
lean_dec(v_i_7291_);
v_stop_boxed_7295_ = lean_unbox_usize(v_stop_7292_);
lean_dec(v_stop_7292_);
v_res_7296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7288_, v_j_7289_, v_as_7290_, v_i_boxed_7294_, v_stop_boxed_7295_, v_b_7293_);
lean_dec_ref(v_as_7290_);
return v_res_7296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7297_, lean_object* v_aa_7298_, lean_object* v_adjustResult_7299_, lean_object* v_n_7300_, lean_object* v_j_7301_, lean_object* v_a_7302_){
_start:
{
lean_object* v_zero_7303_; uint8_t v_isZero_7304_; 
v_zero_7303_ = lean_unsigned_to_nat(0u);
v_isZero_7304_ = lean_nat_dec_eq(v_j_7301_, v_zero_7303_);
if (v_isZero_7304_ == 1)
{
lean_dec(v_j_7301_);
lean_dec(v_adjustResult_7299_);
return v_a_7302_;
}
else
{
lean_object* v_one_7305_; lean_object* v_n_7306_; lean_object* v___x_7307_; lean_object* v___x_7308_; lean_object* v_j_7309_; lean_object* v_b_7310_; lean_object* v___x_7311_; uint8_t v___x_7312_; 
v_one_7305_ = lean_unsigned_to_nat(1u);
v_n_7306_ = lean_nat_sub(v_j_7301_, v_one_7305_);
v___x_7307_ = lean_nat_sub(v_n_7300_, v_j_7301_);
lean_dec(v_j_7301_);
v___x_7308_ = lean_nat_sub(v_n_7297_, v_one_7305_);
v_j_7309_ = lean_nat_sub(v___x_7308_, v___x_7307_);
lean_dec(v___x_7307_);
lean_dec(v___x_7308_);
v_b_7310_ = lean_array_fget_borrowed(v_aa_7298_, v_j_7309_);
v___x_7311_ = lean_array_get_size(v_b_7310_);
v___x_7312_ = lean_nat_dec_lt(v_zero_7303_, v___x_7311_);
if (v___x_7312_ == 0)
{
lean_dec(v_j_7309_);
v_j_7301_ = v_n_7306_;
goto _start;
}
else
{
size_t v___x_7314_; size_t v___x_7315_; lean_object* v___x_7316_; 
v___x_7314_ = ((size_t)0ULL);
v___x_7315_ = lean_usize_of_nat(v___x_7311_);
lean_inc(v_adjustResult_7299_);
v___x_7316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7299_, v_j_7309_, v_b_7310_, v___x_7314_, v___x_7315_, v_a_7302_);
v_j_7301_ = v_n_7306_;
v_a_7302_ = v___x_7316_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7318_, lean_object* v_aa_7319_, lean_object* v_adjustResult_7320_, lean_object* v_n_7321_, lean_object* v_j_7322_, lean_object* v_a_7323_){
_start:
{
lean_object* v_res_7324_; 
v_res_7324_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7318_, v_aa_7319_, v_adjustResult_7320_, v_n_7321_, v_j_7322_, v_a_7323_);
lean_dec(v_n_7321_);
lean_dec_ref(v_aa_7319_);
lean_dec(v_n_7318_);
return v_res_7324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7325_, lean_object* v_adjustResult_7326_, lean_object* v_aa_7327_, lean_object* v_n_7328_, lean_object* v_j_7329_, lean_object* v_a_7330_){
_start:
{
lean_object* v_zero_7331_; uint8_t v_isZero_7332_; 
v_zero_7331_ = lean_unsigned_to_nat(0u);
v_isZero_7332_ = lean_nat_dec_eq(v_j_7329_, v_zero_7331_);
if (v_isZero_7332_ == 1)
{
lean_dec(v_adjustResult_7326_);
return v_a_7330_;
}
else
{
lean_object* v_one_7333_; lean_object* v_n_7334_; lean_object* v___x_7335_; lean_object* v___x_7336_; lean_object* v_j_7337_; lean_object* v_b_7338_; lean_object* v___x_7339_; uint8_t v___x_7340_; 
v_one_7333_ = lean_unsigned_to_nat(1u);
v_n_7334_ = lean_nat_sub(v_j_7329_, v_one_7333_);
v___x_7335_ = lean_nat_sub(v_n_7328_, v_j_7329_);
v___x_7336_ = lean_nat_sub(v_n_7325_, v_one_7333_);
v_j_7337_ = lean_nat_sub(v___x_7336_, v___x_7335_);
lean_dec(v___x_7335_);
lean_dec(v___x_7336_);
v_b_7338_ = lean_array_fget_borrowed(v_aa_7327_, v_j_7337_);
v___x_7339_ = lean_array_get_size(v_b_7338_);
v___x_7340_ = lean_nat_dec_lt(v_zero_7331_, v___x_7339_);
if (v___x_7340_ == 0)
{
lean_object* v___x_7341_; 
lean_dec(v_j_7337_);
v___x_7341_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7325_, v_aa_7327_, v_adjustResult_7326_, v_n_7328_, v_n_7334_, v_a_7330_);
return v___x_7341_;
}
else
{
size_t v___x_7342_; size_t v___x_7343_; lean_object* v___x_7344_; lean_object* v___x_7345_; 
v___x_7342_ = ((size_t)0ULL);
v___x_7343_ = lean_usize_of_nat(v___x_7339_);
lean_inc(v_adjustResult_7326_);
v___x_7344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7326_, v_j_7337_, v_b_7338_, v___x_7342_, v___x_7343_, v_a_7330_);
v___x_7345_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7325_, v_aa_7327_, v_adjustResult_7326_, v_n_7328_, v_n_7334_, v___x_7344_);
return v___x_7345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7346_, lean_object* v_adjustResult_7347_, lean_object* v_aa_7348_, lean_object* v_n_7349_, lean_object* v_j_7350_, lean_object* v_a_7351_){
_start:
{
lean_object* v_res_7352_; 
v_res_7352_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7346_, v_adjustResult_7347_, v_aa_7348_, v_n_7349_, v_j_7350_, v_a_7351_);
lean_dec(v_j_7350_);
lean_dec(v_n_7349_);
lean_dec_ref(v_aa_7348_);
lean_dec(v_n_7346_);
return v_res_7352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7353_, lean_object* v_mr_7354_, lean_object* v_a_7355_){
_start:
{
lean_object* v_n_7356_; lean_object* v___x_7357_; 
v_n_7356_ = lean_array_get_size(v_mr_7354_);
v___x_7357_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7356_, v_adjustResult_7353_, v_mr_7354_, v_n_7356_, v_n_7356_, v_a_7355_);
return v___x_7357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7358_, lean_object* v_mr_7359_, lean_object* v_a_7360_){
_start:
{
lean_object* v_res_7361_; 
v_res_7361_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7358_, v_mr_7359_, v_a_7360_);
lean_dec_ref(v_mr_7359_);
return v_res_7361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7362_, lean_object* v_ref_7363_, lean_object* v_addEntry_7364_, lean_object* v_droppedKeys_7365_, lean_object* v_constantsPerTask_7366_, lean_object* v_droppedEntriesRef_7367_, lean_object* v_adjustResult_7368_, lean_object* v_ty_7369_, lean_object* v_a_7370_, lean_object* v_a_7371_, lean_object* v_a_7372_, lean_object* v_a_7373_){
_start:
{
lean_object* v___x_7375_; 
lean_inc_ref(v_ty_7369_);
v___x_7375_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7362_, v_ty_7369_, v_a_7370_, v_a_7371_, v_a_7372_, v_a_7373_);
if (lean_obj_tag(v___x_7375_) == 0)
{
lean_object* v_a_7376_; lean_object* v___x_7377_; 
v_a_7376_ = lean_ctor_get(v___x_7375_, 0);
lean_inc(v_a_7376_);
lean_dec_ref_known(v___x_7375_, 1);
v___x_7377_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ref_7363_, v_addEntry_7364_, v_droppedKeys_7365_, v_constantsPerTask_7366_, v_droppedEntriesRef_7367_, v_ty_7369_, v_a_7370_, v_a_7371_, v_a_7372_, v_a_7373_);
if (lean_obj_tag(v___x_7377_) == 0)
{
lean_object* v_a_7378_; lean_object* v___x_7380_; uint8_t v_isShared_7381_; uint8_t v_isSharedCheck_7391_; 
v_a_7378_ = lean_ctor_get(v___x_7377_, 0);
v_isSharedCheck_7391_ = !lean_is_exclusive(v___x_7377_);
if (v_isSharedCheck_7391_ == 0)
{
v___x_7380_ = v___x_7377_;
v_isShared_7381_ = v_isSharedCheck_7391_;
goto v_resetjp_7379_;
}
else
{
lean_inc(v_a_7378_);
lean_dec(v___x_7377_);
v___x_7380_ = lean_box(0);
v_isShared_7381_ = v_isSharedCheck_7391_;
goto v_resetjp_7379_;
}
v_resetjp_7379_:
{
lean_object* v___x_7382_; lean_object* v___x_7383_; lean_object* v___x_7384_; lean_object* v___x_7385_; lean_object* v___x_7386_; lean_object* v___x_7387_; lean_object* v___x_7389_; 
v___x_7382_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7376_);
v___x_7383_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7378_);
v___x_7384_ = lean_nat_add(v___x_7382_, v___x_7383_);
lean_dec(v___x_7383_);
lean_dec(v___x_7382_);
v___x_7385_ = lean_mk_empty_array_with_capacity(v___x_7384_);
lean_dec(v___x_7384_);
lean_inc(v_adjustResult_7368_);
v___x_7386_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7368_, v_a_7376_, v___x_7385_);
lean_dec(v_a_7376_);
v___x_7387_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7368_, v_a_7378_, v___x_7386_);
lean_dec(v_a_7378_);
if (v_isShared_7381_ == 0)
{
lean_ctor_set(v___x_7380_, 0, v___x_7387_);
v___x_7389_ = v___x_7380_;
goto v_reusejp_7388_;
}
else
{
lean_object* v_reuseFailAlloc_7390_; 
v_reuseFailAlloc_7390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7390_, 0, v___x_7387_);
v___x_7389_ = v_reuseFailAlloc_7390_;
goto v_reusejp_7388_;
}
v_reusejp_7388_:
{
return v___x_7389_;
}
}
}
else
{
lean_object* v_a_7392_; lean_object* v___x_7394_; uint8_t v_isShared_7395_; uint8_t v_isSharedCheck_7399_; 
lean_dec(v_a_7376_);
lean_dec(v_adjustResult_7368_);
v_a_7392_ = lean_ctor_get(v___x_7377_, 0);
v_isSharedCheck_7399_ = !lean_is_exclusive(v___x_7377_);
if (v_isSharedCheck_7399_ == 0)
{
v___x_7394_ = v___x_7377_;
v_isShared_7395_ = v_isSharedCheck_7399_;
goto v_resetjp_7393_;
}
else
{
lean_inc(v_a_7392_);
lean_dec(v___x_7377_);
v___x_7394_ = lean_box(0);
v_isShared_7395_ = v_isSharedCheck_7399_;
goto v_resetjp_7393_;
}
v_resetjp_7393_:
{
lean_object* v___x_7397_; 
if (v_isShared_7395_ == 0)
{
v___x_7397_ = v___x_7394_;
goto v_reusejp_7396_;
}
else
{
lean_object* v_reuseFailAlloc_7398_; 
v_reuseFailAlloc_7398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7398_, 0, v_a_7392_);
v___x_7397_ = v_reuseFailAlloc_7398_;
goto v_reusejp_7396_;
}
v_reusejp_7396_:
{
return v___x_7397_;
}
}
}
}
else
{
lean_object* v_a_7400_; lean_object* v___x_7402_; uint8_t v_isShared_7403_; uint8_t v_isSharedCheck_7407_; 
lean_dec_ref(v_ty_7369_);
lean_dec(v_adjustResult_7368_);
lean_dec(v_droppedEntriesRef_7367_);
lean_dec(v_constantsPerTask_7366_);
lean_dec(v_droppedKeys_7365_);
lean_dec_ref(v_addEntry_7364_);
v_a_7400_ = lean_ctor_get(v___x_7375_, 0);
v_isSharedCheck_7407_ = !lean_is_exclusive(v___x_7375_);
if (v_isSharedCheck_7407_ == 0)
{
v___x_7402_ = v___x_7375_;
v_isShared_7403_ = v_isSharedCheck_7407_;
goto v_resetjp_7401_;
}
else
{
lean_inc(v_a_7400_);
lean_dec(v___x_7375_);
v___x_7402_ = lean_box(0);
v_isShared_7403_ = v_isSharedCheck_7407_;
goto v_resetjp_7401_;
}
v_resetjp_7401_:
{
lean_object* v___x_7405_; 
if (v_isShared_7403_ == 0)
{
v___x_7405_ = v___x_7402_;
goto v_reusejp_7404_;
}
else
{
lean_object* v_reuseFailAlloc_7406_; 
v_reuseFailAlloc_7406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7406_, 0, v_a_7400_);
v___x_7405_ = v_reuseFailAlloc_7406_;
goto v_reusejp_7404_;
}
v_reusejp_7404_:
{
return v___x_7405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7408_, lean_object* v_ref_7409_, lean_object* v_addEntry_7410_, lean_object* v_droppedKeys_7411_, lean_object* v_constantsPerTask_7412_, lean_object* v_droppedEntriesRef_7413_, lean_object* v_adjustResult_7414_, lean_object* v_ty_7415_, lean_object* v_a_7416_, lean_object* v_a_7417_, lean_object* v_a_7418_, lean_object* v_a_7419_, lean_object* v_a_7420_){
_start:
{
lean_object* v_res_7421_; 
v_res_7421_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7408_, v_ref_7409_, v_addEntry_7410_, v_droppedKeys_7411_, v_constantsPerTask_7412_, v_droppedEntriesRef_7413_, v_adjustResult_7414_, v_ty_7415_, v_a_7416_, v_a_7417_, v_a_7418_, v_a_7419_);
lean_dec(v_a_7419_);
lean_dec_ref(v_a_7418_);
lean_dec(v_a_7417_);
lean_dec_ref(v_a_7416_);
lean_dec(v_ref_7409_);
return v_res_7421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7422_, lean_object* v_00_u03b2_7423_, lean_object* v_moduleTreeRef_7424_, lean_object* v_ref_7425_, lean_object* v_addEntry_7426_, lean_object* v_droppedKeys_7427_, lean_object* v_constantsPerTask_7428_, lean_object* v_droppedEntriesRef_7429_, lean_object* v_adjustResult_7430_, lean_object* v_ty_7431_, lean_object* v_a_7432_, lean_object* v_a_7433_, lean_object* v_a_7434_, lean_object* v_a_7435_){
_start:
{
lean_object* v___x_7437_; 
v___x_7437_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7424_, v_ref_7425_, v_addEntry_7426_, v_droppedKeys_7427_, v_constantsPerTask_7428_, v_droppedEntriesRef_7429_, v_adjustResult_7430_, v_ty_7431_, v_a_7432_, v_a_7433_, v_a_7434_, v_a_7435_);
return v___x_7437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7438_, lean_object* v_00_u03b2_7439_, lean_object* v_moduleTreeRef_7440_, lean_object* v_ref_7441_, lean_object* v_addEntry_7442_, lean_object* v_droppedKeys_7443_, lean_object* v_constantsPerTask_7444_, lean_object* v_droppedEntriesRef_7445_, lean_object* v_adjustResult_7446_, lean_object* v_ty_7447_, lean_object* v_a_7448_, lean_object* v_a_7449_, lean_object* v_a_7450_, lean_object* v_a_7451_, lean_object* v_a_7452_){
_start:
{
lean_object* v_res_7453_; 
v_res_7453_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7438_, v_00_u03b2_7439_, v_moduleTreeRef_7440_, v_ref_7441_, v_addEntry_7442_, v_droppedKeys_7443_, v_constantsPerTask_7444_, v_droppedEntriesRef_7445_, v_adjustResult_7446_, v_ty_7447_, v_a_7448_, v_a_7449_, v_a_7450_, v_a_7451_);
lean_dec(v_a_7451_);
lean_dec_ref(v_a_7450_);
lean_dec(v_a_7449_);
lean_dec_ref(v_a_7448_);
lean_dec(v_ref_7441_);
return v_res_7453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7454_, lean_object* v_00_u03b2_7455_, lean_object* v_adjustResult_7456_, lean_object* v_mr_7457_, lean_object* v_a_7458_){
_start:
{
lean_object* v___x_7459_; 
v___x_7459_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7456_, v_mr_7457_, v_a_7458_);
return v___x_7459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7460_, lean_object* v_00_u03b2_7461_, lean_object* v_adjustResult_7462_, lean_object* v_mr_7463_, lean_object* v_a_7464_){
_start:
{
lean_object* v_res_7465_; 
v_res_7465_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7460_, v_00_u03b2_7461_, v_adjustResult_7462_, v_mr_7463_, v_a_7464_);
lean_dec_ref(v_mr_7463_);
return v_res_7465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7466_, lean_object* v_00_u03b2_7467_, lean_object* v_adjustResult_7468_, lean_object* v_j_7469_, size_t v_sz_7470_, size_t v_i_7471_, lean_object* v_bs_7472_){
_start:
{
lean_object* v___x_7473_; 
v___x_7473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7468_, v_j_7469_, v_sz_7470_, v_i_7471_, v_bs_7472_);
return v___x_7473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7474_, lean_object* v_00_u03b2_7475_, lean_object* v_adjustResult_7476_, lean_object* v_j_7477_, lean_object* v_sz_7478_, lean_object* v_i_7479_, lean_object* v_bs_7480_){
_start:
{
size_t v_sz_boxed_7481_; size_t v_i_boxed_7482_; lean_object* v_res_7483_; 
v_sz_boxed_7481_ = lean_unbox_usize(v_sz_7478_);
lean_dec(v_sz_7478_);
v_i_boxed_7482_ = lean_unbox_usize(v_i_7479_);
lean_dec(v_i_7479_);
v_res_7483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7474_, v_00_u03b2_7475_, v_adjustResult_7476_, v_j_7477_, v_sz_boxed_7481_, v_i_boxed_7482_, v_bs_7480_);
return v_res_7483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7484_, lean_object* v_00_u03b2_7485_, lean_object* v_adjustResult_7486_, lean_object* v_j_7487_, lean_object* v_as_7488_, size_t v_i_7489_, size_t v_stop_7490_, lean_object* v_b_7491_){
_start:
{
lean_object* v___x_7492_; 
v___x_7492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7486_, v_j_7487_, v_as_7488_, v_i_7489_, v_stop_7490_, v_b_7491_);
return v___x_7492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7493_, lean_object* v_00_u03b2_7494_, lean_object* v_adjustResult_7495_, lean_object* v_j_7496_, lean_object* v_as_7497_, lean_object* v_i_7498_, lean_object* v_stop_7499_, lean_object* v_b_7500_){
_start:
{
size_t v_i_boxed_7501_; size_t v_stop_boxed_7502_; lean_object* v_res_7503_; 
v_i_boxed_7501_ = lean_unbox_usize(v_i_7498_);
lean_dec(v_i_7498_);
v_stop_boxed_7502_ = lean_unbox_usize(v_stop_7499_);
lean_dec(v_stop_7499_);
v_res_7503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7493_, v_00_u03b2_7494_, v_adjustResult_7495_, v_j_7496_, v_as_7497_, v_i_boxed_7501_, v_stop_boxed_7502_, v_b_7500_);
lean_dec_ref(v_as_7497_);
return v_res_7503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7504_, lean_object* v_n_7505_, lean_object* v_00_u03b1_7506_, lean_object* v_adjustResult_7507_, lean_object* v_aa_7508_, lean_object* v_n_7509_, lean_object* v_j_7510_, lean_object* v_a_7511_, lean_object* v_a_7512_){
_start:
{
lean_object* v___x_7513_; 
v___x_7513_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7505_, v_adjustResult_7507_, v_aa_7508_, v_n_7509_, v_j_7510_, v_a_7512_);
return v___x_7513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7514_, lean_object* v_n_7515_, lean_object* v_00_u03b1_7516_, lean_object* v_adjustResult_7517_, lean_object* v_aa_7518_, lean_object* v_n_7519_, lean_object* v_j_7520_, lean_object* v_a_7521_, lean_object* v_a_7522_){
_start:
{
lean_object* v_res_7523_; 
v_res_7523_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7514_, v_n_7515_, v_00_u03b1_7516_, v_adjustResult_7517_, v_aa_7518_, v_n_7519_, v_j_7520_, v_a_7521_, v_a_7522_);
lean_dec(v_j_7520_);
lean_dec(v_n_7519_);
lean_dec_ref(v_aa_7518_);
lean_dec(v_n_7515_);
return v_res_7523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7524_, lean_object* v_n_7525_, lean_object* v_00_u03b1_7526_, lean_object* v_aa_7527_, lean_object* v_adjustResult_7528_, lean_object* v_n_7529_, lean_object* v_j_7530_, lean_object* v_a_7531_, lean_object* v_a_7532_){
_start:
{
lean_object* v___x_7533_; 
v___x_7533_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7525_, v_aa_7527_, v_adjustResult_7528_, v_n_7529_, v_j_7530_, v_a_7532_);
return v___x_7533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7534_, lean_object* v_n_7535_, lean_object* v_00_u03b1_7536_, lean_object* v_aa_7537_, lean_object* v_adjustResult_7538_, lean_object* v_n_7539_, lean_object* v_j_7540_, lean_object* v_a_7541_, lean_object* v_a_7542_){
_start:
{
lean_object* v_res_7543_; 
v_res_7543_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7534_, v_n_7535_, v_00_u03b1_7536_, v_aa_7537_, v_adjustResult_7538_, v_n_7539_, v_j_7540_, v_a_7541_, v_a_7542_);
lean_dec(v_n_7539_);
lean_dec_ref(v_aa_7537_);
lean_dec(v_n_7535_);
return v_res_7543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7544_, lean_object* v_v_7545_){
_start:
{
lean_inc(v_v_7545_);
return v_v_7545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7546_, lean_object* v_v_7547_){
_start:
{
lean_object* v_res_7548_; 
v_res_7548_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7546_, v_v_7547_);
lean_dec(v_v_7547_);
lean_dec(v_x_7546_);
return v_res_7548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ref_7550_, lean_object* v_addEntry_7551_, lean_object* v_droppedKeys_7552_, lean_object* v_constantsPerTask_7553_, lean_object* v_droppedEntriesRef_7554_, lean_object* v_ty_7555_, lean_object* v_a_7556_, lean_object* v_a_7557_, lean_object* v_a_7558_, lean_object* v_a_7559_){
_start:
{
lean_object* v___x_7561_; 
lean_inc(v_droppedEntriesRef_7554_);
lean_inc(v_droppedKeys_7552_);
lean_inc_ref(v_addEntry_7551_);
v___x_7561_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7551_, v_droppedKeys_7552_, v_droppedEntriesRef_7554_, v_a_7556_, v_a_7557_, v_a_7558_, v_a_7559_);
if (lean_obj_tag(v___x_7561_) == 0)
{
lean_object* v_a_7562_; lean_object* v___f_7563_; lean_object* v___x_7564_; 
v_a_7562_ = lean_ctor_get(v___x_7561_, 0);
lean_inc(v_a_7562_);
lean_dec_ref_known(v___x_7561_, 1);
v___f_7563_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7564_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7562_, v_ref_7550_, v_addEntry_7551_, v_droppedKeys_7552_, v_constantsPerTask_7553_, v_droppedEntriesRef_7554_, v___f_7563_, v_ty_7555_, v_a_7556_, v_a_7557_, v_a_7558_, v_a_7559_);
return v___x_7564_;
}
else
{
lean_object* v_a_7565_; lean_object* v___x_7567_; uint8_t v_isShared_7568_; uint8_t v_isSharedCheck_7572_; 
lean_dec_ref(v_ty_7555_);
lean_dec(v_droppedEntriesRef_7554_);
lean_dec(v_constantsPerTask_7553_);
lean_dec(v_droppedKeys_7552_);
lean_dec_ref(v_addEntry_7551_);
v_a_7565_ = lean_ctor_get(v___x_7561_, 0);
v_isSharedCheck_7572_ = !lean_is_exclusive(v___x_7561_);
if (v_isSharedCheck_7572_ == 0)
{
v___x_7567_ = v___x_7561_;
v_isShared_7568_ = v_isSharedCheck_7572_;
goto v_resetjp_7566_;
}
else
{
lean_inc(v_a_7565_);
lean_dec(v___x_7561_);
v___x_7567_ = lean_box(0);
v_isShared_7568_ = v_isSharedCheck_7572_;
goto v_resetjp_7566_;
}
v_resetjp_7566_:
{
lean_object* v___x_7570_; 
if (v_isShared_7568_ == 0)
{
v___x_7570_ = v___x_7567_;
goto v_reusejp_7569_;
}
else
{
lean_object* v_reuseFailAlloc_7571_; 
v_reuseFailAlloc_7571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7571_, 0, v_a_7565_);
v___x_7570_ = v_reuseFailAlloc_7571_;
goto v_reusejp_7569_;
}
v_reusejp_7569_:
{
return v___x_7570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ref_7573_, lean_object* v_addEntry_7574_, lean_object* v_droppedKeys_7575_, lean_object* v_constantsPerTask_7576_, lean_object* v_droppedEntriesRef_7577_, lean_object* v_ty_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_, lean_object* v_a_7581_, lean_object* v_a_7582_, lean_object* v_a_7583_){
_start:
{
lean_object* v_res_7584_; 
v_res_7584_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7573_, v_addEntry_7574_, v_droppedKeys_7575_, v_constantsPerTask_7576_, v_droppedEntriesRef_7577_, v_ty_7578_, v_a_7579_, v_a_7580_, v_a_7581_, v_a_7582_);
lean_dec(v_a_7582_);
lean_dec_ref(v_a_7581_);
lean_dec(v_a_7580_);
lean_dec_ref(v_a_7579_);
lean_dec(v_ref_7573_);
return v_res_7584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7585_, lean_object* v_ref_7586_, lean_object* v_addEntry_7587_, lean_object* v_droppedKeys_7588_, lean_object* v_constantsPerTask_7589_, lean_object* v_droppedEntriesRef_7590_, lean_object* v_ty_7591_, lean_object* v_a_7592_, lean_object* v_a_7593_, lean_object* v_a_7594_, lean_object* v_a_7595_){
_start:
{
lean_object* v___x_7597_; 
v___x_7597_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ref_7586_, v_addEntry_7587_, v_droppedKeys_7588_, v_constantsPerTask_7589_, v_droppedEntriesRef_7590_, v_ty_7591_, v_a_7592_, v_a_7593_, v_a_7594_, v_a_7595_);
return v___x_7597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7598_, lean_object* v_ref_7599_, lean_object* v_addEntry_7600_, lean_object* v_droppedKeys_7601_, lean_object* v_constantsPerTask_7602_, lean_object* v_droppedEntriesRef_7603_, lean_object* v_ty_7604_, lean_object* v_a_7605_, lean_object* v_a_7606_, lean_object* v_a_7607_, lean_object* v_a_7608_, lean_object* v_a_7609_){
_start:
{
lean_object* v_res_7610_; 
v_res_7610_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7598_, v_ref_7599_, v_addEntry_7600_, v_droppedKeys_7601_, v_constantsPerTask_7602_, v_droppedEntriesRef_7603_, v_ty_7604_, v_a_7605_, v_a_7606_, v_a_7607_, v_a_7608_);
lean_dec(v_a_7608_);
lean_dec_ref(v_a_7607_);
lean_dec(v_a_7606_);
lean_dec_ref(v_a_7605_);
lean_dec(v_ref_7599_);
return v_res_7610_;
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
